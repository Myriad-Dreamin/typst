mod breakpoint;

use std::{
    borrow::Cow,
    io::{Read, Write},
    sync::Mutex,
};

use dap::{
    events::Event, requests::Command, responses::ResponseBody, server::Server, types,
};
use typst::syntax::{
    ast::{AstNode, Closure, DestructAssignment, Expr, FuncCall, Ident, Pattern},
    Source, SyntaxKind, SyntaxNode,
};
use typst_library::prelude::*;

pub use self::breakpoint::*;

#[repr(u32)]
enum BreakpointKind {
    Function = 1 << 0,
    FunctionEnd = 1 << 1,
    LetBinding = 1 << 2,
    Assignment = 1 << 3,
    CallEnd = 1 << 4,
}

pub struct DebuggerHost<R: Read, W: Write> {
    server: Mutex<Server<R, W>>,
    logger: Mutex<std::fs::File>,
}

impl<R: Read, W: Write> DebuggerHost<R, W> {
    pub fn new(server: Server<R, W>) -> Self {
        Self {
            server: Mutex::new(server),
            logger: Mutex::new(std::fs::File::create("debug.log").unwrap()),
        }
    }

    pub fn wait_init(&self) -> StrResult<()> {
        let mut server = self.server.lock().unwrap();

        let req = match server.poll_request().map_err(|e| eco_format!("{e}"))? {
            Some(req) => req,
            None => return Err(eco_format!("invalid command")),
        };
        if let Command::Initialize(_) = req.command {
            let rsp = req.success(ResponseBody::Initialize(types::Capabilities {
                ..Default::default()
            }));

            // When you call respond, send_event etc. the message will be wrapped
            // in a base message with a appropriate seq number, so you don't have to keep track of that yourself
            server.respond(rsp).map_err(|e| eco_format!("{e}"))?;

            server
                .send_event(Event::Initialized)
                .map_err(|e| eco_format!("{e}"))?;
        } else {
            return Err("unhandled command".into());
        }
        Ok(())
    }

    pub fn send_terminated(&self) -> StrResult<()> {
        let mut server = self.server.lock().unwrap();
        server
            .send_event(Event::Terminated(None))
            .map_err(|e| eco_format!("{e}"))?;
        Ok(())
    }

    pub fn handle(&self, vm: &mut Vm, mut args: Array) {
        let mut server = self.server.lock().unwrap();

        let req = loop {
            match server.poll_request() {
                Ok(Some(req)) => break req,
                Ok(None) => continue,
                Err(err) => {
                    writeln!(
                        self.logger.lock().unwrap(),
                        "poll request error: {:?}",
                        err
                    )
                    .unwrap();
                    return;
                }
            }
        };

        writeln!(self.logger.lock().unwrap(), "req: {:?}", req).unwrap();

        let Ok(Value::Args(args)) = args.at_mut(0) else {
            unreachable!("debugger host must be called with args")
        };

        writeln!(
            self.logger.lock().unwrap(),
            "handle: {:?} {:?} at depth {:?}",
            args.named::<Value>("kind").ok(),
            args.named::<Value>("loc").ok(),
            vm.scopes().scopes.len(),
        )
        .unwrap();
    }
}

#[allow(dead_code)]
pub struct BreakpointDesc {
    kind: u32,
    loc: Option<(usize, usize)>,
}

struct InstrumentVisitor<'a> {
    breakpoints: Vec<BreakpointDesc>,
    source: &'a Source,
    tokens: Vec<&'a SyntaxNode>,
}

struct LineColumn(Option<(usize, usize)>);

impl fmt::Display for LineColumn {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Some((l, c)) => write!(f, "({}, {})", l, c),
            None => write!(f, "none"),
        }
    }
}

impl<'a> InstrumentVisitor<'a> {
    fn new(source: &'a Source) -> Self {
        Self {
            breakpoints: Default::default(),
            source,
            tokens: Default::default(),
        }
    }

    fn visit(&mut self, node: &'a SyntaxNode) {
        self.tokens.push(node);

        for ch in node.children() {
            self.visit(ch);
        }
    }

    fn find_loc(&self, node: &'a SyntaxNode, pre: bool) -> LineColumn {
        LineColumn(
            self.source
                .range(node.span())
                .and_then(|rng| {
                    let sub_loc = if pre { rng.start } else { rng.end };
                    let l = self.source.byte_to_line(sub_loc)?;
                    let c = self.source.byte_to_column(sub_loc)?;
                    Some((l, c))
                })
                .or_else(|| {
                    if node.is_empty() {
                        return None;
                    }
                    if pre {
                        node.children().find_map(|ch| self.find_loc(ch, pre).0)
                    } else {
                        node.children().rev().find_map(|ch| self.find_loc(ch, pre).0)
                    }
                }),
        )
    }

    fn instrument_children_with(
        &mut self,
        node: &SyntaxNode,
        kind_set: u32,
        filter: impl Fn(&SyntaxNode) -> bool,
        instrumenter: impl Fn(&mut Self, &mut SyntaxNode, u32),
    ) -> SyntaxNode {
        let mut children = node.children().cloned().collect::<Vec<_>>();
        for (ch, sel) in children.iter_mut().zip(node.children()) {
            if !filter(sel) {
                continue;
            }

            instrumenter(self, ch, kind_set);
        }
        SyntaxNode::inner(node.kind(), children)
    }

    fn instrument_children(
        &mut self,
        node: &SyntaxNode,
        kind_set: u32,
        filter: impl Fn(&SyntaxNode) -> bool,
    ) -> SyntaxNode {
        self.instrument_children_with(node, kind_set, filter, Self::instrument)
    }

    fn instrument_expr(&mut self, node: &mut SyntaxNode, mut kind: u32) {
        let post_loc = self.find_loc(node, false);
        if post_loc.0.is_none() {
            // println!("no loc: {:?}", node);
        }
        let pre = if (kind & (BreakpointKind::Function as u32)) != 0 {
            let pre_loc = self.find_loc(node, true);
            let pre = format!(r#"{{ breakpoint(kind: {kind}, loc: {pre_loc}); "#);
            self.breakpoints.push(BreakpointDesc { kind, loc: pre_loc.0 });

            kind &= !(BreakpointKind::Function as u32);
            kind |= BreakpointKind::FunctionEnd as u32;

            pre
        } else {
            "{ ".to_owned()
        };
        let post = format!(r#"; breakpoint(kind: {kind}, loc: {post_loc}) }}"#);
        self.breakpoints.push(BreakpointDesc { kind, loc: post_loc.0 });
        let lb = SyntaxNode::leaf(SyntaxKind::LeftBrace, pre);
        let rb = SyntaxNode::leaf(SyntaxKind::RightBrace, post);
        let wrapped =
            SyntaxNode::inner(SyntaxKind::CodeBlock, vec![lb, node.clone(), rb]);
        *node = wrapped;
    }

    fn instrument(&mut self, node: &mut SyntaxNode, kind_set: u32) {
        if node.erroneous() || node.kind().is_trivia() || node.kind().is_keyword() {
            return;
        }

        match node.kind() {
            SyntaxKind::Closure => {
                // println!("check closure: {:?}", node);
                let closure = node.cast::<Closure>().unwrap();
                let body = closure.body().to_untyped();
                *node = self.instrument_children(
                    node,
                    BreakpointKind::Function as u32,
                    |ch| ch == body,
                );
            }
            SyntaxKind::LetBinding => {
                // println!("let bind: {:?}", node);
                *node = match node.cast_first_match::<Pattern>() {
                    Some(Pattern::Normal(Expr::Closure(closure))) => {
                        // instrument a closure description
                        // let x(...) = { ... }
                        //     ^^^^^^^^^^^^^^^^
                        let closure = closure.to_untyped();
                        self.instrument_children(node, 0, |ch| ch == closure)
                    }
                    _ => {
                        // instrument a let binding
                        // let x = ...
                        //         ^^^
                        let rhs = node
                            .cast_last_match::<Expr>()
                            .unwrap()
                            .to_owned()
                            .to_untyped();
                        self.instrument_children(
                            node,
                            BreakpointKind::LetBinding as u32,
                            |ch| ch == rhs,
                        )
                    }
                };

                return;
            }
            SyntaxKind::FuncCall => {
                let t = node
                    .cast::<FuncCall>()
                    .unwrap()
                    .callee()
                    .to_untyped()
                    .cast::<Ident>();
                if let Some(t) = t {
                    if t.as_str() == "breakpoint" {
                        return;
                    }
                }
                self.instrument_expr(node, kind_set | (BreakpointKind::CallEnd as u32));
                return;
            }
            SyntaxKind::DestructAssignment => {
                let value =
                    node.cast::<DestructAssignment>().unwrap().value().to_untyped();
                self.instrument_children(
                    node,
                    BreakpointKind::Assignment as u32,
                    |ch: &SyntaxNode| ch == value,
                );
            }
            SyntaxKind::Let => {
                // println!("let: {:?}", node);
                return;
            }
            _ => {}
        }

        if node.children().len() > 0 {
            let mut children = node.children().cloned().collect::<Vec<_>>();
            for ch in children.iter_mut() {
                self.instrument(ch, 0);
            }
            *node = SyntaxNode::inner(node.kind(), children);
        }

        if (kind_set
            & ((BreakpointKind::Function as u32)
                | (BreakpointKind::LetBinding as u32)
                | (BreakpointKind::Assignment as u32)))
            != 0
        {
            self.instrument_expr(node, kind_set);
        }
    }
}

pub fn instrument_breakpoints(
    id: FileId,
    source: &str,
) -> (Option<Vec<BreakpointDesc>>, Cow<'_, str>) {
    if id.package().is_some() {
        return (None, Cow::Borrowed(source));
    }
    if id.vpath().as_rootless_path().to_string_lossy().contains("debug.typ") {
        return (None, Cow::Borrowed(source)); // todo
    }

    let ast = Source::new(id, source.to_owned());

    let mut visitor = InstrumentVisitor::new(&ast);
    visitor.visit(ast.root());

    // for token in visitor.tokens.iter() {
    //     println!("{:?}", token);
    // }

    // println!("ast: {:#?}", ast.root());
    let mut t = ast.root().clone();
    visitor.instrument(&mut t, 0);

    let instrumented = r#"#import "debug.typ": breakpoint
"#
    .to_owned()
        + t.into_text().as_ref();
    // println!("text: {}", instrumented);

    return (Some(visitor.breakpoints), Cow::Owned(instrumented));
}

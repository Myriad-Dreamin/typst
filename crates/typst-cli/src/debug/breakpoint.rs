use std::collections::HashMap;
use std::sync::RwLock;

use once_cell::sync::Lazy;
use typst::eval::Tracer;

use typst_library::prelude::*;

use typst_library::meta::Effect;

pub type BreakpointHandler = Box<dyn Fn(&mut Vm, Array, i64) + Send + Sync>;

/// The global software breakpoint id
pub(crate) static SOFTWARE_BREAKPOINT: Lazy<Effect> =
    Lazy::new(|| Effect::register("breakpoint".into(), Box::new(breakpoint_raw)));

/// The global software breakpoint id
pub(crate) static BREAKPOINT_TOKEN: Lazy<RwLock<HashMap<i64, BreakpointHandler>>> =
    Lazy::new(|| RwLock::new(Default::default()));

#[derive(Debug, PartialEq, Eq)]
pub struct BreakpointToken(i64);

impl BreakpointToken {
    pub fn new(handler: BreakpointHandler) -> Self {
        let mut token = BREAKPOINT_TOKEN.write().unwrap();
        let id = token.keys().max().cloned().unwrap_or_default() + 1;
        token.insert(id, handler);

        Self(id)
    }
}

impl Drop for BreakpointToken {
    fn drop(&mut self) {
        let mut token = BREAKPOINT_TOKEN.write().unwrap();
        token.remove(&self.0);
    }
}

/// Raw implementation of breakpoint effect.
/// It update the breakpoint entries in the tracer.
///
/// If the entries is not exist, it will not do anything.
#[func]
pub(crate) fn breakpoint_raw(
    /// The virtual machine.
    vm: &mut Vm,
    /// The arguments of breakpoint.
    arguments: Array,
) -> Value {
    // get breakpoint entries
    let tok = vm.vt.tracer.get_effect(SOFTWARE_BREAKPOINT.id());
    let Some(tok) = tok.map(|e| {
        let Value::Int(tok) = e.clone() else {
            unreachable!("breakpoint effect must be an integer")
        };
        tok
    }) else {
        return Value::None;
    };

    let handler = BREAKPOINT_TOKEN.read().unwrap();
    let Some(handler) = handler.get(&tok) else {
        return Value::None;
    };

    handler(vm, arguments, tok);

    Value::None
}

/// Effect point
#[func]
pub fn breakpoint(
    /// The virtual machine.
    vm: &mut Vm,
    /// The arguments for effect handler.
    arguments: Array,
) -> Value {
    breakpoint_raw(vm, arguments)
}

pub fn enable_breakpoint(tracer: &mut Tracer, token: &BreakpointToken) {
    tracer.set_effect(SOFTWARE_BREAKPOINT.id(), Value::Int(token.0));
}

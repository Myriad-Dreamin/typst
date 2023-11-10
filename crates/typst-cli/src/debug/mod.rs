mod breakpoint;

use typst_library::prelude::*;

pub use self::breakpoint::*;

#[derive(Debug, Default, PartialEq, Eq)]
pub struct DebuggerHost(());

impl DebuggerHost {
    pub fn handle(&self, vm: &mut Vm, args: Array) {
        println!("handle: {:?} at {:?}", args, vm.scopes());
    }
}

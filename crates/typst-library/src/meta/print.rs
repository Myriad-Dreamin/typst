use once_cell::sync::Lazy;
use typst::eval::Tracer;

use crate::prelude::*;

use super::Effect;

/// The global print effect id
pub(crate) static PRINT_EFFECT: Lazy<Effect> =
    Lazy::new(|| Effect::register("print".into(), Box::new(print_raw)));

/// Raw implementation of print effect.
/// It update the print entries in the tracer.
///
/// If the entries is not exist, it will not do anything.
#[func]
pub(crate) fn print_raw(
    /// The virtual machine.
    vm: &mut Vm,
    /// The arguments of print.
    arguments: Array,
) -> Value {
    // get print entries
    let entries = vm.vt.tracer.get_effect(PRINT_EFFECT.id());
    let Some(mut entries) = entries.map(|e| {
        let Value::Array(entries) = e.clone() else {
            unreachable!("print effect must be an array")
        };
        entries
    }) else {
        return Value::None;
    };

    // add new entry
    entries.push(Value::Array(arguments));
    vm.vt.tracer.set_effect(PRINT_EFFECT.id(), Value::Array(entries));

    Value::None
}

/// Effect point
#[func]
pub fn print(
    /// The virtual machine.
    vm: &mut Vm,
    /// The arguments for effect handler.
    arguments: Array,
    /// Can be an arbitrary location, as its value is irrelevant for the
    /// function's return value. Why is it required then? As noted before, Typst
    /// has to evaluate parts of your code multiple times to determine the
    /// values of all state. By only allowing this function within
    /// [`locate`]($locate) calls, the amount of code that can depend on the
    /// query's result is reduced. If you could call it directly at the top
    /// level of a module, the evaluation of the whole module and its exports
    /// could depend on the query's result.
    location: Location,
) -> Value {
    let _ = location;

    print_raw(vm, arguments)
}

pub fn enable_print(tracer: &mut Tracer) {
    tracer.set_effect(PRINT_EFFECT.id(), Value::Array(Default::default()));
}

pub fn get_prints(tracer: &Tracer) -> Option<Array> {
    let entries = tracer.get_effect(PRINT_EFFECT.id());
    entries.map(|e| {
        let Value::Array(entries) = e.clone() else {
            unreachable!("print effect must be an array")
        };
        entries
    })
}

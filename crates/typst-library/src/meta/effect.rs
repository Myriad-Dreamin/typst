use std::{collections::HashMap, sync::RwLock};

use once_cell::sync::Lazy;

use crate::prelude::*;

/// The global effect interner.
static INTERNER: Lazy<RwLock<Interner>> =
    Lazy::new(|| RwLock::new(Interner { to_id: HashMap::new(), from_id: Vec::new() }));

/// A effect interner.
struct Interner {
    to_id: HashMap<Str, Effect>,
    from_id: Vec<(Str, EffectHandler)>,
}

pub type EffectHandler = Box<dyn Fn(&mut Vm, Array) -> Value + Send + Sync>;

#[derive(Debug, Clone, Copy)]
pub struct Effect(u16);

impl Effect {
    pub fn register(key: Str, handler: EffectHandler) -> Self {
        if let Some(&id) = INTERNER.read().unwrap().to_id.get(&key) {
            return id;
        }

        let mut interner = INTERNER.write().unwrap();
        let num = interner.from_id.len().try_into().expect("out of file ids");

        // Create a new entry forever by leaking the key. We can't leak more
        // than 2^16 key (and typically will leak a lot less), so its not a
        // big deal.
        let id = Effect(num);
        interner.to_id.insert(key.clone(), id);
        interner.from_id.push((key, handler));
        id
    }

    pub fn id(self) -> u16 {
        self.0
    }
}

/// Trap vm by some effect.
#[func]
pub fn handle_effect(
    /// The virtual machine.
    vm: &mut Vm,
    /// The key that identifies this effect.
    key: Str,
    /// The arguments for effect handler.
    arguments: Array,
) -> Value {
    let Some(eff_id) = INTERNER.read().unwrap().to_id.get(&key).cloned() else {
        return Value::None;
    };

    let handler = &INTERNER.read().unwrap().from_id[eff_id.0 as usize].1;
    handler(vm, arguments)
}

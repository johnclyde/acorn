use std::collections::HashMap;

use crate::atom::{Atom, AtomId};
use crate::constant_name::GlobalConstantName;
use crate::module::{ModuleId, SKOLEM};

// The ConstantKey identifies a constant in the Acorn language.
#[derive(Hash, Debug, Eq, PartialEq, Clone)]
pub struct ConstantKey {
    pub module: ModuleId,
    pub name: String,
}

impl ConstantKey {
    pub fn from_name(name: GlobalConstantName) -> ConstantKey {
        ConstantKey {
            module: name.module_id,
            name: name.local_name.to_string(),
        }
    }
}

// In the Acorn language a constant is uniquely identified by its module id and name.
// The low-level prover, on the other hand, just wants each constant to have a
// numerical id.
// The ConstantMap is a mapping between the two.
#[derive(Clone)]
pub struct ConstantMap {
    // For global constant i in the prover, global_constants[i] is the corresponding ConstantKey.
    // The AtomId -> ConstantKey lookup direction.
    global_constants: Vec<Option<ConstantKey>>,

    // For local constant i in the prover, local_constants[i] is the corresponding ConstantKey.
    // The AtomId -> ConstantKey lookup direction.
    local_constants: Vec<Option<ConstantKey>>,

    // Inverse map of constants.
    // The ConstantKey -> AtomId lookup direction.
    // Multiple ConstantKey can map to the same AtomId, when two constants alias to the same thing.
    keymap: HashMap<ConstantKey, Atom>,
}

impl ConstantMap {
    pub fn new() -> ConstantMap {
        ConstantMap {
            global_constants: vec![],
            local_constants: vec![],
            keymap: HashMap::new(),
        }
    }

    // Assigns an id to this (module, name) pair if it doesn't already have one.
    // local determines whether the constant will be represented as a local or global atom.
    pub fn add_constant(&mut self, name: GlobalConstantName, local: bool) -> Atom {
        if name.module_id == SKOLEM {
            panic!("skolem constants should not be stored in the ConstantMap");
        }
        let key = ConstantKey::from_name(name);
        if let Some(&atom) = self.keymap.get(&key) {
            return atom;
        }
        let atom = if local {
            let atom_id = self.local_constants.len() as AtomId;
            self.local_constants.push(Some(key.clone()));
            Atom::LocalConstant(atom_id)
        } else {
            let atom_id = self.global_constants.len() as AtomId;
            self.global_constants.push(Some(key.clone()));
            Atom::GlobalConstant(atom_id)
        };
        self.keymap.insert(key, atom);
        atom
    }

    // This function is called when two constants are equal.
    // We can add an alias if we have never seen one of them before.
    // Returns true if we added an alias.
    pub fn maybe_add_alias(
        &mut self,
        new_name: &GlobalConstantName,
        old_name: &GlobalConstantName,
    ) -> bool {
        let new_key = ConstantKey::from_name(new_name.clone());
        if self.keymap.contains_key(&new_key) {
            return false;
        }
        let old_key = ConstantKey::from_name(old_name.clone());
        if !self.keymap.contains_key(&old_key) {
            return false;
        }
        let atom = self.keymap[&old_key];
        self.keymap.insert(new_key, atom);
        true
    }

    // Get information about a global constant.
    pub fn get_global_info(&self, atom_id: AtomId) -> (ModuleId, String) {
        let key = &self.global_constants[atom_id as usize].as_ref().unwrap();
        (key.module, key.name.to_string())
    }

    // Get information about a local constant.
    pub fn get_local_info(&self, atom_id: AtomId) -> (ModuleId, String) {
        let key = &self.local_constants[atom_id as usize].as_ref().unwrap();
        (key.module, key.name.to_string())
    }
}

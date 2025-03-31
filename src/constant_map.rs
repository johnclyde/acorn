use std::collections::HashMap;

use crate::atom::{Atom, AtomId};
use crate::constant_name::GlobalConstantName;
use crate::module::SKOLEM;

// In the Acorn language a constant is uniquely identified by the GlobalConstantName.
// The low-level prover, on the other hand, just wants each constant to have a
// numerical id.
// The ConstantMap is a mapping between the two.
#[derive(Clone)]
pub struct ConstantMap {
    // For global constant i in the prover, global_constants[i] is the corresponding GlobalConstantName.
    // The AtomId -> GlobalConstantName lookup direction.
    global_constants: Vec<Option<GlobalConstantName>>,

    // For local constant i in the prover, local_constants[i] is the corresponding GlobalConstantName.
    // The AtomId -> GlobalConstantName lookup direction.
    local_constants: Vec<Option<GlobalConstantName>>,

    // Inverse map of constants.
    // The GlobalConstantName -> AtomId lookup direction.
    // Multiple GlobalConstantName can map to the same AtomId, when two constants alias to the same thing.
    name_to_id: HashMap<GlobalConstantName, Atom>,
}

impl ConstantMap {
    pub fn new() -> ConstantMap {
        ConstantMap {
            global_constants: vec![],
            local_constants: vec![],
            name_to_id: HashMap::new(),
        }
    }

    // Assigns an id to this (module, name) pair if it doesn't already have one.
    // local determines whether the constant will be represented as a local or global atom.
    pub fn add_constant(&mut self, name: GlobalConstantName, local: bool) -> Atom {
        if name.module_id == SKOLEM {
            panic!("skolem constants should not be stored in the ConstantMap");
        }
        if let Some(&atom) = self.name_to_id.get(&name) {
            return atom;
        }
        let atom = if local {
            let atom_id = self.local_constants.len() as AtomId;
            self.local_constants.push(Some(name.clone()));
            Atom::LocalConstant(atom_id)
        } else {
            let atom_id = self.global_constants.len() as AtomId;
            self.global_constants.push(Some(name.clone()));
            Atom::GlobalConstant(atom_id)
        };
        self.name_to_id.insert(name, atom);
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
        if self.name_to_id.contains_key(&new_name) {
            return false;
        }
        if !self.name_to_id.contains_key(&old_name) {
            return false;
        }
        let atom = self.name_to_id[&old_name];
        self.name_to_id.insert(new_name.clone(), atom);
        true
    }

    // Get information about a global constant.
    pub fn get_global_info(&self, atom_id: AtomId) -> &GlobalConstantName {
        &self.global_constants[atom_id as usize].as_ref().unwrap()
    }

    // Get information about a local constant.
    pub fn get_local_info(&self, atom_id: AtomId) -> &GlobalConstantName {
        &self.local_constants[atom_id as usize].as_ref().unwrap()
    }
}

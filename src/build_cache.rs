use std::sync::Arc;

use dashmap::DashMap;

use crate::module::{ModuleDescriptor, ModuleHash};

// The build cache stores the verified goals for modules that had no warnings or errors in them.
// They might still be dependent on other modules with warnings.
// They can't be dependent on modules with errors, because the prover won't run at all with errors.
#[derive(Clone)]
pub struct BuildCache {
    modules: Arc<DashMap<ModuleDescriptor, ModuleHash>>,
}

impl BuildCache {
    pub fn new() -> Self {
        BuildCache {
            modules: Arc::new(DashMap::new()),
        }
    }

    pub fn insert(&mut self, module_id: ModuleDescriptor, hash: ModuleHash) {
        self.modules.insert(module_id, hash);
    }

    pub fn get(&self, descriptor: &ModuleDescriptor) -> Option<ModuleHash> {
        self.modules
            .get(descriptor)
            .map(|entry| entry.value().clone())
    }

    #[cfg(test)]
    pub fn num_modules(&self) -> usize {
        self.modules.len()
    }
}

use std::sync::Arc;

use dashmap::DashMap;

use crate::module::ModuleRef;

// Information stored about a single module in the cache.
struct BuildCacheEntry {
    hash: u64,
    verified: Vec<(u32, u32)>,
}

// The build cache stores the verified goals for modules that had no warnings or errors in them.
// They might still be dependent on other modules with warnings.
// They can't be dependent on modules with errors, because the prover won't run at all with errors.
#[derive(Clone)]
pub struct BuildCache {
    modules: Arc<DashMap<ModuleRef, BuildCacheEntry>>,
}

impl BuildCache {
    pub fn new() -> Self {
        BuildCache {
            modules: Arc::new(DashMap::new()),
        }
    }

    pub fn insert(&self, module_id: ModuleRef, hash: u64, verified: Vec<(u32, u32)>) {
        self.modules
            .insert(module_id, BuildCacheEntry { hash, verified });
    }

    pub fn get(&self, module_id: &ModuleRef, hash: u64) -> Option<Vec<(u32, u32)>> {
        self.modules.get(module_id).and_then(|entry| {
            if entry.hash == hash {
                Some(entry.verified.clone())
            } else {
                None
            }
        })
    }

    #[cfg(test)]
    pub fn num_modules(&self) -> usize {
        self.modules.len()
    }
}

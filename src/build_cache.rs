use std::collections::HashMap;

use crate::module::ModuleRef;

// Information stored about a single module in the cache.
#[derive(Clone)]
struct BuildCacheEntry {
    hash: u64,
    verified: Vec<(u32, u32)>,
}

// Information stored from a single build.
#[derive(Clone)]
pub struct BuildCache {
    // When every goal in a module is verified in a build, we cache information for it.
    // We only keep "good" modules in the cache.
    modules: HashMap<ModuleRef, BuildCacheEntry>,
}

impl BuildCache {
    pub fn new() -> Self {
        BuildCache {
            modules: HashMap::new(),
        }
    }

    pub fn add(&mut self, module_id: ModuleRef, hash: u64, verified: Vec<(u32, u32)>) {
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

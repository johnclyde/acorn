use std::sync::Arc;

use dashmap::DashMap;

use crate::module::{ModuleDescriptor, ModuleHash};

// The BuildCache contains a hash for each module from the last time it was cleanly built.
// This enables skipping verification for modules that haven't changed.
#[derive(Clone)]
pub struct BuildCache {
    // The internal map from module descriptor to module hash
    inner: Arc<DashMap<ModuleDescriptor, ModuleHash>>,
}

impl BuildCache {
    // Creates a new empty build cache
    pub fn new() -> BuildCache {
        BuildCache {
            inner: Arc::new(DashMap::new()),
        }
    }

    // Gets the cached hash for a module descriptor
    pub fn get(&self, descriptor: &ModuleDescriptor) -> Option<ModuleHash> {
        self.inner
            .get(descriptor)
            .map(|entry| entry.value().clone())
    }

    // Inserts a hash for a module descriptor
    pub fn insert(&self, descriptor: ModuleDescriptor, hash: ModuleHash) {
        self.inner.insert(descriptor, hash);
    }

    // Returns the number of entries in the cache
    pub fn len(&self) -> usize {
        self.inner.len()
    }
}

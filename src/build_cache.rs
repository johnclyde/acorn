use std::path::PathBuf;
use std::sync::Arc;

use dashmap::DashMap;

use crate::module::ModuleDescriptor;
use crate::module_cache::ModuleCache;

// The BuildCache contains a hash for each module from the last time it was cleanly built.
// This enables skipping verification for modules that haven't changed.
// We read once at startup, and write whole files at a time when needed.
// Hopefully that makes it okay to not lock it. But we might need to be better about this.
#[derive(Clone)]
pub struct BuildCache {
    // The internal map from module descriptor to module hash
    inner: Arc<DashMap<ModuleDescriptor, ModuleCache>>,

    // A directory to persist the cache in.
    directory: Option<PathBuf>,

    // Whether it's okay to write to the cache directory.
    // If false, the cache will not be saved to disk.
    writable: bool,
}

impl BuildCache {
    // Creates a new empty build cache
    pub fn new(directory: Option<PathBuf>, writable: bool) -> BuildCache {
        BuildCache {
            inner: Arc::new(DashMap::new()),
            directory,
            writable,
        }
    }

    // Gets the cached hash for a module descriptor
    pub fn get(&self, descriptor: &ModuleDescriptor) -> Option<ModuleCache> {
        self.inner
            .get(descriptor)
            .map(|entry| entry.value().clone())
    }

    // Inserts a hash for a module descriptor
    pub fn insert(&self, descriptor: ModuleDescriptor, hash: ModuleCache) {
        self.inner.insert(descriptor, hash);
    }

    // Returns the number of entries in the cache
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    // Saves the build cache to its directory, if possible.
    pub fn save(&self) {
        if !self.writable {
            return;
        }
        let directory = match &self.directory {
            Some(directory) => directory,
            None => return,
        };

        todo!("save build cache to {:?}", directory);
    }
}

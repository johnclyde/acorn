use std::sync::Arc;

use dashmap::DashMap;

use crate::module::{ModuleDescriptor, ModuleHash};

// The BuildCache contains a hash for each module from the last time it was cleanly built.
// This enables skipping verification for modules that haven't changed.
#[derive(Clone)]
pub struct BuildCache {
    // The internal map from module descriptor to module hash
    pub inner: Arc<DashMap<ModuleDescriptor, ModuleHash>>,
}

impl BuildCache {
    // Creates a new empty build cache
    pub fn new() -> BuildCache {
        BuildCache {
            inner: Arc::new(DashMap::new()),
        }
    }
}

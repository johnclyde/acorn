use std::hash::{Hash, Hasher};
use serde::{Deserialize, Serialize};
use fxhash::FxHasher;

use crate::module::Module;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModuleCache {
    // There is one prefix hash per line in the file.
    // Each one hashes that line and all the lines before it.
    prefixes: Vec<u64>,

    // This single hash represents all dependencies.
    dependencies: u64,
}

impl ModuleCache {
    pub fn new(prefixes: u64, dependencies: u64) -> ModuleCache {
        ModuleCache {
            prefixes: vec![prefixes],
            dependencies,
        }
    }

    pub fn matches_through_line(&self, other: &Option<ModuleCache>, line: u32) -> bool {
        let line = line as usize;
        match other {
            Some(other) => {
                self.dependencies == other.dependencies
                    && line < self.prefixes.len()
                    && self.prefixes.get(line) == other.prefixes.get(line)
            }
            None => false,
        }
    }
}

pub struct ModuleHasher {
    // Will become part of the ModuleCache
    prefix_hashes: Vec<u64>,

    // For hashing the dependencies of the module
    dependency_hasher: FxHasher,
}

impl ModuleHasher {
    pub fn new(text: &str) -> ModuleHasher {
        let mut line_hasher = FxHasher::default();
        let mut prefix_hashes = vec![];
        for line in text.lines() {
            line.hash(&mut line_hasher);
            prefix_hashes.push(line_hasher.finish());
        }

        ModuleHasher {
            prefix_hashes,
            dependency_hasher: FxHasher::default(),
        }
    }

    // Should be called in an order that's consistent across different hashes of the same module
    pub fn add_dependency(&mut self, module: &Module) {
        if let Some(h) = &module.hash {
            if let Some(last_prefix_hash) = h.prefixes.last() {
                last_prefix_hash.hash(&mut self.dependency_hasher);
            }
            h.dependencies.hash(&mut self.dependency_hasher);
        }
    }

    pub fn finish(self) -> ModuleCache {
        ModuleCache {
            prefixes: self.prefix_hashes,
            dependencies: self.dependency_hasher.finish(),
        }
    }
}
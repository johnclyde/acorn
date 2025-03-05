use fxhash::FxHasher;
use serde::{Deserialize, Serialize};
use std::error::Error;
use std::fs::File;
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::path::Path;

use crate::module::{Module, ModuleDescriptor};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ModuleCache {
    // This single hash represents all dependencies.
    dependencies: u64,

    // There is one prefix hash per line in the file.
    // Each one hashes that line and all the lines before it.
    prefixes: Vec<u32>,
}

impl ModuleCache {
    pub fn new(prefixes: u32, dependencies: u64) -> ModuleCache {
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

    pub fn save(&self, filename: &Path) -> Result<(), Box<dyn Error>> {
        let content = serde_yaml::to_string(&self)?;
        let mut file = File::create(filename)?;
        file.write_all(content.as_bytes())?;
        Ok(())
    }

    pub fn load(filename: &Path) -> Result<ModuleCache, Box<dyn Error>> {
        let file = File::open(filename)?;
        let cache = serde_yaml::from_reader(file)?;
        Ok(cache)
    }

    // Loads a ModuleCache along with its descriptor.
    pub fn load_relative(
        root: &Path,
        full_filename: &Path,
    ) -> Option<(ModuleDescriptor, ModuleCache)> {
        let relative_filename = full_filename.strip_prefix(root).ok()?;
        let ext = relative_filename.extension()?;
        if ext != "yaml" {
            return None;
        }
        let stem = relative_filename.file_stem()?;
        let name = stem.to_string_lossy().to_string().replace("/", ".");
        let descriptor = ModuleDescriptor::Name(name);
        let module_cache = ModuleCache::load(full_filename).ok()?;
        Some((descriptor, module_cache))
    }
}

pub struct ModuleHasher {
    // Will become part of the ModuleCache
    prefix_hashes: Vec<u32>,

    // For hashing the dependencies of the module
    dependency_hasher: FxHasher,
}

impl ModuleHasher {
    pub fn new(text: &str) -> ModuleHasher {
        let mut line_hasher = FxHasher::default();
        let mut prefix_hashes = vec![];
        for line in text.lines() {
            line.hash(&mut line_hasher);
            prefix_hashes.push(line_hasher.finish() as u32);
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

#[cfg(test)]
mod tests {
    use tempfile::tempdir;

    use super::*;
    use std::fs;
    use std::io::Read;

    #[test]
    fn test_save_and_load() {
        // Create a temporary directory for our test
        let temp_dir = tempdir().expect("Failed to create temp directory");
        let file_path = temp_dir.path().join("test_cache.yaml");

        let original_cache = ModuleCache {
            prefixes: vec![12345, 23456],
            dependencies: 67890,
        };

        // Save the cache to a file
        original_cache
            .save(&file_path)
            .expect("Failed to save cache");

        // Verify file was created and contains YAML
        assert!(file_path.exists());
        let mut file = File::open(&file_path).expect("Failed to open file");
        let mut contents = String::new();
        file.read_to_string(&mut contents)
            .expect("Failed to read file");
        assert!(contents.contains("prefixes:"));
        assert!(contents.contains("dependencies: 678"));

        // Load the cache from the file
        let loaded_cache = ModuleCache::load(&file_path).expect("Failed to load cache");
        assert_eq!(original_cache, loaded_cache);

        // Clean up
        fs::remove_file(file_path).expect("Failed to clean up test file");
    }
}

use fxhash::FxHasher;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs::File;
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::path::Path;

use crate::module::{Module, ModuleDescriptor};

// The ModuleHash reflects the state of a module that is loadable, but may or may not be verifiable.
#[derive(Debug)]
pub struct ModuleHash {
    // The dependencies hash represents all dependencies.
    dependencies: u64,

    // The content hash represents just the content of the file.
    // It's zero if there are no lines in the file.
    content: u64,

    // There is one prefix hash per line in the file.
    // Each one hashes that line and all the lines before it.
    // The last one should match the content hash.
    prefix_hashes: Vec<u64>,
}

impl ModuleHash {
    // Hashes the dependencies of a module into a single hash.
    // The dependencies should be in alphabetical order by name.
    fn hash_dependencies<'a>(deps: impl IntoIterator<Item = &'a Module>) -> u64 {
        let mut hasher = FxHasher::default();
        for dep in deps {
            if let Some(h) = &dep.hash {
                h.dependencies.hash(&mut hasher);
                h.content.hash(&mut hasher);
            }
        }
        hasher.finish()
    }

    // Returns a content hash, and a list of prefix hashes.
    fn hash_content(text: &str) -> (u64, Vec<u64>) {
        let mut line_hasher = FxHasher::default();
        let mut prefix_hashes = vec![];
        for line in text.lines() {
            line.hash(&mut line_hasher);
            prefix_hashes.push(line_hasher.finish());
        }
        let content = *prefix_hashes.last().unwrap_or(&0);
        (content, prefix_hashes)
    }

    pub fn new<'a>(text: &str, deps: impl IntoIterator<Item = &'a Module>) -> ModuleHash {
        let (content, prefix_hashes) = ModuleHash::hash_content(text);
        let dependencies = ModuleHash::hash_dependencies(deps);
        ModuleHash {
            dependencies,
            content,
            prefix_hashes,
        }
    }

    pub fn matches_through_line(&self, cache: &Option<ModuleCache>, line: u32) -> bool {
        let line = line as usize;
        match cache {
            Some(cache) => {
                if self.dependencies != cache.dependencies {
                    return false;
                }
                if self.content == cache.content {
                    return true;
                }
                line < self.prefix_hashes.len()
                    && self.prefix_hashes.get(line) == cache.prefix_hashes.get(line)
            }
            None => false,
        }
    }
}

// The ModuleCache reflects a module that we have previously verified successfully.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModuleCache {
    // dependencies, content, and prefix_hashes all match the ModuleHash.
    dependencies: u64,
    content: u64,

    // These aren't serialized because they are large and can be recomputed from the file.
    // So, they are optional and may be absent.
    #[serde(skip)]
    prefix_hashes: Vec<u64>,

    // theorems[theorem name][module name] = list of premises used in that module
    // TODO: see if we can serialize this.
    pub theorems: BTreeMap<String, BTreeMap<String, BTreeSet<String>>>,
}

impl ModuleCache {
    // Whether we should save this cache, given an existing one.
    pub fn requires_save(&self, existing: &ModuleCache) -> bool {
        self.dependencies != existing.dependencies || self.content != existing.content
    }

    pub fn save(&self, filename: &Path) -> Result<(), Box<dyn Error>> {
        let content = serde_yaml::to_string(&self)?;
        let mut file = File::create(filename)?;
        file.write_all(content.as_bytes())?;
        Ok(())
    }

    // Note: this does not populate prefixes.
    fn load(filename: &Path) -> Result<ModuleCache, Box<dyn Error>> {
        let file = File::open(filename)?;
        let cache = serde_yaml::from_reader(file)?;
        Ok(cache)
    }

    // Loads a ModuleCache along with its descriptor.
    // Note: this does not populate prefixes.
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

    pub fn new(hash: &ModuleHash) -> ModuleCache {
        ModuleCache {
            dependencies: hash.dependencies,
            content: hash.content,
            prefix_hashes: hash.prefix_hashes.clone(),
            theorems: BTreeMap::new(),
        }
    }

    // Asserts that the premises for the theorem are equal to the given list.
    // Syntax is module:theorem.
    pub fn assert_premises_eq(&self, theorem: &str, premises: &[&str]) {
        let premise_map = self.theorems.get(theorem).expect("no premises for theorem");
        let mut expected = vec![];
        for (module, names) in premise_map {
            for name in names {
                expected.push(format!("{}:{}", module, name));
            }
        }
        assert_eq!(expected, premises);
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
        let theorems: BTreeMap<String, BTreeMap<String, BTreeSet<String>>> = [(
            "theorem_name".to_string(),
            [(
                "module_name".to_string(),
                ["dependency_name".to_string()].into_iter().collect(),
            )]
            .into_iter()
            .collect(),
        )]
        .into_iter()
        .collect();
        let original_cache = ModuleCache {
            prefix_hashes: vec![12345, 23456],
            dependencies: 67890,
            content: 23456,
            theorems,
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
        assert!(contents.contains("dependencies: 678"));
        assert!(contents.contains("content: 23456"));
        assert!(contents.contains("theorem_name"));
        assert!(contents.contains("module_name"));
        assert!(contents.contains("dependency_name"));
        assert!(!contents.contains("prefix_hashes"));

        // Load the cache from the file
        let loaded_cache = ModuleCache::load(&file_path).expect("Failed to load cache");
        assert_eq!(original_cache.dependencies, loaded_cache.dependencies);
        assert_eq!(original_cache.content, loaded_cache.content);
        assert_eq!(original_cache.theorems, loaded_cache.theorems);
        assert!(!loaded_cache.requires_save(&original_cache));

        // Clean up
        fs::remove_file(file_path).expect("Failed to clean up test file");
    }
}

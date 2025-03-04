use std::hash::{Hash, Hasher};
use std::{fmt, path::PathBuf};

use fxhash::FxHasher;
use serde::{Deserialize, Serialize};

use crate::compilation;
use crate::environment::Environment;

// The code in one file is exposed to other Acorn code as a "module".
// You could have two different types both named "MyStruct" but defined in different places.
// Each name is uniquely identified not just by its string name, but also by the module it's defined in.
// When you look at the AcornType object, they should have each have a different ModuleId.
pub type ModuleId = u16;

// Some entities that are created for the prover get their own modules.
// Skolem functions are created during normalization to replace "exists" quantifiers.
pub const SKOLEM: ModuleId = 0;

// The regular module ids start here.
pub const FIRST_NORMAL: ModuleId = 1;

pub struct Module {
    // The way the user can refer to this module.
    pub descriptor: ModuleDescriptor,

    // The state of the module, whether it's been loaded or not.
    pub state: LoadState,

    // The hash of the module's code.
    // None before the module is loaded.
    pub hash: Option<ModuleHash>,
}

impl Module {
    pub fn default_modules() -> Vec<Module> {
        let mut modules = vec![];
        while modules.len() < FIRST_NORMAL as usize {
            modules.push(Module::anonymous());
        }
        modules
    }

    pub fn anonymous() -> Module {
        Module {
            descriptor: ModuleDescriptor::Anonymous,
            state: LoadState::None,
            hash: None,
        }
    }

    // New modules start in the Loading state.
    pub fn new(descriptor: ModuleDescriptor) -> Module {
        Module {
            descriptor,
            state: LoadState::Loading,
            hash: None,
        }
    }

    pub fn load_error(&mut self, error: compilation::Error) {
        self.state = LoadState::Error(error);
    }

    // Called when a module load succeeds.
    pub fn load_ok(&mut self, env: Environment, hash: ModuleHash) {
        self.state = LoadState::Ok(env);
        self.hash = Some(hash);
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModuleHash {
    // There is one prefix hash per line in the file.
    // Each one hashes that line and all the lines before it.
    prefixes: Vec<u64>,

    // This single hash represents all dependencies.
    dependencies: u64,
}

impl ModuleHash {
    pub fn new(prefixes: u64, dependencies: u64) -> ModuleHash {
        ModuleHash {
            prefixes: vec![prefixes],
            dependencies,
        }
    }

    pub fn matches_through_line(&self, other: &Option<ModuleHash>, line: u32) -> bool {
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
    // Will become part of the ModuleHash
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

    pub fn finish(self) -> ModuleHash {
        ModuleHash {
            prefixes: self.prefix_hashes,
            dependencies: self.dependency_hasher.finish(),
        }
    }
}

// The LoadState describes the state of a module, loaded or not or in progress.
pub enum LoadState {
    // There is no such module, not even an id for it
    None,

    // The module is in the process of being loaded.
    // Modules that fail on circular import will be in this state forever.
    Loading,

    // The module has been loaded, but there is an error in its code
    Error(compilation::Error),

    // The module has been loaded successfully and we have its environment
    Ok(Environment),
}

// A Descriptor expresses the different ways that a module user can specify a module.
#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub enum ModuleDescriptor {
    // Anything that can't be referred to
    Anonymous,

    // An import chain like foo.bar.baz
    // This sort of module can be either loaded by a project, or referred to in code.
    Name(String),

    // A filename.
    // This sort of module can be loaded by a project, but not referred to in code.
    File(PathBuf),
}

impl fmt::Display for ModuleDescriptor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            ModuleDescriptor::Anonymous => write!(f, "<anonymous>"),
            ModuleDescriptor::Name(name) => write!(f, "{}", name),
            ModuleDescriptor::File(path) => write!(f, "{}", path.display()),
        }
    }
}

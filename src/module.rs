use std::hash::{Hash, Hasher};
use std::{fmt, path::PathBuf};

use fxhash::FxHasher;

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

impl Hash for Module {
    // Used for hashing this module as a dependency.
    fn hash<H: Hasher>(&self, state: &mut H) {
        if let Some(h) = &self.hash {
            if let Some(last_prefix_hash) = h.prefix_hashes.last() {
                last_prefix_hash.hash(state);
            }
            h.dependency_hash.hash(state);
        }
    }
}

#[derive(Debug, Clone)]
pub struct ModuleHash {
    // There is one prefix hash per line in the file.
    // Each one hashes that line and all the lines before it.
    prefix_hashes: Vec<u64>,

    // This single hash represents all dependencies.
    dependency_hash: u64,
}

impl PartialEq for ModuleHash {
    // We don't need to check every prefix hash, just the last one.
    fn eq(&self, other: &Self) -> bool {
        self.dependency_hash == other.dependency_hash
            && self.prefix_hashes.last() == other.prefix_hashes.last()
    }
}

impl ModuleHash {
    pub fn new(prefix_hash: u64, dependency_hash: u64) -> ModuleHash {
        ModuleHash {
            prefix_hashes: vec![prefix_hash],
            dependency_hash,
        }
    }
}

pub struct ModuleHasher {
    // Will become part of the ModuleHash
    prefix_hashes: Vec<u64>,

    // For hashing the lines of code in the module
    line_hasher: FxHasher,

    // For hashing the dependencies of the module
    dependency_hasher: FxHasher,
}

impl ModuleHasher {
    pub fn new() -> ModuleHasher {
        ModuleHasher {
            prefix_hashes: vec![],
            line_hasher: FxHasher::default(),
            dependency_hasher: FxHasher::default(),
        }
    }

    // Can only be called once.
    pub fn set_text(&mut self, text: &str) {
        assert!(self.prefix_hashes.is_empty());
        text.hash(&mut self.line_hasher);
        self.prefix_hashes.push(self.line_hasher.finish());
    }

    // Should be called in an order that's consistent across different hashes of the same module
    pub fn add_dependency(&mut self, module: &Module) {
        if let Some(h) = &module.hash {
            if let Some(last_prefix_hash) = h.prefix_hashes.last() {
                last_prefix_hash.hash(&mut self.dependency_hasher);
            }
            h.dependency_hash.hash(&mut self.dependency_hasher);
        }
    }

    pub fn finish(self) -> ModuleHash {
        ModuleHash {
            prefix_hashes: self.prefix_hashes,
            dependency_hash: self.dependency_hasher.finish(),
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

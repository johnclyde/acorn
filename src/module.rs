use std::{fmt, path::PathBuf};

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

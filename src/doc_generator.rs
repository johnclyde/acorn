use std::fmt;
use std::io::Write;
use std::path::Path;

use crate::acorn_type::Datatype;
use crate::environment::Environment;
use crate::project::Project;

#[derive(Debug)]
pub enum DocError {
    IoError(std::io::Error),
    DirectoryNotFound(String),
    NotADirectory(String),
}

impl fmt::Display for DocError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DocError::IoError(e) => write!(f, "{}", e),
            DocError::DirectoryNotFound(path) => write!(f, "Directory '{}' does not exist", path),
            DocError::NotADirectory(path) => write!(f, "'{}' is not a directory", path),
        }
    }
}

impl From<std::io::Error> for DocError {
    fn from(err: std::io::Error) -> Self {
        DocError::IoError(err)
    }
}

pub struct DocGenerator<'a> {
    project: &'a Project,
}

impl<'a> DocGenerator<'a> {
    pub fn new(project: &'a Project) -> Self {
        DocGenerator { project }
    }

    /// Documents a type by writing all its methods to a markdown file.
    /// env: The environment containing the type
    /// type_name: The name of the type (e.g., "Int")
    /// datatype: The datatype to document
    /// filename: Where to write the documentation
    pub fn document_type(
        &self,
        env: &Environment,
        type_name: &str,
        datatype: &Datatype,
        filename: impl AsRef<Path>,
    ) -> Result<(), DocError> {
        let mut methods = env.bindings.get_datatype_attributes(datatype);
        methods.sort();

        let mut file = std::fs::File::create(filename)?;

        writeln!(file, "# {} Type Documentation\n", type_name)?;

        for method_name in methods {
            writeln!(file, "## {}", method_name)?;
        }

        Ok(())
    }

    /// Generates documentation for all types in all top-level modules.
    /// Creates one file named "Typename.md" for each type in the doc_root directory.
    pub fn generate(&self, doc_root: impl AsRef<Path>) -> Result<(), DocError> {
        let doc_root = doc_root.as_ref();

        if !doc_root.exists() {
            return Err(DocError::DirectoryNotFound(doc_root.display().to_string()));
        }
        if !doc_root.is_dir() {
            return Err(DocError::NotADirectory(doc_root.display().to_string()));
        }

        // Iterate over all modules
        for (descriptor, module_id) in self.project.iter_modules() {
            // Skip non-top-level modules
            if !descriptor.is_top_level() {
                continue;
            }

            // Get the module environment
            let env = match self.project.get_env_by_id(module_id) {
                Some(env) => env,
                None => continue, // Skip if we can't get the environment
            };

            // Iterate over all types in this module
            for (type_name, potential_type) in env.bindings.iter_types() {
                // Extract the base datatype
                let datatype = match potential_type.as_base_datatype() {
                    Some(dt) => dt,
                    None => continue, // Skip types without a base datatype
                };

                // Only document if the type name matches the datatype's name
                // This ensures we're using the canonical name
                if type_name != &datatype.name {
                    continue;
                }

                // Only document if this is the authoritative source
                // Either the module that defines the datatype, or a module whose name matches
                if module_id != datatype.module_id && !descriptor.is_authoritative_name(&datatype.name) {
                    continue;
                }

                // Create the output filename
                let filename = doc_root.join(format!("{}.md", type_name));

                // Document this type
                self.document_type(env, type_name, datatype, filename)?;
            }
        }

        Ok(())
    }
}

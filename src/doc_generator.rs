use std::collections::HashMap;
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
    MissingCategoryFile(String),
    DocumentationConflict {
        type_name: String,
        first_module: String,
        second_module: String,
    },
}

impl fmt::Display for DocError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DocError::IoError(e) => write!(f, "{}", e),
            DocError::DirectoryNotFound(path) => write!(f, "Directory '{}' does not exist", path),
            DocError::NotADirectory(path) => write!(f, "'{}' is not a directory", path),
            DocError::MissingCategoryFile(path) => write!(
                f,
                "Directory '{}' is missing required _category_.json file",
                path
            ),
            DocError::DocumentationConflict {
                type_name,
                first_module,
                second_module,
            } => {
                write!(f, "Documentation conflict for type '{}': both modules '{}' and '{}' appear to be authoritative", 
                       type_name, first_module, second_module)
            }
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
        // Filter out attributes that are wholly numeric
        methods.retain(|name| !name.chars().all(|c| c.is_numeric()));
        methods.sort();
        println!("{}", filename.as_ref().display());
        let mut file = std::fs::File::create(filename)?;

        writeln!(file, "# {}", type_name)?;

        // Write doc comments if they exist
        if let Some(doc_comments) = env.bindings.get_datatype_doc_comment(datatype) {
            writeln!(file)?;
            for comment in doc_comments {
                writeln!(file, "{}", comment)?;
            }
        }

        for method_name in methods {
            writeln!(file, "## {}", method_name)?;
        }

        Ok(())
    }

    /// Generates documentation for all types in all top-level modules.
    /// Creates one file named "Typename.md" for each type in the doc_root directory.
    /// Returns the number of files created.
    pub fn generate(&self, doc_root: impl AsRef<Path>) -> Result<usize, DocError> {
        let doc_root = doc_root.as_ref();

        if !doc_root.exists() {
            return Err(DocError::DirectoryNotFound(doc_root.display().to_string()));
        }
        if !doc_root.is_dir() {
            return Err(DocError::NotADirectory(doc_root.display().to_string()));
        }

        // Check for _category_.json file
        let category_file = doc_root.join("_category_.json");
        if !category_file.exists() {
            return Err(DocError::MissingCategoryFile(
                doc_root.display().to_string(),
            ));
        }

        // Remove all existing .md files in the directory
        for entry in std::fs::read_dir(doc_root)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_file() && path.extension().and_then(|s| s.to_str()) == Some("md") {
                std::fs::remove_file(path)?;
            }
        }

        let mut documented_types: HashMap<String, String> = HashMap::new();
        let mut file_count = 0;

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
                if module_id != datatype.module_id
                    && !descriptor.is_authoritative_name(&datatype.name)
                {
                    continue;
                }

                // Check if we've already documented this type
                if let Some(first_module) = documented_types.get(type_name) {
                    return Err(DocError::DocumentationConflict {
                        type_name: type_name.clone(),
                        first_module: first_module.clone(),
                        second_module: descriptor.to_string(),
                    });
                }

                // Record that we're documenting this type from this module
                documented_types.insert(type_name.clone(), descriptor.to_string());

                // Create the output filename
                let filename = doc_root.join(format!("{}.md", type_name));

                self.document_type(env, type_name, datatype, filename)?;
                file_count += 1;
            }
        }

        Ok(file_count)
    }
}

use std::io::Write;
use std::path::Path;

use crate::acorn_type::{AcornType, Datatype, PotentialType};
use crate::binding_map::BindingMap;
use crate::module::ModuleDescriptor;
use crate::project::Project;

pub struct DocGenerator<'a> {
    project: &'a Project,
}

impl<'a> DocGenerator<'a> {
    pub fn new(project: &'a Project) -> Self {
        DocGenerator { project }
    }

    /// Documents a type by writing all its methods to a markdown file.
    /// module_name: The module where the type is defined (e.g., "int")
    /// type_name: The name of the type (e.g., "Int")
    /// filename: Where to write the documentation
    pub fn document_type(&self, module_name: &str, type_name: &str, filename: impl AsRef<Path>) -> Result<(), String> {
        // Get the module environment
        let descriptor = ModuleDescriptor::Name(module_name.to_string());
        let env = self.project
            .get_env(&descriptor)
            .ok_or_else(|| format!("Module '{}' not found", module_name))?;
        
        // Find the datatype
        let datatype = self.find_datatype(&env.bindings, type_name)
            .ok_or_else(|| format!("Type '{}' not found in module '{}'", type_name, module_name))?;
        
        // Get methods visible from this module
        let methods = self.get_visible_methods(&env.bindings, &datatype);
        
        // Write to file
        let mut file = std::fs::File::create(filename)
            .map_err(|e| format!("Failed to create file: {}", e))?;
        
        // Write header
        writeln!(file, "# {} Type Documentation\n", type_name)
            .map_err(|e| format!("Failed to write header: {}", e))?;
        
        // Write methods
        for method_name in methods {
            writeln!(file, "## {}", method_name)
                .map_err(|e| format!("Failed to write method: {}", e))?;
        }
        
        Ok(())
    }
    
    /// Find a datatype by name in the bindings
    fn find_datatype(&self, bindings: &BindingMap, type_name: &str) -> Option<Datatype> {
        // Look through all datatypes to find one matching the name
        bindings.get_type_for_typename(type_name).and_then(|potential_type| {
            if let PotentialType::Resolved(AcornType::Data(datatype, _)) = potential_type {
                Some(datatype.clone())
            } else {
                None
            }
        })
    }
    
    /// Get methods (attributes) visible from the given bindings for a datatype
    fn get_visible_methods(&self, bindings: &BindingMap, datatype: &Datatype) -> Vec<String> {
        let mut methods = bindings.get_datatype_attributes(datatype);
        methods.sort();
        methods
    }
}
use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::{AcornType, TypeParam};
use crate::acorn_value::AcornValue;
use crate::compilation::{ErrorSource, Result};
use crate::source::{Source, SourceType};

/// A value along with information on where to find it in the source.
#[derive(Debug, Clone)]
pub struct Proposition {
    /// A boolean value. The essence of the proposition is "value is true".
    pub value: AcornValue,

    /// The type parameters that this proposition can be instantiated with.
    pub params: Vec<TypeParam>,

    /// Where this proposition came from.
    pub source: Source,
}

impl fmt::Display for Proposition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.params.is_empty() {
            write!(f, "{} ", TypeParam::params_to_str(&self.params))?;
        }
        self.value.fmt(f)
    }
}

impl Proposition {
    /// Creates a proposition that may be generic. Params can be empty.
    pub fn new(value: AcornValue, params: Vec<TypeParam>, source: Source) -> Proposition {
        if source.importable && value.has_arbitrary() {
            panic!(
                "importable propositions should not have arbitrary types, at {:?}",
                source
            );
        }
        Proposition {
            value,
            params,
            source,
        }
    }

    /// Creates a non-generic proposition.
    pub fn monomorphic(value: AcornValue, source: Source) -> Proposition {
        assert!(!value.has_generic());
        Proposition::new(value, vec![], source)
    }

    /// Just changes the value while keeping the other stuff intact
    pub fn with_value(self, value: AcornValue) -> Proposition {
        Proposition::new(value, self.params, self.source)
    }

    /// Theorems have theorem names, and so do axioms because those work like theorems.
    pub fn theorem_name(&self) -> Option<&str> {
        match &self.source.source_type {
            SourceType::Axiom(name) | SourceType::Theorem(name) => name.as_deref(),
            _ => None,
        }
    }

    /// Instantiates a generic proposition to have a particular type.
    pub fn instantiate(&self, params: &[(String, AcornType)]) -> MonomorphicProposition {
        if self.params.len() != params.len() {
            panic!(
                "proposition has {} params, but we tried to instantiate with {}",
                self.params.len(),
                params.len()
            );
        }
        let value = self.value.instantiate(params);
        if value.has_generic() {
            let joined = params
                .iter()
                .map(|(p, _)| p.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            panic!("instantiated {} but {} is still generic", joined, value);
        }
        let source = match &self.source.source_type {
            SourceType::ConstantDefinition(v, name) => {
                let new_type = SourceType::ConstantDefinition(v.instantiate(params), name.clone());
                Source {
                    module_id: self.source.module_id,
                    range: self.source.range.clone(),
                    source_type: new_type,
                    importable: self.source.importable,
                    depth: self.source.depth,
                }
            }
            _ => self.source.clone(),
        };
        MonomorphicProposition { value, source }
    }

    pub fn as_monomorphic(&self) -> Option<MonomorphicProposition> {
        if self.params.is_empty() {
            Some(MonomorphicProposition {
                value: self.value.clone(),
                source: self.source.clone(),
            })
        } else {
            None
        }
    }

    /// Validates that the params exactly match the type variables used in the value.
    /// Returns an error if there's a mismatch.
    pub fn validate_params(&self, source: &dyn ErrorSource) -> Result<()> {
        // Collect all type variables from the value
        let mut value_vars = HashMap::new();
        self.value.find_type_vars(&mut value_vars, source)?;

        // Check that every param is used in the value
        for param in &self.params {
            if !value_vars.contains_key(&param.name) {
                return Err(source.error(&format!(
                    "Type parameter '{}' is declared but not used in the value",
                    param.name
                )));
            }
        }

        // Check that every type variable in the value is declared in params
        for (var_name, var_param) in &value_vars {
            if !self.params.iter().any(|p| &p.name == var_name) {
                return Err(source.error(&format!(
                    "Type variable '{}' is used in the value but not declared in parameters",
                    var_name
                )));
            }

            // Check that the typeclasses match for declared parameters
            if let Some(param) = self.params.iter().find(|p| &p.name == var_name) {
                if param.typeclass != var_param.typeclass {
                    return Err(source.error(&format!(
                        "Type variable '{}' has different typeclass constraints in declaration ({:?}) and usage ({:?})",
                        var_name, param.typeclass, var_param.typeclass
                    )));
                }
            }
        }

        // Check that the number of params matches the number of unique type variables
        if self.params.len() != value_vars.len() {
            return Err(source.error(&format!(
                "Mismatch between number of declared type parameters ({}) and used type variables ({})",
                self.params.len(), value_vars.len()
            )));
        }

        Ok(())
    }
}

/// A proposition that is not generic.
#[derive(Debug, Clone)]
pub struct MonomorphicProposition {
    /// A boolean value. The essence of the proposition is "value is true".
    pub value: AcornValue,

    /// Where this proposition came from.
    pub source: Source,
}

impl fmt::Display for MonomorphicProposition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.fmt(f)
    }
}

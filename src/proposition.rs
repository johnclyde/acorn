use std::fmt;

use crate::acorn_type::{AcornType, TypeParam};
use crate::acorn_value::AcornValue;
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
        // TODO: is it correct to have this check here?
        // if source.importable && value.has_arbitrary() {
        //     panic!("importable propositions should not have arbitrary types");
        // }
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
        let value = self.value.instantiate(params);
        if value.has_generic() {
            panic!("tried to instantiate but {} is still generic", value);
        }
        let source = match &self.source.source_type {
            SourceType::ConstantDefinition(v, name) => {
                let new_type = SourceType::ConstantDefinition(v.instantiate(params), name.clone());
                Source {
                    module: self.source.module,
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

use std::fmt;

use crate::acorn_type::{AcornType, PotentialType, Typeclass, UnresolvedType};
use crate::acorn_value::AcornValue;
use crate::compilation::{self, ErrorSource};
use crate::module::ModuleId;
use crate::potential_value::PotentialValue;
use crate::unresolved_constant::UnresolvedConstant;

// A name can refer to any of these things.
#[derive(Debug, Clone, PartialEq)]
pub enum NamedEntity {
    Value(AcornValue),
    Type(AcornType),
    Module(ModuleId),
    Typeclass(Typeclass),

    // A constant that we don't know the specific type of yet.
    UnresolvedValue(UnresolvedConstant),

    // A generic type that we don't know the instantiated type of yet.
    UnresolvedType(UnresolvedType),
}

impl NamedEntity {
    // Create a new NamedEntity from a PotentialValue
    pub fn new(value: PotentialValue) -> Self {
        match value {
            PotentialValue::Unresolved(u) => NamedEntity::UnresolvedValue(u),
            PotentialValue::Resolved(v) => NamedEntity::Value(v),
        }
    }

    // Convert this entity into a PotentialValue, erroring if it's not the right sort of entity.
    pub fn expect_potential_value(
        self,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorSource,
    ) -> compilation::Result<PotentialValue> {
        match self {
            NamedEntity::Value(value) => {
                value.get_type().check_eq(expected_type, source)?;
                Ok(PotentialValue::Resolved(value))
            }
            NamedEntity::Type(_) | NamedEntity::UnresolvedType(_) => {
                Err(source.error("name refers to a type but we expected a value"))
            }
            NamedEntity::Module(_) => {
                Err(source.error("name refers to a module but we expected a value"))
            }
            NamedEntity::Typeclass(_) => {
                Err(source.error("name refers to a typeclass but we expected a value"))
            }
            NamedEntity::UnresolvedValue(u) => {
                // TODO: should we typecheck?
                Ok(PotentialValue::Unresolved(u))
            }
        }
    }

    // Convert this entity into a PotentialType, erroring if it's not the right sort of type.
    pub fn expect_potential_type(
        self,
        source: &dyn ErrorSource,
    ) -> compilation::Result<PotentialType> {
        match self {
            NamedEntity::Value(_) => {
                Err(source.error("name refers to a value but we expected a type"))
            }
            NamedEntity::Type(t) => Ok(PotentialType::Resolved(t)),
            NamedEntity::UnresolvedType(u) => Ok(PotentialType::Unresolved(u)),
            NamedEntity::Module(_) => {
                Err(source.error("name refers to a module but we expected a type"))
            }
            NamedEntity::Typeclass(_) => {
                Err(source.error("name refers to a typeclass but we expected a type"))
            }
            NamedEntity::UnresolvedValue(_) => {
                Err(source.error("name refers to an unresolved value but we expected a type"))
            }
        }
    }
}

impl fmt::Display for NamedEntity {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            NamedEntity::Value(value) => write!(f, "{}", value),
            NamedEntity::Type(typ) => write!(f, "{}", typ),
            NamedEntity::Module(module_id) => write!(f, "module_{}", module_id),
            NamedEntity::Typeclass(typeclass) => write!(f, "{:?}", typeclass),
            NamedEntity::UnresolvedValue(unresolved) => write!(f, "{:?}", unresolved),
            NamedEntity::UnresolvedType(unresolved) => write!(f, "{:?}", unresolved),
        }
    }
}

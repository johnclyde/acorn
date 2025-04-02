use crate::acorn_type::{AcornType, TypeParam};
use crate::acorn_value::AcornValue;
use crate::compilation::{self, ErrorSource};
use crate::names::GlobalName;
use crate::unresolved_constant::UnresolvedConstant;

pub static EMPTY_TYPE_PARAMS: [TypeParam; 0] = [];

// Could be a value, but could also be an unresolved constant.
#[derive(Debug, Clone)]
pub enum PotentialValue {
    // (module, constant name, type, type parameters)
    Unresolved(UnresolvedConstant),

    // Something that we do know the type of.
    Resolved(AcornValue),
}

impl PotentialValue {
    // Convert this to a value, panicking if it's unresolved.
    pub fn force_value(self) -> AcornValue {
        match self {
            PotentialValue::Unresolved(u) => {
                panic!("tried to force unresolved constant {}", u.name.local_name);
            }
            PotentialValue::Resolved(c) => c,
        }
    }

    // Convert this to a value, or return an error if it's unresolved.
    pub fn as_value(self, source: &dyn ErrorSource) -> compilation::Result<AcornValue> {
        match self {
            PotentialValue::Unresolved(u) => {
                Err(source.error(&format!("value {} has unresolved type", u.name.local_name)))
            }
            PotentialValue::Resolved(c) => Ok(c),
        }
    }

    // If this is an unresolved value, it will have a generic type.
    pub fn get_type(&self) -> AcornType {
        match &self {
            PotentialValue::Unresolved(u) => u.generic_type.clone(),
            PotentialValue::Resolved(v) => v.get_type(),
        }
    }

    // Gets the unresolved parameters, if this is unresolved.
    pub fn unresolved_params(&self) -> &[TypeParam] {
        match &self {
            PotentialValue::Unresolved(u) => &u.params,
            PotentialValue::Resolved(_) => &EMPTY_TYPE_PARAMS,
        }
    }

    pub fn as_unresolved(
        self,
        source: &dyn ErrorSource,
    ) -> compilation::Result<UnresolvedConstant> {
        match self {
            PotentialValue::Unresolved(u) => Ok(u),
            PotentialValue::Resolved(v) => {
                Err(source.error(&format!("expected unresolved value, but found {}", v)))
            }
        }
    }

    // Resolve this into a value, using type variables for unknown parameters.
    pub fn to_generic_value(self) -> AcornValue {
        match self {
            PotentialValue::Unresolved(u) => u.to_generic_value(),
            PotentialValue::Resolved(v) => v,
        }
    }

    // Create a potential value for a constant. Can be unresolved, in which case we need params.
    pub fn constant(
        name: GlobalName,
        constant_type: AcornType,
        params: Vec<TypeParam>,
    ) -> PotentialValue {
        if params.is_empty() {
            PotentialValue::Resolved(AcornValue::constant(name, vec![], constant_type))
        } else {
            PotentialValue::Unresolved(UnresolvedConstant {
                name,
                params,
                generic_type: constant_type,
            })
        }
    }
}

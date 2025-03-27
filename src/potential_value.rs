use crate::acorn_type::{AcornType, TypeParam};
use crate::acorn_value::AcornValue;
use crate::compilation::{self, ErrorSource};
use crate::constant_name::LocalConstantName;
use crate::module::ModuleId;
use crate::unresolved_constant::UnresolvedConstant;

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
                panic!("tried to force unresolved constant {}", u.name);
            }
            PotentialValue::Resolved(c) => c,
        }
    }

    // Convert this to a value, or return an error if it's unresolved.
    pub fn as_value(self, source: &dyn ErrorSource) -> compilation::Result<AcornValue> {
        match self {
            PotentialValue::Unresolved(u) => {
                Err(source.error(&format!("value {} has unresolved type", u.name)))
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

    // Create a constant. Can be unresolved, in which case we need params.
    pub fn constant(
        module_id: ModuleId,
        name: &LocalConstantName,
        constant_type: AcornType,
        params: Vec<TypeParam>,
    ) -> PotentialValue {
        if params.is_empty() {
            PotentialValue::Resolved(AcornValue::constant(
                module_id,
                name.to_string(),
                vec![],
                constant_type,
            ))
        } else {
            PotentialValue::Unresolved(UnresolvedConstant {
                module_id,
                name: name.to_string(),
                params,
                generic_type: constant_type,
            })
        }
    }
}

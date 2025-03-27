use crate::acorn_type::{AcornType, TypeParam};
use crate::acorn_value::AcornValue;
use crate::compilation::{self, ErrorSource};
use crate::module::ModuleId;

// A generic constant that we don't know the type of yet.
// It's more of a "constant with unresolved type" than an "unresolved constant".
#[derive(Debug, Clone)]
pub struct UnresolvedConstant {
    pub module_id: ModuleId,

    // The name can have a dot in it, indicating this value is <typename>.<constantname>.
    pub name: String,

    // The type parameters are all the type variables used in the definition of this constant,
    // in their canonical order. Each of these type parameters should be referenced in the type of
    // the constant itself. Otherwise we would not be able to infer them.
    pub params: Vec<TypeParam>,

    // The generic type uses the params.
    pub generic_type: AcornType,
}

impl UnresolvedConstant {
    pub fn resolve(
        &self,
        source: &dyn ErrorSource,
        params: Vec<AcornType>,
    ) -> compilation::Result<AcornValue> {
        if params.len() != self.params.len() {
            return Err(source.error(&format!(
                "expected {} type parameters, but got {}",
                self.params.len(),
                params.len()
            )));
        }

        let named_params: Vec<_> = self
            .params
            .iter()
            .zip(params.iter())
            .map(|(param, t)| (param.name.clone(), t.clone()))
            .collect();
        let resolved_type = self.generic_type.instantiate(&named_params);
        Ok(AcornValue::constant(
            self.module_id,
            self.name.clone(),
            params,
            resolved_type,
        ))
    }
}

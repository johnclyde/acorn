use std::collections::HashMap;

use crate::acorn_type::{AcornType, Class, Typeclass};

/// Utility for matching types during unification.
pub struct TypeUnifier {
    /// Type unification fills in a mapping for any parametric types that need to be specified,
    /// in order to make it match.
    /// Every parameter used in self will get a mapping entry.
    pub mapping: HashMap<String, AcornType>,
}

impl TypeUnifier {
    pub fn new() -> Self {
        TypeUnifier {
            mapping: HashMap::new(),
        }
    }

    /// Figures out whether it is possible to instantiate self to get instance.
    ///
    /// "validator" is a function that checks whether a typeclass is valid for a given type.
    /// This is abstracted out because the prover and the compiler have different ideas of what is valid.
    ///
    /// Returns whether it was successful.
    pub fn match_instance(
        &mut self,
        generic_type: &AcornType,
        instance: &AcornType,
        validator: &mut dyn FnMut(&Class, &Typeclass) -> bool,
    ) -> bool {
        match (generic_type, instance) {
            (AcornType::Variable(param), _) => {
                if let Some(t) = self.mapping.get(&param.name) {
                    // This type variable is already mapped
                    return t == instance;
                }
                if let Some(typeclass) = param.typeclass.as_ref() {
                    match instance {
                        AcornType::Data(class, _) => {
                            if !validator(&class, typeclass) {
                                return false;
                            }
                        }
                        AcornType::Arbitrary(param) | AcornType::Variable(param) => {
                            match &param.typeclass {
                                Some(tc) => {
                                    if tc != typeclass {
                                        return false;
                                    }
                                }
                                None => return false,
                            }
                        }
                        _ => return false,
                    }
                }
                self.mapping.insert(param.name.clone(), instance.clone());
                true
            }
            (AcornType::Function(f), AcornType::Function(g)) => {
                if f.arg_types.len() != g.arg_types.len() {
                    return false;
                }
                if !self.match_instance(&f.return_type, &g.return_type, validator) {
                    return false;
                }
                for (f_arg_type, g_arg_type) in f.arg_types.iter().zip(&g.arg_types) {
                    if !self.match_instance(f_arg_type, g_arg_type, validator) {
                        return false;
                    }
                }
                true
            }
            (AcornType::Data(g_class, g_params), AcornType::Data(i_class, i_params)) => {
                if g_class != i_class || g_params.len() != i_params.len() {
                    return false;
                }
                for (g_param, i_param) in g_params.iter().zip(i_params) {
                    if !self.match_instance(g_param, i_param, validator) {
                        return false;
                    }
                }
                true
            }
            _ => generic_type == instance,
        }
    }
}

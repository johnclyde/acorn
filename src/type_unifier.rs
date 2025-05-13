use std::collections::HashMap;

use crate::acorn_type::{AcornType, Class, Typeclass};

/// Utility for matching types during unification.
pub struct TypeUnifier {
    /// Type unification fills in a mapping for any parametric types that need to be specified,
    /// in order to make it match.
    /// Every parameter used in self will get a mapping entry.
    pub mapping: HashMap<String, AcornType>,
}

/// The different errors we can get from unification.
pub enum Error {
    /// Unification failed, because this class is not an instance of this typeclass.
    Class(Class, Typeclass),

    /// Unification failed becaue the first typeclass is not an extension of the second.
    /// TypeclassFailure(A, B) indicates that A does not extend B.
    /// This is directional. Field extends Ring, but not vice versa.
    Typeclass(Typeclass, Typeclass),

    /// Unification failed for some other reason.
    Other,
}

/// The unifier itself does not know which typeclasses correspond to what.
/// The registry is responsible for that.
pub trait TypeclassRegistry {
    /// Returns true if the class is an instance of the typeclass.
    fn is_instance_of(&self, class: &Class, typeclass: &Typeclass) -> bool;

    /// Returns true if typeclass extends base.
    fn extends(&self, typeclass: &Typeclass, base: &Typeclass) -> bool;
}

pub type Result = std::result::Result<(), Error>;

fn require_eq(t1: &AcornType, t2: &AcornType) -> Result {
    if t1 == t2 {
        Ok(())
    } else {
        Err(Error::Other)
    }
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
        instance_type: &AcornType,
        registry: &dyn TypeclassRegistry,
    ) -> Result {
        match (generic_type, instance_type) {
            (AcornType::Variable(param), _) => {
                if let Some(t) = self.mapping.get(&param.name) {
                    // This type variable is already mapped
                    return require_eq(t, instance_type);
                }
                if let Some(generic_typeclass) = param.typeclass.as_ref() {
                    match instance_type {
                        AcornType::Data(class, _) => {
                            if !registry.is_instance_of(&class, generic_typeclass) {
                                return Err(Error::Class(class.clone(), generic_typeclass.clone()));
                            }
                        }
                        AcornType::Arbitrary(param) | AcornType::Variable(param) => {
                            match &param.typeclass {
                                Some(instance_typeclass) => {
                                    if instance_typeclass != generic_typeclass
                                        && !registry.extends(instance_typeclass, generic_typeclass)
                                    {
                                        return Err(Error::Typeclass(
                                            instance_typeclass.clone(),
                                            generic_typeclass.clone(),
                                        ));
                                    }
                                }
                                None => return Err(Error::Other),
                            }
                        }
                        _ => return Err(Error::Other),
                    }
                }
                self.mapping
                    .insert(param.name.clone(), instance_type.clone());
            }
            (AcornType::Function(f), AcornType::Function(g)) => {
                if f.arg_types.len() != g.arg_types.len() {
                    return Err(Error::Other);
                }
                self.match_instance(&f.return_type, &g.return_type, registry)?;
                for (f_arg_type, g_arg_type) in f.arg_types.iter().zip(&g.arg_types) {
                    self.match_instance(f_arg_type, g_arg_type, registry)?;
                }
            }
            (AcornType::Data(g_class, g_params), AcornType::Data(i_class, i_params)) => {
                if g_class != i_class || g_params.len() != i_params.len() {
                    return Err(Error::Other);
                }
                for (g_param, i_param) in g_params.iter().zip(i_params) {
                    self.match_instance(g_param, i_param, registry)?;
                }
            }
            _ => return require_eq(generic_type, instance_type),
        }
        Ok(())
    }
}

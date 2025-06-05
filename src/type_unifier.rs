use std::collections::HashMap;

use crate::acorn_type::{AcornType, Datatype, Typeclass};
use crate::acorn_value::AcornValue;
use crate::compilation::{self, ErrorSource};
use crate::module::ModuleId;
use crate::potential_value::PotentialValue;
use crate::unresolved_constant::UnresolvedConstant;

/// Utility for matching types during unification.
pub struct TypeUnifier<'a> {
    /// The registry tells us which classes are instances of which typeclasses,
    /// and which typeclasses have an extension relationship.
    registry: &'a dyn TypeclassRegistry,

    /// Type unification fills in a mapping for any parametric types that need to be specified,
    /// in order to make it match.
    /// Every parameter used in self will get a mapping entry.
    pub mapping: HashMap<String, AcornType>,
}

/// The different errors we can get from unification.
pub enum Error {
    /// Unification failed, because this datatype is not an instance of this typeclass.
    Datatype(Datatype, Typeclass),

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
    /// Returns whether the class is an instance of the typeclass.
    fn is_instance_of(&self, class: &Datatype, typeclass: &Typeclass) -> bool;

    /// Returns whether typeclass extends base.
    /// In particular, this returns false when typeclass == base.
    fn extends(&self, typeclass: &Typeclass, base: &Typeclass) -> bool;

    /// Returns whether this type has the attributes defined on the given entity.
    /// The entity name can be either a class or typeclass.
    fn inherits_attributes(&self, t: &AcornType, module_id: ModuleId, entity_name: &str) -> bool {
        match t {
            AcornType::Data(dt, _) => dt.module_id == module_id && dt.name == entity_name,
            AcornType::Variable(param) | AcornType::Arbitrary(param) => {
                let Some(param_tc) = &param.typeclass else {
                    return false;
                };
                if param_tc.module_id == module_id && param_tc.name == entity_name {
                    return true;
                }
                let typeclass = Typeclass {
                    module_id,
                    name: entity_name.to_string(),
                };
                self.extends(param_tc, &typeclass)
            }
            _ => false,
        }
    }
}

pub type Result = std::result::Result<(), Error>;

fn require_eq(t1: &AcornType, t2: &AcornType) -> Result {
    if t1 == t2 {
        Ok(())
    } else {
        Err(Error::Other)
    }
}

impl<'a> TypeUnifier<'a> {
    pub fn new(registry: &'a dyn TypeclassRegistry) -> Self {
        TypeUnifier {
            registry,
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
    ) -> Result {
        match (generic_type, instance_type) {
            (AcornType::Variable(param), _) => {
                if let Some(t) = self.mapping.get(&param.name) {
                    // This type variable is already mapped
                    return require_eq(t, instance_type);
                }
                if let Some(generic_typeclass) = param.typeclass.as_ref() {
                    match instance_type {
                        AcornType::Data(dt, _) => {
                            if !self.registry.is_instance_of(&dt, generic_typeclass) {
                                return Err(Error::Datatype(dt.clone(), generic_typeclass.clone()));
                            }
                        }
                        AcornType::Arbitrary(param) | AcornType::Variable(param) => {
                            match &param.typeclass {
                                Some(instance_typeclass) => {
                                    if instance_typeclass != generic_typeclass
                                        && !self
                                            .registry
                                            .extends(instance_typeclass, generic_typeclass)
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
                self.match_instance(&f.return_type, &g.return_type)?;
                for (f_arg_type, g_arg_type) in f.arg_types.iter().zip(&g.arg_types) {
                    self.match_instance(f_arg_type, g_arg_type)?;
                }
            }
            (AcornType::Data(g_class, g_params), AcornType::Data(i_class, i_params)) => {
                if g_class != i_class || g_params.len() != i_params.len() {
                    return Err(Error::Other);
                }
                for (g_param, i_param) in g_params.iter().zip(i_params) {
                    self.match_instance(g_param, i_param)?;
                }
            }
            _ => return require_eq(generic_type, instance_type),
        }
        Ok(())
    }

    /// Runs match_instance but wraps it with a human-readable error message when it fails.
    pub fn user_match_instance(
        &mut self,
        generic: &AcornType,
        instance: &AcornType,
        what: &str,
        source: &dyn ErrorSource,
    ) -> compilation::Result<()> {
        if !self.match_instance(generic, instance).is_ok() {
            return Err(source.error(&format!(
                "{} has type {} but we expected some sort of {}",
                what, instance, generic
            )));
        }
        Ok(())
    }

    /// Infer the type of an unresolved constant, based on its arguments (if it is a function)
    /// and the expected type.
    /// Returns a value that applies the function to the arguments.
    /// If the type cannot be inferred, returns an error.
    pub fn resolve_with_inference(
        &mut self,
        unresolved: UnresolvedConstant,
        args: Vec<AcornValue>,
        expected_return_type: Option<&AcornType>,
        source: &dyn ErrorSource,
    ) -> compilation::Result<AcornValue> {
        // Use the arguments to infer types
        let unresolved_return_type = if args.is_empty() {
            unresolved.generic_type.clone()
        } else if let AcornType::Function(unresolved_function_type) = &unresolved.generic_type {
            if unresolved_function_type.has_arbitrary() {
                return Err(source.error("unresolved function type has arbitrary"));
            }

            for (i, arg) in args.iter().enumerate() {
                if arg.has_generic() {
                    return Err(
                        source.error(&format!("argument {} ({}) has unresolved type", i, arg))
                    );
                }
                let arg_type: &AcornType = match &unresolved_function_type.arg_types.get(i) {
                    Some(t) => t,
                    None => {
                        return Err(source.error(&format!(
                            "expected {} arguments but got {}",
                            unresolved_function_type.arg_types.len(),
                            args.len()
                        )));
                    }
                };
                self.user_match_instance(
                    arg_type,
                    &arg.get_type(),
                    &format!("argument {}", i),
                    source,
                )?;
            }

            unresolved_function_type.applied_type(args.len())
        } else {
            return Err(source.error("expected a function type"));
        };

        if let Some(target_type) = expected_return_type {
            // Use the expected type to infer types
            self.user_match_instance(&unresolved_return_type, target_type, "return value", source)?;
        }

        // Determine the parameters for the instance
        let mut named_params = vec![];
        let mut instance_params = vec![];
        for param in &unresolved.params {
            match self.mapping.get(&param.name) {
                Some(t) => {
                    named_params.push((param.name.clone(), t.clone()));
                    instance_params.push(t.clone());
                }
                None => {
                    return Err(source.error(
                        "The arguments are insufficient to infer the type of this function. \
                        Try making its parameters explicit",
                    ));
                }
            }
        }

        // Resolve
        let instance_fn = unresolved.resolve(source, instance_params)?;
        let value = AcornValue::apply(instance_fn, args);
        value.check_type(expected_return_type, source)?;
        Ok(value)
    }

    /// If we have an expected type and this is still a potential value, resolve it.
    pub fn maybe_resolve_value(
        &mut self,
        potential: PotentialValue,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorSource,
    ) -> compilation::Result<PotentialValue> {
        let expected_type = match expected_type {
            Some(t) => t,
            None => return Ok(potential),
        };
        let uc = match potential {
            PotentialValue::Unresolved(uc) => uc,
            p => return Ok(p),
        };
        let value = self.resolve_with_inference(uc, vec![], Some(expected_type), source)?;
        Ok(PotentialValue::Resolved(value))
    }
}

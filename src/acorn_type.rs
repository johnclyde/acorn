use std::{collections::HashMap, fmt};

use crate::compilation::{ErrorSource, Result};
use crate::module::ModuleId;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct UnresolvedType {
    // The module where this type was defined in.
    pub module_id: ModuleId,

    // The name of this type.
    pub name: String,

    // How many parameters we need to instantiate this type.
    pub num_params: usize,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum PotentialType {
    // A usable type.
    Resolved(AcornType),

    // A generic type that we don't know the parameters for yet.
    // (module, name, number of parameters).
    Unresolved(UnresolvedType),
}

impl PotentialType {
    // Resolves the type given the parameters.
    // Reports an error if the parameters don't match what we expected.
    pub fn resolve(self, params: Vec<AcornType>, source: &dyn ErrorSource) -> Result<AcornType> {
        match self {
            PotentialType::Resolved(t) => {
                if !params.is_empty() {
                    Err(source.error("resolved type cannot take parameters"))
                } else {
                    Ok(t)
                }
            }
            PotentialType::Unresolved(ut) => {
                if params.len() != ut.num_params {
                    Err(source.error(&format!(
                        "type {} expects {} parameters, but got {}",
                        ut.name,
                        ut.num_params,
                        params.len()
                    )))
                } else {
                    Ok(AcornType::Data(ut.module_id, ut.name, params))
                }
            }
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct FunctionType {
    pub arg_types: Vec<AcornType>,
    pub return_type: Box<AcornType>,
}

impl fmt::Display for FunctionType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let lhs = if self.arg_types.len() == 1 {
            let arg_type = &self.arg_types[0];
            if arg_type.is_functional() {
                format!("({})", arg_type)
            } else {
                format!("{}", arg_type)
            }
        } else {
            format!("({})", AcornType::types_to_str(&self.arg_types))
        };
        write!(f, "{} -> {}", lhs, self.return_type)
    }
}

impl FunctionType {
    fn new(arg_types: Vec<AcornType>, return_type: AcornType) -> FunctionType {
        assert!(arg_types.len() > 0);
        if let AcornType::Function(ftype) = return_type {
            // Normalize function types by un-currying.
            let combined_args = arg_types
                .into_iter()
                .chain(ftype.arg_types.into_iter())
                .collect();
            FunctionType {
                arg_types: combined_args,
                return_type: ftype.return_type,
            }
        } else {
            FunctionType {
                arg_types,
                return_type: Box::new(return_type),
            }
        }
    }

    fn new_partial(&self, remove_args: usize) -> FunctionType {
        assert!(remove_args < self.arg_types.len());
        FunctionType {
            arg_types: self.arg_types[remove_args..].to_vec(),
            return_type: self.return_type.clone(),
        }
    }

    // The type after applying this function to a certain number of arguments.
    // Panics if the application is invalid.
    pub fn applied_type(&self, num_args: usize) -> AcornType {
        if num_args > self.arg_types.len() {
            panic!(
                "Can't apply function type {:?} taking {} args to {} args",
                self,
                self.arg_types.len(),
                num_args
            );
        }
        if num_args == self.arg_types.len() {
            *self.return_type.clone()
        } else {
            AcornType::Function(self.new_partial(num_args))
        }
    }

    pub fn has_arbitrary(&self) -> bool {
        self.arg_types.iter().any(|t| t.has_arbitrary()) || self.return_type.has_arbitrary()
    }
}

// Typeclasses are represented by the module they were defined in, and their name.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct TypeClass {
    pub module_id: ModuleId,
    pub name: String,
}

// Every AcornValue has an AcornType.
// This is the "richer" form of a type. The environment uses these types; the prover uses ids.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub enum AcornType {
    // Nothing can ever be the empty type.
    Empty,

    // Booleans are special
    Bool,

    // Data types are structures, inductive types, or axiomatic types.
    // There are three parts:
    // 1. The module they were defined in.
    // 2. The name of the type.
    // 3. The type parameters, if any.
    Data(ModuleId, String, Vec<AcornType>),

    // Function types are defined by their inputs and output.
    Function(FunctionType),

    // Type variables and arbitrary types are similar, but different.
    // Type variables are not monomorphic. Arbitrary types are monomorphic.
    // They do share the same namespace; you shouldn't have type variables and arbitrary types
    // inside the same type that have the same name.
    //
    // For example, in:
    //
    // theorem reverse_twice<T>(list: List<T>) {
    //     // Imagine some proof here.
    //     list.reverse.reverse = list
    // }
    //
    // To an external user of this theorem, T is a type variable. You can apply it to any type.
    // To use this theorem, we need to instantiate T to a concrete type, like Nat or Int.
    //
    // To the internal proof, T is an arbitrary type. It's fixed for the duration of the proof.
    // To prove this theorem, we *don't* need to instantiate T to a monomorphic type.

    // A type variable represents an unknown type, possibly belonging to a particular typeclass.
    // Expressions with type variables can be instantiated to particular types.
    Variable(String, Option<TypeClass>),

    // An arbitrary type represents a type that is (optionally) a fixed instance of a typeclass,
    // but we don't know anything else about it.
    Arbitrary(String, Option<TypeClass>),
}

impl AcornType {
    // Create the type, in non-curried form, for a function with the given arguments and return type.
    // arg_types can be empty.
    pub fn new_functional(arg_types: Vec<AcornType>, return_type: AcornType) -> AcornType {
        if arg_types.is_empty() {
            return_type
        } else {
            AcornType::Function(FunctionType::new(arg_types, return_type))
        }
    }

    // Whether this type contains the given type variable within it somewhere.
    pub fn has_type_variable(&self, name: &str) -> bool {
        match self {
            AcornType::Variable(vname, _) => vname == name,
            AcornType::Function(function_type) => {
                for arg_type in &function_type.arg_types {
                    if arg_type.has_type_variable(name) {
                        return true;
                    }
                }
                function_type.return_type.has_type_variable(name)
            }
            _ => false,
        }
    }

    // Create the type you get when you apply this type to the given type.
    // Panics if the application is invalid.
    // Does partial application.
    pub fn apply(&self, arg_type: &AcornType) -> AcornType {
        if let AcornType::Function(function_type) = self {
            assert_eq!(function_type.arg_types[0], *arg_type);
            function_type.applied_type(1)
        } else {
            panic!("Can't apply {:?} to {:?}", self, arg_type);
        }
    }

    pub fn types_to_str(types: &[AcornType]) -> String {
        let mut result = String::new();
        for (i, acorn_type) in types.iter().enumerate() {
            if i > 0 {
                result.push_str(", ");
            }
            result.push_str(&format!("{}", acorn_type));
        }
        result
    }

    pub fn decs_to_str(dec_types: &Vec<AcornType>, stack_size: usize) -> String {
        let mut result = String::new();
        for (i, dec_type) in dec_types.iter().enumerate() {
            if i > 0 {
                result.push_str(", ");
            }
            result.push_str(&format!("x{}: {}", i + stack_size, dec_type));
        }
        result
    }

    // Replaces type variables in the provided list with the corresponding type.
    pub fn instantiate(&self, params: &[(String, AcornType)]) -> AcornType {
        match self {
            AcornType::Variable(name, None) => {
                for (param_name, param_type) in params {
                    if name == param_name {
                        return param_type.clone();
                    }
                }
                self.clone()
            }
            AcornType::Function(function_type) => AcornType::new_functional(
                function_type
                    .arg_types
                    .iter()
                    .map(|t| t.instantiate(params))
                    .collect(),
                function_type.return_type.instantiate(params),
            ),
            _ => self.clone(),
        }
    }

    // Figures out whether it is possible to instantiate self to get instance.
    // Fills in a mapping for any parametric types that need to be specified, in order to make it match.
    // This will include "Foo" -> Parameter("Foo") mappings for types that should remain the same.
    // Every parameter used in self will get a mapping entry.
    // Returns whether it was successful.
    pub fn match_instance(
        &self,
        instance: &AcornType,
        mapping: &mut HashMap<String, AcornType>,
    ) -> bool {
        match (self, instance) {
            (AcornType::Variable(name, _), _) => {
                if let Some(t) = mapping.get(name) {
                    // This type variable is already mapped
                    return t == instance;
                }
                mapping.insert(name.clone(), instance.clone());
                true
            }
            (AcornType::Function(f), AcornType::Function(g)) => {
                if f.arg_types.len() != g.arg_types.len() {
                    return false;
                }
                if !f.return_type.match_instance(&g.return_type, mapping) {
                    return false;
                }
                for (f_arg_type, g_arg_type) in f.arg_types.iter().zip(&g.arg_types) {
                    if !f_arg_type.match_instance(g_arg_type, mapping) {
                        return false;
                    }
                }
                true
            }
            (
                AcornType::Data(g_module, g_name, g_params),
                AcornType::Data(i_module, i_name, i_params),
            ) => {
                if g_module != i_module || g_name != i_name || g_params.len() != i_params.len() {
                    return false;
                }
                for (g_param, i_param) in g_params.iter().zip(i_params) {
                    if !g_param.match_instance(i_param, mapping) {
                        return false;
                    }
                }
                true
            }
            _ => self == instance,
        }
    }

    // Converts all arbitrary types to type variables.
    pub fn to_generic(&self) -> AcornType {
        match self {
            AcornType::Arbitrary(name, tc) => AcornType::Variable(name.to_string(), tc.clone()),
            AcornType::Function(ftype) => AcornType::new_functional(
                ftype.arg_types.iter().map(|t| t.to_generic()).collect(),
                ftype.return_type.to_generic(),
            ),
            AcornType::Data(module, name, params) => AcornType::Data(
                *module,
                name.to_string(),
                params.iter().map(|t| t.to_generic()).collect(),
            ),
            _ => self.clone(),
        }
    }

    // A type is generic if it has any type variables within it.
    pub fn has_generic(&self) -> bool {
        match self {
            AcornType::Bool | AcornType::Empty | AcornType::Arbitrary(..) => false,
            AcornType::Variable(..) => true,
            AcornType::Data(_, _, types) => types.iter().any(|t| t.has_generic()),
            AcornType::Function(ftype) => {
                for arg_type in &ftype.arg_types {
                    if arg_type.has_generic() {
                        return true;
                    }
                }
                ftype.return_type.has_generic()
            }
        }
    }

    // Converts all type variables to arbitrary types.
    pub fn to_arbitrary(&self) -> AcornType {
        match self {
            AcornType::Variable(name, tc) => AcornType::Arbitrary(name.to_string(), tc.clone()),
            AcornType::Function(ftype) => AcornType::new_functional(
                ftype.arg_types.iter().map(|t| t.to_arbitrary()).collect(),
                ftype.return_type.to_arbitrary(),
            ),
            _ => self.clone(),
        }
    }

    pub fn has_arbitrary(&self) -> bool {
        match self {
            AcornType::Arbitrary(..) => true,
            AcornType::Function(ftype) => ftype.has_arbitrary(),
            AcornType::Data(_, _, params) => params.iter().any(|t| t.has_arbitrary()),
            _ => false,
        }
    }

    pub fn is_functional(&self) -> bool {
        match self {
            AcornType::Function(_) => true,
            _ => false,
        }
    }
}

impl fmt::Display for AcornType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AcornType::Bool => write!(f, "Bool"),
            AcornType::Data(_, name, params) => {
                write!(f, "{}", name)?;
                if !params.is_empty() {
                    write!(f, "<{}>", AcornType::types_to_str(params))?;
                }
                Ok(())
            }
            AcornType::Function(function_type) => write!(f, "{}", function_type),
            AcornType::Empty => write!(f, "empty"),
            AcornType::Variable(name, tc) | AcornType::Arbitrary(name, tc) => {
                write!(f, "{}", name)?;
                if let Some(tc) = tc {
                    write!(f, ": {}", tc.name)?;
                }
                Ok(())
            }
        }
    }
}

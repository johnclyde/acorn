use std::{collections::HashMap, fmt};

use crate::compilation::{ErrorSource, Result};
use crate::module::ModuleId;

// Classes are represented by the module they were defined in, and their name.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct Class {
    pub module_id: ModuleId,
    pub name: String,
}

// Typeclasses are represented by the module they were defined in, and their name.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct Typeclass {
    pub module_id: ModuleId,
    pub name: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct UnresolvedType {
    // The underlying generic type.
    pub class: Class,

    // The parameters we need to instantiate this type, along with their typeclass if any..
    pub params: Vec<Option<Typeclass>>,
}

impl UnresolvedType {
    // Just sticks fake names in there to print.
    pub fn to_display_type(&self) -> AcornType {
        let mut params = vec![];
        for (i, param) in self.params.iter().enumerate() {
            params.push(AcornType::Variable(TypeParam {
                name: format!("T{}", i),
                typeclass: param.clone(),
            }));
        }
        AcornType::Data(self.class.clone(), params)
    }
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
    // Every replacement must be a type variable being replaced with an arbitrary type.
    pub fn invertible_resolve(
        self,
        params: Vec<AcornType>,
        source: &dyn ErrorSource,
    ) -> Result<AcornType> {
        if let PotentialType::Unresolved(ut) = &self {
            if ut.params.len() != params.len() {
                return Err(source.error(&format!(
                    "type {} expects {} parameters, but got {}",
                    ut.class.name,
                    ut.params.len(),
                    params.len()
                )));
            }
            for (i, (typeclass, param_type)) in ut.params.iter().zip(params.iter()).enumerate() {
                match param_type {
                    AcornType::Arbitrary(param) => {
                        if typeclass != &param.typeclass {
                            return Err(source.error(&format!(
                                "expected param {} to have typeclass {:?}, but got {:?}",
                                i, typeclass, param.typeclass
                            )));
                        }
                    }
                    _ => {
                        // Can this even happen?
                        return Err(source.error("bad parameter syntax"));
                    }
                }
            }
        }
        self.resolve(params, source)
    }

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
                if params.len() != ut.params.len() {
                    Err(source.error(&format!(
                        "type {} expects {} parameters, but got {}",
                        ut.class.name,
                        ut.params.len(),
                        params.len()
                    )))
                } else {
                    // TODO: check that params obeys ut's typeclasses
                    Ok(AcornType::Data(ut.class, params))
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

    // Makes a partial type by removing the first n arguments.
    fn remove_args(&self, n: usize) -> FunctionType {
        assert!(n < self.arg_types.len());
        FunctionType {
            arg_types: self.arg_types[n..].to_vec(),
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
            AcornType::Function(self.remove_args(num_args))
        }
    }

    pub fn has_arbitrary(&self) -> bool {
        self.arg_types.iter().any(|t| t.has_arbitrary()) || self.return_type.has_arbitrary()
    }
}

/// A type parameter is a way of naming a type by its properties.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct TypeParam {
    pub name: String,
    pub typeclass: Option<Typeclass>,
}

impl fmt::Display for TypeParam {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(tc) = &self.typeclass {
            write!(f, "{}: {}", self.name, tc.name)
        } else {
            write!(f, "{}", self.name)
        }
    }
}

impl TypeParam {
    pub fn params_to_str(params: &[TypeParam]) -> String {
        let mut result = "<".to_string();
        for (i, param) in params.iter().enumerate() {
            if i > 0 {
                result.push_str(", ");
            }
            result.push_str(&format!("{}", param));
        }
        result.push('>');
        result
    }
}

/// Every AcornValue has an AcornType.
/// This is the "richer" form of a type. The environment uses these types; the prover uses ids.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub enum AcornType {
    /// Nothing can ever be the empty type.
    Empty,

    /// Booleans are special
    Bool,

    /// Data types are structures, inductive types, or axiomatic types.
    /// They have a class, and may have type parameters.
    Data(Class, Vec<AcornType>),

    /// Function types are defined by their inputs and output.
    Function(FunctionType),

    /// Type variables and arbitrary types are similar, but different.
    /// Type variables are not monomorphic. Arbitrary types are monomorphic.
    /// They do share the same namespace; you shouldn't have type variables and arbitrary types
    /// inside the same type that have the same name.
    ///
    /// For example, in:
    ///
    /// ```acorn
    /// theorem reverse_twice<T>(list: List<T>) {
    ///     // Imagine some proof here.
    ///     list.reverse.reverse = list
    /// }
    /// ```
    ///
    /// To an external user of this theorem, T is a type variable. You can apply it to any type.
    /// To use this theorem, we need to instantiate T to a concrete type, like Nat or Int.
    ///
    /// To the internal proof, T is an arbitrary type. It's fixed for the duration of the proof.
    /// To prove this theorem, we *don't* need to instantiate T to a monomorphic type.
    ///
    /// A type variable represents an unknown type, possibly belonging to a particular typeclass.
    /// Expressions with type variables can be instantiated to particular types.
    Variable(TypeParam),

    /// An arbitrary type represents a type that is (optionally) a fixed instance of a typeclass,
    /// but we don't know anything else about it.
    Arbitrary(TypeParam),
}

impl AcornType {
    /// This just checks exact equality, without any generic stuff.
    pub fn check_eq(&self, source: &dyn ErrorSource, expected: Option<&AcornType>) -> Result<()> {
        if let Some(e) = expected {
            if e != self {
                return Err(source.error(&format!("expected type {}, but this is {}", e, self)));
            }
        }
        Ok(())
    }

    /// Create the type, in non-curried form, for a function with the given arguments and return type.
    /// arg_types can be empty.
    pub fn functional(arg_types: Vec<AcornType>, return_type: AcornType) -> AcornType {
        if arg_types.is_empty() {
            return_type
        } else {
            AcornType::Function(FunctionType::new(arg_types, return_type))
        }
    }

    /// Whether this type contains the given type variable within it somewhere.
    pub fn has_type_variable(&self, name: &str) -> bool {
        match self {
            AcornType::Variable(param) => param.name == name,
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

    /// Create the type you get when you apply this type to the given type.
    /// Panics if the application is invalid.
    /// Does partial application.
    pub fn apply(&self, arg_type: &AcornType) -> AcornType {
        if let AcornType::Function(function_type) = self {
            assert_eq!(function_type.arg_types[0], *arg_type);
            function_type.applied_type(1)
        } else {
            panic!("Can't apply {:?} to {:?}", self, arg_type);
        }
    }

    fn types_to_str(types: &[AcornType]) -> String {
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
    // Note that this does not check if typeclasses match.
    pub fn instantiate(&self, params: &[(String, AcornType)]) -> AcornType {
        match self {
            AcornType::Variable(param) => {
                for (param_name, param_type) in params {
                    if &param.name == param_name {
                        return param_type.clone();
                    }
                }
                self.clone()
            }
            AcornType::Function(function_type) => AcornType::functional(
                function_type
                    .arg_types
                    .iter()
                    .map(|t| t.instantiate(params))
                    .collect(),
                function_type.return_type.instantiate(params),
            ),
            AcornType::Data(class, types) => AcornType::Data(
                class.clone(),
                types.iter().map(|t| t.instantiate(params)).collect(),
            ),
            _ => self.clone(),
        }
    }

    // Figures out whether it is possible to instantiate self to get instance.
    //
    // Fills in a mapping for any parametric types that need to be specified, in order to make it match.
    // This will include "Foo" -> Parameter("Foo") mappings for types that should remain the same.
    // Every parameter used in self will get a mapping entry.
    //
    // "validator" is a function that checks whether a typeclass is valid for a given type.
    // This is abstracted out because the prover and the compiler have different ideas of what is valid.
    //
    // Returns whether it was successful.
    pub fn match_instance(
        &self,
        instance: &AcornType,
        validator: &mut dyn FnMut(&Class, &Typeclass) -> bool,
        mapping: &mut HashMap<String, AcornType>,
    ) -> bool {
        match (self, instance) {
            (AcornType::Variable(param), _) => {
                if let Some(t) = mapping.get(&param.name) {
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
                mapping.insert(param.name.clone(), instance.clone());
                true
            }
            (AcornType::Function(f), AcornType::Function(g)) => {
                if f.arg_types.len() != g.arg_types.len() {
                    return false;
                }
                if !f
                    .return_type
                    .match_instance(&g.return_type, validator, mapping)
                {
                    return false;
                }
                for (f_arg_type, g_arg_type) in f.arg_types.iter().zip(&g.arg_types) {
                    if !f_arg_type.match_instance(g_arg_type, validator, mapping) {
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
                    if !g_param.match_instance(i_param, validator, mapping) {
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
            AcornType::Arbitrary(param) => AcornType::Variable(param.clone()),
            AcornType::Function(ftype) => AcornType::functional(
                ftype.arg_types.iter().map(|t| t.to_generic()).collect(),
                ftype.return_type.to_generic(),
            ),
            AcornType::Data(class, params) => AcornType::Data(
                class.clone(),
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
            AcornType::Data(_, types) => types.iter().any(|t| t.has_generic()),
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
            AcornType::Variable(param) => AcornType::Arbitrary(param.clone()),
            AcornType::Function(ftype) => AcornType::functional(
                ftype.arg_types.iter().map(|t| t.to_arbitrary()).collect(),
                ftype.return_type.to_arbitrary(),
            ),
            AcornType::Data(class, params) => AcornType::Data(
                class.clone(),
                params.iter().map(|t| t.to_arbitrary()).collect(),
            ),
            _ => self.clone(),
        }
    }

    pub fn has_arbitrary(&self) -> bool {
        match self {
            AcornType::Arbitrary(..) => true,
            AcornType::Function(ftype) => ftype.has_arbitrary(),
            AcornType::Data(_, params) => params.iter().any(|t| t.has_arbitrary()),
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
            AcornType::Data(class, params) => {
                write!(f, "{}", class.name)?;
                if !params.is_empty() {
                    write!(f, "<{}>", AcornType::types_to_str(params))?;
                }
                Ok(())
            }
            AcornType::Function(function_type) => write!(f, "{}", function_type),
            AcornType::Empty => write!(f, "empty"),
            AcornType::Variable(param) | AcornType::Arbitrary(param) => {
                write!(f, "{}", param.name)?;
                Ok(())
            }
        }
    }
}

use std::fmt;

use crate::acorn_type::{Class, Typeclass};
use crate::module::ModuleId;

/// The LocalName provides an identifier for a constant that is unique within its module.
#[derive(Debug, Eq, PartialEq, Clone, Hash, PartialOrd, Ord)]
pub enum LocalName {
    /// An unqualified name has no dots.
    Unqualified(String),

    /// An attribute can either be of a class or a typeclass.
    /// The first string is the class or typeclass name, defined in this module.
    /// The second string is the attribute name.
    Attribute(String, String),
}

impl fmt::Display for LocalName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LocalName::Unqualified(name) => write!(f, "{}", name),
            LocalName::Attribute(class, attr) => write!(f, "{}.{}", class, attr),
        }
    }
}

impl LocalName {
    pub fn unqualified(name: &str) -> LocalName {
        LocalName::Unqualified(name.to_string())
    }

    pub fn attribute(class: &str, attr: &str) -> LocalName {
        LocalName::Attribute(class.to_string(), attr.to_string())
    }

    /// Just use this for testing.
    pub fn guess(s: &str) -> LocalName {
        if s.contains('.') {
            let parts: Vec<&str> = s.split('.').collect();
            if parts.len() == 2 {
                LocalName::Attribute(parts[0].to_string(), parts[1].to_string())
            } else {
                panic!("Unguessable name format: {}", s);
            }
        } else {
            LocalName::Unqualified(s.to_string())
        }
    }

    pub fn to_defined(self) -> OldDefinedName {
        OldDefinedName::Local(self)
    }

    /// Return this constant's name as a chain of strings, if that's possible.
    pub fn name_chain(&self) -> Option<Vec<&str>> {
        match self {
            LocalName::Unqualified(name) => Some(vec![name]),
            LocalName::Attribute(class, attr) => Some(vec![class, attr]),
        }
    }

    pub fn is_attribute_of(&self, receiver: &str) -> bool {
        match self {
            LocalName::Unqualified(_) => false,
            LocalName::Attribute(r, _) => r == receiver,
        }
    }
}

/// An instance name is something like Ring.add<Int>.
/// This can be defined directly, although it should be expressed in
/// parametrized form when it's a value.
#[derive(Hash, Debug, Eq, PartialEq, Clone, PartialOrd, Ord)]
pub struct InstanceName {
    /// Like "Ring", in Ring.add<Int>.
    pub typeclass: Typeclass,

    /// Like "add", in Ring.add<Int>.
    pub attribute: String,

    /// Like "Int", in Ring.add<Int>.
    pub class: Class,
}

impl fmt::Display for InstanceName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}.{}<{}>",
            self.typeclass.name, self.attribute, self.class.name
        )
    }
}

/// The OldDefinedName describes how a constant, type, or typeclass was defined.
/// It doesn't work correctly with mixins, because it doesn't differentiate between
/// the place where the class was defined, and the place where the attribute was defined.
#[derive(Hash, Debug, Eq, PartialEq, Clone, PartialOrd, Ord)]
pub enum OldDefinedName {
    /// A regular local name.
    Local(LocalName),

    /// An attribute defined via an instance statement.
    Instance(InstanceName),
}

impl fmt::Display for OldDefinedName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            OldDefinedName::Local(name) => write!(f, "{}", name),
            OldDefinedName::Instance(name) => write!(f, "{}", name),
        }
    }
}

impl OldDefinedName {
    pub fn unqualified(name: &str) -> OldDefinedName {
        OldDefinedName::Local(LocalName::Unqualified(name.to_string()))
    }

    pub fn attribute(class: &str, attr: &str) -> OldDefinedName {
        OldDefinedName::Local(LocalName::Attribute(class.to_string(), attr.to_string()))
    }

    pub fn instance(tc: Typeclass, attr: &str, class: Class) -> OldDefinedName {
        let inst = InstanceName {
            typeclass: tc,
            attribute: attr.to_string(),
            class,
        };
        OldDefinedName::Instance(inst)
    }

    pub fn is_qualified(&self) -> bool {
        match self {
            OldDefinedName::Local(LocalName::Unqualified(_)) => false,
            _ => true,
        }
    }

    pub fn is_instance(&self) -> bool {
        match self {
            OldDefinedName::Instance(..) => true,
            _ => false,
        }
    }

    pub fn as_attribute(&self) -> Option<(&str, &str)> {
        match self {
            OldDefinedName::Local(LocalName::Attribute(class, attr)) => Some((class, attr)),
            _ => None,
        }
    }

    pub fn matches_instance(&self, typeclass: &Typeclass, class: &Class) -> bool {
        match self {
            OldDefinedName::Instance(inst) => inst.typeclass == *typeclass && inst.class == *class,
            OldDefinedName::Local(_) => false,
        }
    }

    pub fn as_local(&self) -> Option<&LocalName> {
        match self {
            OldDefinedName::Local(name) => Some(name),
            OldDefinedName::Instance(..) => None,
        }
    }

    /// Just use this for testing.
    pub fn guess(s: &str) -> OldDefinedName {
        OldDefinedName::Local(LocalName::guess(s))
    }
}

/// The GlobalName provides a globally unique identifier for a constant.
/// It doesn't work correctly with mixins, because it doesn't differentiate between
/// the place where the class was defined, and the place where the attribute was defined.
#[derive(Debug, Eq, PartialEq, Clone, Hash, PartialOrd, Ord)]
pub struct GlobalName {
    pub module_id: ModuleId,
    pub local_name: LocalName,
}

impl GlobalName {
    pub fn new(module_id: ModuleId, local_name: LocalName) -> GlobalName {
        GlobalName {
            module_id,
            local_name,
        }
    }

    /// Only use this for testing.
    pub fn guess(module_id: ModuleId, s: &str) -> GlobalName {
        GlobalName {
            module_id,
            local_name: LocalName::guess(s),
        }
    }

    /// If this value is a dotted attribute of a class or typeclass, return:
    ///   (module id, receiver name, attribute name)
    pub fn as_attribute(&self) -> Option<(ModuleId, &str, &str)> {
        if let LocalName::Attribute(receiver, member) = &self.local_name {
            Some((self.module_id, receiver, member))
        } else {
            None
        }
    }

    pub fn is_attribute_of(&self, class: &Class) -> bool {
        self.module_id == class.module_id && self.local_name.is_attribute_of(&class.name)
    }
}

/// The ConstantName provides an identifier for a constant.
/// It is unique within a given scope. It is not necessarily globally unique, because you
/// could have two different modules mix the same attribute into a class or typeclass, or
/// you could have a stack variable with the same name in two different places.
#[derive(Debug, Eq, PartialEq, Clone, Hash, PartialOrd, Ord)]
pub enum ConstantName {
    /// An attribute of a class.
    ClassAttribute(Class, String),

    /// An attribute of a typeclass.
    TypeclassAttribute(Typeclass, String),

    /// A name for a constant that is not an attribute.
    Unqualified(ModuleId, String),
}

impl ConstantName {
    pub fn class_attr(class: Class, attr: &str) -> ConstantName {
        ConstantName::ClassAttribute(class, attr.to_string())
    }

    pub fn typeclass_attr(tc: Typeclass, attr: &str) -> ConstantName {
        ConstantName::TypeclassAttribute(tc, attr.to_string())
    }

    pub fn unqualified(module_id: ModuleId, name: &str) -> ConstantName {
        ConstantName::Unqualified(module_id, name.to_string())
    }

    pub fn as_attribute(&self) -> Option<(ModuleId, &str, &str)> {
        match self {
            ConstantName::ClassAttribute(class, attr) => Some((class.module_id, &class.name, attr)),
            ConstantName::TypeclassAttribute(tc, attr) => Some((tc.module_id, &tc.name, attr)),
            ConstantName::Unqualified(..) => None,
        }
    }

    pub fn to_global_name(&self) -> GlobalName {
        match self {
            ConstantName::ClassAttribute(class, attr) => {
                GlobalName::new(class.module_id, LocalName::attribute(&class.name, attr))
            }
            ConstantName::TypeclassAttribute(tc, attr) => {
                GlobalName::new(tc.module_id, LocalName::attribute(&tc.name, attr))
            }
            ConstantName::Unqualified(module_id, name) => {
                GlobalName::new(*module_id, LocalName::unqualified(name))
            }
        }
    }
}

impl fmt::Display for ConstantName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ConstantName::ClassAttribute(class, attr) => {
                write!(f, "{}.{}", class.name, attr)
            }
            ConstantName::TypeclassAttribute(tc, attr) => {
                write!(f, "{}.{}", tc.name, attr)
            }
            ConstantName::Unqualified(_, name) => write!(f, "{}", name),
        }
    }
}

// For migrating from GlobalName to ConstantName.
#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct NameShim(GlobalName);

impl NameShim {
    pub fn class_attr(class: Class, attr: &str) -> NameShim {
        NameShim(GlobalName::new(
            class.module_id,
            LocalName::attribute(&class.name, attr),
        ))
    }

    pub fn typeclass_attr(tc: Typeclass, attr: &str) -> NameShim {
        NameShim(GlobalName::new(
            tc.module_id,
            LocalName::attribute(&tc.name, attr),
        ))
    }

    pub fn unqualified(module_id: ModuleId, name: &str) -> NameShim {
        NameShim(GlobalName::new(module_id, LocalName::unqualified(name)))
    }

    /// TODO: deprecate and remove.
    pub fn new(global_name: GlobalName) -> NameShim {
        NameShim(global_name)
    }

    /// TODO: deprecate and remove.
    pub fn to_global_name(&self) -> GlobalName {
        self.0.clone()
    }

    pub fn as_attribute(&self) -> Option<(ModuleId, &str, &str)> {
        self.0.as_attribute()
    }

    /// TODO: deprecate and remove.
    pub fn as_global_name(&self) -> &GlobalName {
        &self.0
    }

    pub fn module_id(&self) -> ModuleId {
        self.0.module_id
    }
}

/// The DefinedName describes how a constant was defined.
#[derive(Hash, Debug, Eq, PartialEq, Clone, PartialOrd, Ord)]
pub enum DefinedName {
    /// A regular constant name.
    Constant(ConstantName),

    /// An attribute defined via an instance statement.
    Instance(InstanceName),
}

impl fmt::Display for DefinedName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DefinedName::Constant(name) => write!(f, "{}", name),
            DefinedName::Instance(name) => write!(f, "{}", name),
        }
    }
}

impl DefinedName {
    pub fn unqualified(module_id: ModuleId, name: &str) -> DefinedName {
        DefinedName::Constant(ConstantName::unqualified(module_id, name))
    }

    pub fn attribute(class: &Class, attr: &str) -> DefinedName {
        DefinedName::Constant(ConstantName::class_attr(class.clone(), attr))
    }

    pub fn instance(tc: Typeclass, attr: &str, class: Class) -> DefinedName {
        let inst = InstanceName {
            typeclass: tc,
            attribute: attr.to_string(),
            class,
        };
        DefinedName::Instance(inst)
    }

    pub fn is_qualified(&self) -> bool {
        match self {
            DefinedName::Constant(ConstantName::Unqualified(..)) => false,
            _ => true,
        }
    }

    pub fn is_instance(&self) -> bool {
        match self {
            DefinedName::Instance(..) => true,
            _ => false,
        }
    }

    pub fn as_attribute(&self) -> Option<(&str, &str)> {
        match self {
            DefinedName::Constant(c) => {
                let (_, entity, attr) = c.as_attribute()?;
                Some((entity, attr))
            }
            _ => None,
        }
    }

    pub fn matches_instance(&self, typeclass: &Typeclass, class: &Class) -> bool {
        match self {
            DefinedName::Instance(inst) => inst.typeclass == *typeclass && inst.class == *class,
            DefinedName::Constant(_) => false,
        }
    }
}

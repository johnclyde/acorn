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

    pub fn to_defined(self) -> DefinedName {
        DefinedName::Local(self)
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

/// The DefinedName describes how a constant, type, or typeclass was defined.
#[derive(Hash, Debug, Eq, PartialEq, Clone, PartialOrd, Ord)]
pub enum DefinedName {
    /// A regular local name.
    Local(LocalName),

    /// An attribute defined via an instance statement.
    Instance(InstanceName),
}

impl fmt::Display for DefinedName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DefinedName::Local(name) => write!(f, "{}", name),
            DefinedName::Instance(name) => write!(f, "{}", name),
        }
    }
}

impl DefinedName {
    pub fn unqualified(name: &str) -> DefinedName {
        DefinedName::Local(LocalName::Unqualified(name.to_string()))
    }

    pub fn attribute(class: &str, attr: &str) -> DefinedName {
        DefinedName::Local(LocalName::Attribute(class.to_string(), attr.to_string()))
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
            DefinedName::Local(LocalName::Unqualified(_)) => false,
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
            DefinedName::Local(LocalName::Attribute(class, attr)) => Some((class, attr)),
            _ => None,
        }
    }

    pub fn matches_instance(&self, typeclass: &Typeclass, class: &Class) -> bool {
        match self {
            DefinedName::Instance(inst) => inst.typeclass == *typeclass && inst.class == *class,
            DefinedName::Local(_) => false,
        }
    }

    pub fn as_local(&self) -> Option<&LocalName> {
        match self {
            DefinedName::Local(name) => Some(name),
            DefinedName::Instance(..) => None,
        }
    }

    /// Just use this for testing.
    pub fn guess(s: &str) -> DefinedName {
        DefinedName::Local(LocalName::guess(s))
    }
}

/// The GlobalName provides a globally unique identifier for a constant.
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

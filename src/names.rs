use std::{fmt, vec};

use crate::acorn_type::Typeclass;
use crate::module::ModuleId;

// The LocalName describes how a constant, type, or typeclass is named in the module that defines it.
#[derive(Hash, Debug, Eq, PartialEq, Clone, PartialOrd, Ord)]
pub enum LocalName {
    // An unqualified name has no dots.
    Unqualified(String),

    // An attribute can either be of a class or a typeclass.
    // The first string is the class or typeclass name, defined in this module.
    // The second string is the attribute name.
    Attribute(String, String),

    // An instance name is like Ring.add<Int>.
    // The typeclass doesn't have to be defined here.
    // The first string is the attribute name.
    // The second string is the name of the instance class, which has to be defined in this module.
    Instance(Typeclass, String, String),
}

impl fmt::Display for LocalName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LocalName::Unqualified(name) => write!(f, "{}", name),
            LocalName::Attribute(class, attr) => write!(f, "{}.{}", class, attr),
            LocalName::Instance(tc, attr, class) => {
                write!(f, "{}.{}<{}>", tc.name, attr, class)
            }
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

    pub fn instance(tc: &Typeclass, attr: &str, class: &str) -> LocalName {
        LocalName::Instance(tc.clone(), attr.to_string(), class.to_string())
    }

    pub fn is_qualified(&self) -> bool {
        match self {
            LocalName::Unqualified(_) => false,
            _ => true,
        }
    }

    pub fn as_attribute(&self) -> Option<(&str, &str)> {
        match self {
            LocalName::Attribute(class, attr) => Some((class, attr)),
            _ => None,
        }
    }

    // Return this constant's name as a chain of strings, if that's possible.
    pub fn name_chain(&self) -> Option<Vec<&str>> {
        match self {
            LocalName::Unqualified(name) => Some(vec![name]),
            LocalName::Attribute(class, attr) => Some(vec![class, attr]),
            LocalName::Instance(..) => None,
        }
    }

    // Just use this for testing.
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
}

// The GlobalName provides a globally unique identifier for a constant.
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

    // Only use this for testing.
    pub fn guess(module_id: ModuleId, s: &str) -> GlobalName {
        GlobalName {
            module_id,
            local_name: LocalName::guess(s),
        }
    }
}

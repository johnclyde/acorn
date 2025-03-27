use std::fmt;

use crate::acorn_type::Typeclass;
use crate::module::ModuleId;

// The LocalName describes how a constant is named in the module that defines it.
#[derive(Hash, Debug, Eq, PartialEq, Clone)]
pub enum LocalConstantName {
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

impl fmt::Display for LocalConstantName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LocalConstantName::Unqualified(name) => write!(f, "{}", name),
            LocalConstantName::Attribute(class, attr) => write!(f, "{}.{}", class, attr),
            LocalConstantName::Instance(tc, attr, class) => {
                // TODO: Stop using this double-dot syntax.
                write!(f, "{}.{}.{}", class, &tc.name, attr)
            }
        }
    }
}

impl LocalConstantName {
    pub fn unqualified(name: &str) -> LocalConstantName {
        LocalConstantName::Unqualified(name.to_string())
    }

    pub fn attribute(class: &str, attr: &str) -> LocalConstantName {
        LocalConstantName::Attribute(class.to_string(), attr.to_string())
    }

    pub fn instance(tc: &Typeclass, attr: &str, class: &str) -> LocalConstantName {
        LocalConstantName::Instance(tc.clone(), attr.to_string(), class.to_string())
    }
}

// The GlobalName provides a globally unique identifier for a constant.
pub struct GlobalConstantName {
    pub module_id: ModuleId,
    pub local_name: LocalConstantName,
}

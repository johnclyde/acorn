use std::collections::HashSet;
use std::fmt;

use crate::acorn_type::{AcornType, Datatype, Typeclass};
use crate::acorn_value::{AcornValue, ConstantInstance};
use crate::names::ConstantName;
use crate::potential_value::PotentialValue;
use crate::proposition::Proposition;
use crate::source::Source;

/// A fact is a statement that we are assuming to be true in a particular context.
#[derive(Clone, Debug)]
pub enum Fact {
    /// A true statement representable as a boolean value.
    Proposition(Proposition),

    /// The first typeclass extends this set of typeclasses.
    Extends(Typeclass, HashSet<Typeclass>, Source),

    /// The fact that this class is an instance of this typeclass.
    Instance(Datatype, Typeclass, Source),

    /// A defined constant.
    /// The tuple is the name of the constant, the definition, and the source.
    /// Can be generic or not, depending on the potential value.
    Definition(PotentialValue, AcornValue, Source),
}

impl fmt::Display for Fact {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Fact::Proposition(p) => write!(f, "prop: {}", p.source.description()),
            Fact::Extends(tc, base_set, _) => {
                if base_set.is_empty() {
                    write!(f, "{} extends nothing", tc.name)
                } else {
                    let mut names: Vec<String> = base_set.iter().map(|t| t.name.clone()).collect();
                    names.sort();
                    write!(f, "{} extends {}", tc.name, names.join(", "))
                }
            }
            Fact::Instance(class, typeclass, _) => {
                write!(f, "{} is an instance of {}", class.name, typeclass.name)
            }
            Fact::Definition(_, _, source) => write!(f, "{}", source.description()),
        }
    }
}

impl Fact {
    pub fn proposition(value: AcornValue, source: Source) -> Fact {
        Fact::Proposition(Proposition::monomorphic(value, source))
    }

    pub fn source(&self) -> &Source {
        match self {
            Fact::Proposition(p) => &p.source,
            Fact::Extends(_, _, source) => source,
            Fact::Instance(_, _, source) => source,
            Fact::Definition(_, _, source) => source,
        }
    }

    /// A fact that is used is normalization means that we still need it, even if it isn't used by
    /// the prover.
    pub fn used_in_normalization(&self) -> bool {
        match self {
            Fact::Instance(..) => true,
            Fact::Extends(..) => true,
            _ => self.as_instance_alias().is_some(),
        }
    }

    /// Returns Some(..) if this fact is an aliasing for an instance of a typeclass constant.
    /// I.e., it's part of an instance statement with "let _ = _" so that it's an alias of a previously
    /// defined constant.
    pub fn as_instance_alias(&self) -> Option<(ConstantInstance, &ConstantName, AcornType)> {
        if let Fact::Definition(potential, definition, _) = self {
            if let PotentialValue::Resolved(AcornValue::Constant(ci)) = potential {
                if let Some(name) = definition.as_simple_constant() {
                    return Some((ci.clone(), name, definition.get_type()));
                }
            }
        }
        None
    }
}

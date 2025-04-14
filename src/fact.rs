use crate::acorn_type::{Class, Typeclass};
use crate::acorn_value::AcornValue;
use crate::potential_value::PotentialValue;
use crate::proposition::Proposition;
use crate::source::Source;

// A fact is a statement that we are assuming to be true in a particular context.
#[derive(Clone, Debug)]
pub enum Fact {
    // A true statement representable as a boolean value.
    Proposition(Proposition),

    // The fact that this class is an instance of this typeclass.
    Instance(Class, Typeclass, Source),

    /// A defined constant.
    /// The tuple is the name of the constant, the definition, and the source.
    /// Can be generic or not, depending on the potential value.
    Definition(PotentialValue, AcornValue, Source),
}

impl Fact {
    pub fn proposition(value: AcornValue, source: Source) -> Fact {
        Fact::Proposition(Proposition::monomorphic(value, source))
    }

    pub fn source(&self) -> &Source {
        match self {
            Fact::Proposition(p) => &p.source,
            Fact::Instance(_, _, source) => source,
            Fact::Definition(_, _, source) => source,
        }
    }

    pub fn is_instance(&self) -> bool {
        match self {
            Fact::Instance(..) => true,
            _ => false,
        }
    }
}

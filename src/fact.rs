use crate::acorn_type::{Class, Typeclass};
use crate::proposition::{Proposition, Source};

// A fact is a statement that we are assuming to be true in a particular context.
#[derive(Clone, Debug)]
pub enum Fact {
    // A true statement representable as a boolean value.
    Proposition(Proposition),

    // The fact that this class is an instance of this typeclass.
    Instance(Class, Typeclass, Source),
}

impl Fact {
    pub fn source(&self) -> &Source {
        match self {
            Fact::Proposition(p) => &p.source,
            Fact::Instance(_, _, source) => source,
        }
    }

    pub fn is_instance(&self) -> bool {
        match self {
            Fact::Proposition(_) => false,
            Fact::Instance(..) => true,
        }
    }
}

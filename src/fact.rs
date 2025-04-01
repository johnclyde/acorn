use crate::acorn_type::{Class, Typeclass};
use crate::proposition::Proposition;

// A fact is a statement that we are assuming to be true in a particular context.
#[derive(Clone, Debug)]
pub enum Fact {
    // A true statement about boolean values.
    Proposition(Proposition),

    // The fact that this class is an instance of this typeclass.
    InstanceOf(Class, Typeclass),
}

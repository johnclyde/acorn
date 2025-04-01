use crate::proof_step::Truthiness;
use crate::proposition::Proposition;

// A fact is a statement that we are assuming to be true in a particular context.
#[derive(Clone, Debug)]
pub enum Fact {
    // A true statement, plus a tag for what sort of true it is.
    Proposition(Proposition, Truthiness),
}

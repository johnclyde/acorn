use crate::proof_step::Truthiness;
use crate::proposition::Proposition;

// A fact is a proposition that we already know to be true.
#[derive(Clone, Debug)]
pub struct Fact {
    pub proposition: Proposition,
    pub truthiness: Truthiness,
}

impl Fact {
    pub fn new(proposition: Proposition, truthiness: Truthiness) -> Fact {
        Fact {
            proposition,
            truthiness,
        }
    }
}

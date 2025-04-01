use crate::acorn_type::AcornType;
use crate::proof_step::Truthiness;
use crate::proposition::{Proposition, Source, SourceType};

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

    // Instantiates a generic fact.
    pub fn instantiate(&self, params: &[(String, AcornType)]) -> Fact {
        let value = self.proposition.value.instantiate(params);
        if value.has_generic() {
            panic!("tried to instantiate but {} is still generic", value);
        }
        let source = match &self.proposition.source.source_type {
            SourceType::ConstantDefinition(v, name) => {
                let new_type = SourceType::ConstantDefinition(v.instantiate(params), name.clone());
                Source {
                    module: self.proposition.source.module,
                    range: self.proposition.source.range.clone(),
                    source_type: new_type,
                    importable: self.proposition.source.importable,
                }
            }
            _ => self.proposition.source.clone(),
        };
        let proposition = Proposition { value, source };
        Fact {
            proposition,
            truthiness: self.truthiness,
        }
    }
}

use std::fmt;

use tower_lsp::lsp_types::Range;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::module::ModuleId;
use crate::proof_step::Truthiness;
use crate::source::{Source, SourceType};

// A value along with information on where to find it in the source.
#[derive(Debug, Clone)]
pub struct Proposition {
    // A boolean value. The essence of the proposition is "value is true".
    pub value: AcornValue,

    // Where this proposition came from.
    pub source: Source,
}

impl fmt::Display for Proposition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.fmt(f)
    }
}

impl Proposition {
    pub fn new(value: AcornValue, source: Source) -> Proposition {
        Proposition { value, source }
    }

    pub fn theorem(
        axiomatic: bool,
        value: AcornValue,
        module: ModuleId,
        range: Range,
        depth: u32,
        name: Option<String>,
    ) -> Proposition {
        Proposition {
            value,
            source: Source::theorem(axiomatic, module, range, depth, name),
        }
    }

    pub fn anonymous(value: AcornValue, module: ModuleId, range: Range, depth: u32) -> Proposition {
        Proposition {
            value,
            source: Source::anonymous(module, range, depth),
        }
    }

    // When we have a constraint, we prove the type is inhabited, which exports as vacuous.
    pub fn inhabited(module: ModuleId, type_name: &str, range: Range, depth: u32) -> Proposition {
        let value = AcornValue::Bool(true);
        Proposition {
            value,
            source: Source::inhabited(module, type_name, range, depth),
        }
    }

    pub fn type_definition(
        value: AcornValue,
        module: ModuleId,
        range: Range,
        depth: u32,
        type_name: String,
        member_name: String,
    ) -> Proposition {
        Proposition {
            value,
            source: Source::type_definition(module, range, depth, type_name, member_name),
        }
    }

    pub fn constant_definition(
        value: AcornValue,
        module: ModuleId,
        range: Range,
        depth: u32,
        constant: AcornValue,
        name: &str,
    ) -> Proposition {
        Proposition {
            value,
            source: Source::constant_definition(module, range, depth, constant, name),
        }
    }

    // A proposition that represents the instance relationship.
    pub fn instance(
        value: Option<AcornValue>,
        module: ModuleId,
        range: Range,
        depth: u32,
        instance_name: &str,
        typeclass_name: &str,
    ) -> Proposition {
        let value = value.unwrap_or(AcornValue::Bool(true));
        Proposition {
            value,
            source: Source::instance(module, range, depth, instance_name, typeclass_name),
        }
    }

    pub fn premise(value: AcornValue, module: ModuleId, range: Range, depth: u32) -> Proposition {
        Proposition {
            value,
            source: Source::premise(module, range, depth),
        }
    }

    pub fn with_negated_goal(&self, value: AcornValue) -> Proposition {
        Proposition {
            value,
            source: Source::negated_goal(self.source.module, self.source.range.clone(), self.source.depth),
        }
    }

    // Just changes the value while keeping the other stuff intact
    pub fn with_value(&self, value: AcornValue) -> Proposition {
        Proposition {
            value,
            source: self.source.clone(),
        }
    }

    // Theorems have theorem names, and so do axioms because those work like theorems.
    pub fn theorem_name(&self) -> Option<&str> {
        match &self.source.source_type {
            SourceType::Axiom(name) | SourceType::Theorem(name) => name.as_deref(),
            _ => None,
        }
    }

    // Instantiates a generic proposition to have a particular type.
    pub fn instantiate(&self, params: &[(String, AcornType)]) -> Proposition {
        let value = self.value.instantiate(params);
        if value.has_generic() {
            panic!("tried to instantiate but {} is still generic", value);
        }
        let source = match &self.source.source_type {
            SourceType::ConstantDefinition(v, name) => {
                let new_type = SourceType::ConstantDefinition(v.instantiate(params), name.clone());
                Source {
                    module: self.source.module,
                    range: self.source.range.clone(),
                    source_type: new_type,
                    importable: self.source.importable,
                    depth: self.source.depth,
                }
            }
            _ => self.source.clone(),
        };
        Proposition { value, source }
    }

    pub fn truthiness(&self) -> Truthiness {
        if self.source.source_type == SourceType::NegatedGoal {
            Truthiness::Counterfactual
        } else if self.source.depth == 0 {
            Truthiness::Factual
        } else {
            Truthiness::Hypothetical
        }
    }
}

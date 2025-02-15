use tower_lsp::lsp_types::Range;

use crate::acorn_value::AcornValue;
use crate::environment::Environment;
use crate::module::ModuleId;
use crate::proposition::Proposition;

#[derive(Debug, Clone)]
pub enum Goal {
    // Prove that this proposition is true.
    Prove(Proposition),

    // Find a simplified form of this value.
    Solve(AcornValue, Range),
}

impl Goal {
    pub fn value(&self) -> &AcornValue {
        match self {
            Goal::Prove(p) => &p.value,
            Goal::Solve(v, _) => v,
        }
    }

    pub fn range(&self) -> Range {
        match self {
            Goal::Prove(p) => p.source.range,
            Goal::Solve(_, r) => *r,
        }
    }
}

// A goal along with some information related to it.
pub struct GoalContext {
    pub module_id: ModuleId,

    // A printable name for this goal.
    pub name: String,

    // The goal itself.
    pub goal: Goal,

    // The zero-based line where we would insert a proof for this goal.
    // This is either the last line, for a goal with a block, or the first line.
    pub proof_insertion_line: u32,

    // Whether we need to insert a block, if we do insert a proof.
    pub insert_block: bool,

    // Whether it's okay if we discover an inconsistency in the provided facts.
    // If it's not okay, we warn the user.
    pub inconsistency_okay: bool,

    // This range includes the entire proof block for this goal, if there is one.
    pub first_line: u32,
    pub last_line: u32,
}

impl GoalContext {
    // env is the environment we are proving the goal in.
    pub fn new(
        env: &Environment,
        goal: Goal,
        proof_insertion_line: u32,
        first_line: u32,
        last_line: u32,
    ) -> GoalContext {
        let name = match &goal {
            Goal::Prove(proposition) => {
                // Goals should never be generic.
                assert!(!proposition.value.has_generic());

                match proposition.name() {
                    Some(name) => name.to_string(),
                    None => env
                        .bindings
                        .value_to_code(&proposition.value)
                        .unwrap_or("<goal>".to_string()),
                }
            }
            Goal::Solve(value, _) => {
                let value_str = env
                    .bindings
                    .value_to_code(value)
                    .unwrap_or("<goal>".to_string());
                format!("solve {}", value_str)
            }
        };
        GoalContext {
            module_id: env.module_id,
            name,
            goal,
            proof_insertion_line,
            insert_block: env.implicit,
            inconsistency_okay: env.includes_explicit_false,
            first_line,
            last_line,
        }
    }
}

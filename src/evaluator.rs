use crate::acorn_type::{AcornType, PotentialType};
use crate::binding_map::BindingMap;
use crate::compilation::{self, ErrorSource};
use crate::expression::Expression;
use crate::project::Project;

/// The Evaluator turns expressions into types and values, and other things of that nature.
pub struct Evaluator<'a> {
    bindings: &'a BindingMap,
    project: &'a Project,
}

impl<'a> Evaluator<'a> {
    /// Creates a new evaluator.
    pub fn new(bindings: &'a BindingMap, project: &'a Project) -> Self {
        Self { project, bindings }
    }

    /// Evaluates an expression that represents a type.
    pub fn evaluate_type(&self, expression: &Expression) -> compilation::Result<AcornType> {
        let potential = self
            .bindings
            .evaluate_potential_type(&self.project, expression)?;
        match potential {
            PotentialType::Resolved(t) => Ok(t),
            PotentialType::Unresolved(ut) => {
                Err(expression.error(&format!("type {} is unresolved", ut.class.name)))
            }
        }
    }
}

use std::fmt;

use crate::atom::{Atom, AtomId};
use crate::literal::Literal;

// A record of what happened to a single literal during a single proof step.
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum LiteralTrace {
    // This literal is in the output clause.
    Output { index: usize, flipped: bool },

    // This literal was eliminated by combining with the given step.
    // Step must be a single literal.
    Eliminated { step: usize, flipped: bool },

    // This literal was self-contradictory, of the form x != x.
    Impossible,
}

impl LiteralTrace {
    fn flip(&mut self) {
        match self {
            LiteralTrace::Output { flipped, .. } => *flipped = !*flipped,
            LiteralTrace::Eliminated { flipped, .. } => *flipped = !*flipped,
            LiteralTrace::Impossible => {}
        }
    }

    pub fn step_id(&self) -> Option<usize> {
        match self {
            LiteralTrace::Eliminated { step, .. } => Some(*step),
            _ => None,
        }
    }
}

// Modifies the first trace in place.
fn compose_traces(first: &mut Vec<LiteralTrace>, second: &Vec<LiteralTrace>) {
    for i in 0..first.len() {
        let LiteralTrace::Output { index, flipped } = first[i] else {
            continue;
        };
        first[i] = second[index].clone();
        if flipped {
            first[i].flip();
        }
    }
}

/// A record of how a clause was constructed.
/// These operations are logically after any rewrite that occurred.
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct ClauseTrace {
    /// The ID of the base clause that this trace is based on.
    pub base_id: usize,

    /// What happened to each literal in the base clause.
    pub literals: Vec<LiteralTrace>,
}

/// A clause is a disjunction (an "or") of literals, universally quantified over some variables.
/// We include the types of the universal variables it is quantified over.
/// It cannot contain existential quantifiers.
#[derive(Debug, Eq, PartialEq, Hash, Clone, Ord, PartialOrd)]
pub struct Clause {
    pub literals: Vec<Literal>,
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.literals.is_empty() {
            return write!(f, "<empty>");
        }
        for (i, literal) in self.literals.iter().enumerate() {
            if i > 0 {
                write!(f, " or ")?;
            }
            write!(f, "{}", literal)?;
        }
        Ok(())
    }
}

impl Clause {
    /// Sorts literals.
    /// Removes any duplicate or impossible literals.
    /// An empty clause indicates an impossible clause.
    pub fn new(literals: Vec<Literal>) -> Clause {
        let mut literals = literals
            .into_iter()
            .filter(|x| !x.is_impossible())
            .collect::<Vec<_>>();
        literals.sort();
        literals.dedup();

        let mut c = Clause { literals };
        c.normalize_var_ids();
        c
    }

    /// Normalizes literals into a clause, creating a trace of where each one is sent.
    /// Note that this doesn't flip any literals. It only creates the "Output" and "Impossible"
    /// type traces.
    pub fn normalize_with_trace(literals: Vec<Literal>) -> (Clause, Vec<LiteralTrace>) {
        let mut trace = vec![LiteralTrace::Impossible; literals.len()];

        // Pair each literal with its initial index.
        let mut indexed_literals: Vec<(Literal, usize)> = literals
            .into_iter()
            .enumerate()
            .filter_map(|(i, lit)| {
                if lit.is_impossible() {
                    None
                } else {
                    Some((lit, i))
                }
            })
            .collect();
        indexed_literals.sort();

        let mut output_literals = vec![];
        for (literal, input_index) in indexed_literals {
            if !output_literals.is_empty() {
                let last_index = output_literals.len() - 1;
                if literal == output_literals[last_index] {
                    // This literal is a duplicate, but it is in the output.
                    trace[input_index] = LiteralTrace::Output {
                        index: last_index,
                        flipped: false,
                    };
                    continue;
                }
            }
            let output_index = output_literals.len();
            output_literals.push(literal);
            trace[input_index] = LiteralTrace::Output {
                index: output_index,
                flipped: false,
            };
        }
        let mut c = Clause {
            literals: output_literals,
        };
        c.normalize_var_ids();
        (c, trace)
    }

    /// Creates a new clause and a new trace, given a list of literals and a
    /// trace of how they were created.
    pub fn new_with_trace(
        literals: Vec<Literal>,
        base_id: usize,
        mut trace: Vec<LiteralTrace>,
    ) -> (Clause, ClauseTrace) {
        let (c, incremental_trace) = Clause::normalize_with_trace(literals);
        compose_traces(&mut trace, &incremental_trace);

        let trace = ClauseTrace {
            base_id,
            literals: trace,
        };
        (c, trace)
    }

    /// Creates a new clause. If a trace is provided, we compose the traces.
    /// The base_trace should be applicable to the provided literals.
    pub fn new_composing_traces(
        literals: Vec<Literal>,
        base_trace: Option<ClauseTrace>,
        incremental_trace: &Vec<LiteralTrace>,
    ) -> (Clause, Option<ClauseTrace>) {
        let Some(mut base_trace) = base_trace else {
            return (Clause::new(literals), None);
        };
        compose_traces(&mut base_trace.literals, incremental_trace);
        let (c, trace) = Clause::new_with_trace(literals, base_trace.base_id, base_trace.literals);
        (c, Some(trace))
    }

    pub fn from_literal(literal: Literal, base_id: usize, flipped: bool) -> (Clause, ClauseTrace) {
        Clause::new_with_trace(
            vec![literal],
            base_id,
            vec![LiteralTrace::Output { index: 0, flipped }],
        )
    }

    /// Normalizes the variable IDs in the literals.
    /// If you reorder or modify the literals, you should call this.
    pub fn normalize_var_ids(&mut self) {
        let mut var_ids = vec![];
        for literal in &mut self.literals {
            literal.left.normalize_var_ids(&mut var_ids);
            literal.right.normalize_var_ids(&mut var_ids);
        }
    }

    /// An unsatisfiable clause. Like a lone "false".
    pub fn impossible() -> Clause {
        Clause::new(vec![])
    }

    pub fn parse(s: &str) -> Clause {
        Clause::new(
            s.split(" or ")
                .map(|x| Literal::parse(x))
                .collect::<Vec<_>>(),
        )
    }

    pub fn is_tautology(&self) -> bool {
        // Find the index of the first positive literal
        if let Some(first_pos) = self.literals.iter().position(|x| x.positive) {
            // Check for (!p, p) pairs which cause a tautology
            for neg_literal in &self.literals[0..first_pos] {
                for pos_literal in &self.literals[first_pos..] {
                    if neg_literal.left == pos_literal.left
                        && neg_literal.right == pos_literal.right
                    {
                        return true;
                    }
                }
            }
        }

        self.literals.iter().any(|x| x.is_tautology())
    }

    pub fn is_impossible(&self) -> bool {
        self.literals.is_empty()
    }

    pub fn atom_count(&self) -> u32 {
        self.literals.iter().map(|x| x.atom_count()).sum()
    }

    pub fn len(&self) -> usize {
        self.literals.len()
    }

    pub fn has_any_variable(&self) -> bool {
        self.literals.iter().any(|x| x.has_any_variable())
    }

    pub fn has_skolem(&self) -> bool {
        self.literals.iter().any(|x| x.has_skolem())
    }

    pub fn has_local_constant(&self) -> bool {
        self.literals.iter().any(|x| x.has_local_constant())
    }

    pub fn num_positive_literals(&self) -> usize {
        self.literals.iter().filter(|x| x.positive).count()
    }

    pub fn least_unused_variable(&self) -> AtomId {
        self.literals
            .iter()
            .map(|x| x.least_unused_variable())
            .max()
            .unwrap_or(0)
    }

    /// Whether every literal in this clause is exactly contained by the other clause.
    pub fn contains(&self, other: &Clause) -> bool {
        for literal in &other.literals {
            if !self.literals.iter().any(|x| x == literal) {
                return false;
            }
        }
        true
    }

    /// Whether any top level term has the given atom as its head.
    pub fn has_head(&self, atom: &Atom) -> bool {
        self.literals.iter().any(|x| x.has_head(atom))
    }

    /// Whether we are willing to turn this clause into a line of code in a proof.
    pub fn is_printable(&self) -> bool {
        if self.len() > 1 {
            return false;
        }
        if self.has_skolem() {
            return false;
        }
        true
    }

    /// Converts atoms from the given list to variables, and shifts existing variables to make room.
    pub fn convert_to_variable(&self, from: &[Atom]) -> Clause {
        let new_literals = self
            .literals
            .iter()
            .map(|lit| lit.convert_to_variable(from))
            .collect();
        Clause {
            literals: new_literals,
        }
    }
}

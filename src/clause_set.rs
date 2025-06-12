use std::cmp::Ordering;
use std::vec;

use crate::clause::Clause;
use crate::pattern_tree::PatternTree;
use crate::term::Term;

/// The ClauseSet stores general clauses in a way that allows us to quickly check whether
/// a new clause is a specialization of an existing one.
pub struct ClauseSet {
    /// Stores an id for each clause.
    tree: PatternTree<usize>,
}

impl ClauseSet {
    pub fn new() -> ClauseSet {
        ClauseSet {
            tree: PatternTree::new(),
        }
    }

    /// Inserts a clause into the set, reordering it in every way that is KBO-nonincreasing.
    pub fn insert(&mut self, mut clause: Clause, id: usize) {
        let mut generalized = vec![];
        all_generalized_forms(&mut clause, 0, &mut generalized);
        for c in generalized {
            self.tree.insert_clause(&c, id);
        }
    }

    pub fn find_generalization(&self, clause: &Clause) -> Option<usize> {
        let special = specialized_form(&clause);
        self.tree.find_clause(&special).map(|id| *id)
    }
}

/// Stable under variable substitution, like KBO, but hopefully closer to total in practice.
/// Returns Greater if self > other.
/// Returns Less if other > self.
/// Returns None if they are not comparable.
/// Returns Equal if they are actually equal.
///
/// Concrete terms should always be orderable.
pub fn sub_invariant_term_cmp(
    left: &Term,
    left_neg: bool,
    right: &Term,
    right_neg: bool,
) -> Option<Ordering> {
    // First, compare the head types.
    // I think this is actually more indicative of complexity than the type itself.
    let head_type_cmp = left.head_type.cmp(&right.head_type);
    if head_type_cmp != Ordering::Equal {
        return Some(head_type_cmp);
    }

    // Next, compare the types.
    let type_cmp = left.term_type.cmp(&right.term_type);
    if type_cmp != Ordering::Equal {
        return Some(type_cmp);
    }

    // Compare the signs
    let neg_cmp = left_neg.cmp(&right_neg);
    if neg_cmp != Ordering::Equal {
        return Some(neg_cmp);
    }

    // Then, compare the heads.
    if left.head.is_variable() || right.head.is_variable() {
        // There's no way to compare these things in a substitution-invariant way.
        return None;
    }

    // Recurse
    assert!(left.args.len() == right.args.len());
    for (l, r) in left.args.iter().zip(right.args.iter()) {
        match sub_invariant_term_cmp(l, false, r, false) {
            Some(Ordering::Equal) => continue,
            x => return x,
        };
    }

    Some(Ordering::Equal)
}

/// The generalized and specialized forms relate to each other.
/// When we specialize a clause and put it into the specialized form, it must match
/// one of the generalized forms.
/// The "form" includes both the order of the literals and the direction of each literal.
///
/// Call with zero to start the recursion. First we check all directions of the literals.
/// The start index is the first one to consider swapping.
fn all_generalized_forms(base_clause: &mut Clause, start_index: usize, output: &mut Vec<Clause>) {
    if start_index >= base_clause.literals.len() {
        // We have a complete clause, so we can move on to the reordering stage.
        all_generalized_orders(base_clause, output);
        return;
    }
    let literal = &base_clause.literals[start_index];
    // Ignore literal sign in this stage
    let cmp = sub_invariant_term_cmp(&literal.left, true, &literal.right, true);
    if cmp != Some(Ordering::Less) {
        // The pre-existing direction is okay.
        all_generalized_forms(base_clause, start_index + 1, output);
    }
    if cmp == None || cmp == Some(Ordering::Less) {
        // The swapped direction is okay.
        base_clause.literals[start_index].flip();
        all_generalized_forms(base_clause, start_index + 1, output);
        base_clause.literals[start_index].flip();
    }
}

/// Generate all orders of the provided clause that are a valid generalized form.
fn all_generalized_orders(base_clause: &Clause, output: &mut Vec<Clause>) {
    todo!();
}

/// Put this clause into the "specialized" form.
/// This should only be called on concrete clauses.
fn specialized_form(_base_clause: &Clause) -> Clause {
    todo!();
}

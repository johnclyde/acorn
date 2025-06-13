use std::cmp::Ordering;
use std::vec;

use crate::clause::Clause;
use crate::literal::Literal;
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

    pub fn find_generalization(&self, clause: Clause) -> Option<usize> {
        let special = specialized_form(clause);
        self.tree.find_clause(&special).map(|id| *id)
    }
}

/// Compare two literals in a substitution-invariant way.
/// First compares left terms, then right terms if left terms are equal.
fn sub_invariant_literal_cmp(lit1: &Literal, lit2: &Literal) -> Option<Ordering> {
    // First compare the left terms
    let left_cmp = sub_invariant_term_cmp(&lit1.left, !lit1.positive, &lit2.left, !lit2.positive);
    match left_cmp {
        Some(Ordering::Equal) => {
            // If left terms are equal, compare right terms
            sub_invariant_term_cmp(&lit1.right, !lit1.positive, &lit2.right, !lit2.positive)
        }
        other => other,
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
    
    // If heads are different atoms, we can compare them
    if left.head != right.head {
        return Some(left.head.cmp(&right.head));
    }

    // Heads are the same, so recurse on arguments
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
    // Helper function to generate all permutations recursively
    fn generate_permutations(
        literals: &[Literal],
        current: &mut Vec<Literal>,
        used: &mut Vec<bool>,
        output: &mut Vec<Clause>,
    ) {
        // Base case: we've built a complete permutation
        if current.len() == literals.len() {
            let mut clause = Clause {
                literals: current.clone(),
            };
            clause.normalize_var_ids();
            output.push(clause);
            return;
        }

        // Try each unused literal as the next element
        for i in 0..literals.len() {
            if used[i] {
                continue;
            }

            // Check if this literal can be the next one in a non-increasing order
            if let Some(last) = current.last() {
                let cmp = sub_invariant_literal_cmp(last, &literals[i]);
                if cmp == Some(Ordering::Less) {
                    continue;
                }
            }

            // Mark this literal as used
            used[i] = true;
            current.push(literals[i].clone());

            // Recurse
            generate_permutations(literals, current, used, output);

            // Backtrack
            current.pop();
            used[i] = false;
        }
    }

    let mut current = Vec::new();
    let mut used = vec![false; base_clause.literals.len()];
    generate_permutations(&base_clause.literals, &mut current, &mut used, output);
}

/// Put this clause into the "specialized" form.
/// This should only be called on concrete clauses.
fn specialized_form(mut clause: Clause) -> Clause {
    // First, ensure each literal has the larger term on the left
    for literal in &mut clause.literals {
        let cmp = sub_invariant_term_cmp(&literal.left, true, &literal.right, true)
            .expect("Concrete terms should always be comparable");
        if cmp == Ordering::Less {
            // The right term is larger, so swap
            literal.flip();
        }
    }

    // Then, sort the literals using our comparison function
    // Since this is for concrete clauses, we can unwrap the comparison
    clause.literals.sort_by(|a, b| {
        sub_invariant_literal_cmp(a, b)
            .expect("Concrete literals should always be comparable")
            .reverse() // Reverse to get non-increasing order
    });

    clause.normalize_var_ids();
    clause
}

#[cfg(test)]
mod tests {
    use super::*;


    #[test]
    fn test_clause_set_basic_generalization() {
        let mut clause_set = ClauseSet::new();
        
        // Insert a general clause: "c0(x0, c1) or c2(c3, x0)"
        let general_clause = Clause::parse("c0(x0, c1) or c2(c3, x0)");
        clause_set.insert(general_clause, 1);
        
        // Test that a specialized version is recognized
        let special_clause = Clause::parse("c2(c3, c3) or c0(c3, c1)");
        let result = clause_set.find_generalization(special_clause);
        assert_eq!(result, Some(1), "Should find the generalization");
    }

    #[test]
    fn test_clause_set_reordered_literals() {
        let mut clause_set = ClauseSet::new();
        
        // Insert a clause with specific order
        let clause = Clause::parse("c0(x0) or c1(c2, x0) or c3(x0, c4)");
        clause_set.insert(clause, 2);
        
        // Test that reordered specializations are recognized
        let special1 = Clause::parse("c1(c2, c5) or c3(c5, c4) or c0(c5)");
        assert_eq!(clause_set.find_generalization(special1), Some(2));
        
        let special2 = Clause::parse("c3(c6, c4) or c0(c6) or c1(c2, c6)");
        assert_eq!(clause_set.find_generalization(special2), Some(2));
    }

    #[test]
    fn test_clause_set_flipped_equality() {
        let mut clause_set = ClauseSet::new();
        
        // Insert an equality clause
        let clause = Clause::parse("x0 = c0 or c1(x0)");
        clause_set.insert(clause, 3);
        
        // Test that flipped equalities are recognized
        let special = Clause::parse("c2 = c0 or c1(c2)");
        assert_eq!(clause_set.find_generalization(special), Some(3));
        
        // Also test with the equality already flipped
        let special2 = Clause::parse("c0 = c3 or c1(c3)");
        assert_eq!(clause_set.find_generalization(special2), Some(3));
    }

    #[test]
    fn test_clause_set_no_generalization() {
        let mut clause_set = ClauseSet::new();
        
        // Insert a specific clause
        let clause = Clause::parse("c0(c1, c2) or c3(c4)");
        clause_set.insert(clause, 4);
        
        // Test clauses that should NOT have generalizations
        let no_match1 = Clause::parse("c0(c1, c4) or c3(c4)");
        assert_eq!(clause_set.find_generalization(no_match1), None);
        
        let no_match2 = Clause::parse("c0(c2, c1) or c3(c4)");
        assert_eq!(clause_set.find_generalization(no_match2), None);
    }

    #[test]
    fn test_clause_set_multiple_variables() {
        let mut clause_set = ClauseSet::new();
        
        // Insert a clause with multiple variables
        let clause = Clause::parse("c0(x0, x1) or c1(x1, x0)");
        clause_set.insert(clause, 5);
        
        // Test various specializations
        let special1 = Clause::parse("c0(c2, c3) or c1(c3, c2)");
        assert_eq!(clause_set.find_generalization(special1), Some(5));
        
        let special2 = Clause::parse("c1(c4, c5) or c0(c5, c4)");
        assert_eq!(clause_set.find_generalization(special2), Some(5));
        
        // This should NOT match because the variable pattern is different
        let no_match = Clause::parse("c0(c2, c3) or c1(c4, c5)");
        assert_eq!(clause_set.find_generalization(no_match), None);
    }

    #[test]
    fn test_clause_set_single_literal() {
        let mut clause_set = ClauseSet::new();
        
        // Insert single literal clauses
        let clause1 = Clause::parse("c0(x0, c1)");
        clause_set.insert(clause1, 6);
        
        let clause2 = Clause::parse("x0 = c1");
        clause_set.insert(clause2, 7);
        
        // Test specializations
        assert_eq!(clause_set.find_generalization(Clause::parse("c0(c2, c1)")), Some(6));
        assert_eq!(clause_set.find_generalization(Clause::parse("c2 = c1")), Some(7));
        assert_eq!(clause_set.find_generalization(Clause::parse("c1 = c2")), Some(7));
    }

    #[test]
    fn test_clause_set_negated_literals() {
        let mut clause_set = ClauseSet::new();
        
        // Insert a clause with negated literals
        let clause = Clause::parse("c0 = x0 or x1 != c1");
        clause_set.insert(clause, 1);
        
        // Test that it matches correct specializations
        let special1 = Clause::parse("c0 = c2 or c3 != c1");
        assert_eq!(clause_set.find_generalization(special1), Some(1));
        
        // Test with reordered literals
        let special2 = Clause::parse("c4 != c1 or c0 = c4");
        assert_eq!(clause_set.find_generalization(special2), Some(1));
        
        // Test with flipped inequality
        let special3 = Clause::parse("c0 = c5 or c1 != c5");
        assert_eq!(clause_set.find_generalization(special3), Some(1));
    }

    #[test]
    fn test_clause_set_no_positive_negative_confusion() {
        let mut clause_set = ClauseSet::new();
        
        // Insert a clause with a positive literal
        let positive_clause = Clause::parse("x0 = c0");
        clause_set.insert(positive_clause, 1);
        
        // Insert a clause with a negative literal
        let negative_clause = Clause::parse("x0 != c1");
        clause_set.insert(negative_clause, 2);
        
        // Test that positive matches positive
        assert_eq!(clause_set.find_generalization(Clause::parse("c2 = c0")), Some(1));
        
        // Test that negative matches negative
        assert_eq!(clause_set.find_generalization(Clause::parse("c3 != c1")), Some(2));
        
        // Test that positive does NOT match negative
        assert_eq!(clause_set.find_generalization(Clause::parse("c2 != c0")), None);
        
        // Test that negative does NOT match positive
        assert_eq!(clause_set.find_generalization(Clause::parse("c3 = c1")), None);
    }

    #[test]
    fn test_clause_set_mixed_positive_negative() {
        let mut clause_set = ClauseSet::new();
        
        // Insert a complex clause with both positive and negative literals
        // Using "not" for boolean literals and "!=" for inequalities
        let clause = Clause::parse("not c0(x0) or c1(x0, x1) or x1 != c2");
        clause_set.insert(clause, 1);
        
        // Test various specializations
        let special1 = Clause::parse("not c0(c3) or c1(c3, c4) or c4 != c2");
        assert_eq!(clause_set.find_generalization(special1), Some(1));
        
        // Test with reordering
        let special2 = Clause::parse("c1(c5, c6) or c6 != c2 or not c0(c5)");
        assert_eq!(clause_set.find_generalization(special2), Some(1));
        
        // Test that wrong signs don't match
        let wrong1 = Clause::parse("c0(c3) or c1(c3, c4) or c4 != c2");  // First literal should be negative
        assert_eq!(clause_set.find_generalization(wrong1), None);
        
        let wrong2 = Clause::parse("not c0(c3) or not c1(c3, c4) or c4 != c2");  // Second literal should be positive
        assert_eq!(clause_set.find_generalization(wrong2), None);
    }

    #[test]
    fn test_clause_set_all_negative() {
        let mut clause_set = ClauseSet::new();
        
        // Insert a simpler clause with only inequality literals
        let clause = Clause::parse("x0 != c0 or x1 != c1 or x0 != x1");
        clause_set.insert(clause, 1);
        
        // Test that it matches
        let special = Clause::parse("c2 != c0 or c3 != c1 or c2 != c3");
        assert_eq!(clause_set.find_generalization(special), Some(1));
        
        // Test with reordering
        let special2 = Clause::parse("c4 != c5 or c4 != c0 or c5 != c1");
        assert_eq!(clause_set.find_generalization(special2), Some(1));
    }

    #[test]
    fn test_clause_set_boolean_negation() {
        let mut clause_set = ClauseSet::new();
        
        // Test with boolean negation (not)
        let clause = Clause::parse("not c0(x0) or c1(x0)");
        clause_set.insert(clause, 1);
        
        // Test that it matches
        let special = Clause::parse("not c0(c2) or c1(c2)");
        assert_eq!(clause_set.find_generalization(special), Some(1));
        
        // Test reordering
        let special2 = Clause::parse("c1(c3) or not c0(c3)");
        assert_eq!(clause_set.find_generalization(special2), Some(1));
        
        // Test that signs matter
        let wrong = Clause::parse("c0(c2) or c1(c2)");  // Missing "not"
        assert_eq!(clause_set.find_generalization(wrong), None);
    }
}

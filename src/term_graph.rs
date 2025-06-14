use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::hash::Hash;

use crate::atom::Atom;
use crate::clause::Clause;
use crate::term::Term;

/// Each term has a unique id.
/// We never invent new terms. We only make copies of terms that the caller created and find
/// relationships between them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermId(u32);

impl fmt::Display for TermId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Every time we set two terms equal or not equal, that action is tagged with a StepId.
/// The term graph uses it to provide a history of the reasoning that led to a conclusion.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StepId(pub usize);

impl StepId {
    pub fn get(&self) -> usize {
        self.0
    }
}

impl fmt::Display for StepId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// The rationale for a single rewrite step.
#[derive(Debug, Eq, PartialEq, Copy, Clone, Ord, PartialOrd)]
pub struct RewriteStep {
    /// The id of the rule used for this rewrite.
    /// We know this rewrite is true based on the pattern step alone.
    pub pattern_id: StepId,

    /// The id of the rule containing the subterm that inspired this rewrite.
    /// If it was just the rewrite pattern that inspired this step, this is None.
    /// This isn't mathematically necessary to prove the step, but it is necessary to recreate this rule.
    pub inspiration_id: Option<StepId>,
}

/// The goal of the TermGraph is to find a contradiction.
/// When we do, we need to explain to the outside world why this is actually a contradiction.
/// The TermGraphContradiction encodes this.
///
/// Warning!
/// Currently this can only represent contradictions that come from a series of rewrites.
/// In particular, it can't represent contradictions that use clause reduction.
/// So, beware.
#[derive(Debug, Eq, PartialEq)]
pub struct TermGraphContradiction {
    /// Every contradiction is based on one inequality, plus a set of rewrites that turn
    /// one site of the inequality into the other.
    pub inequality_id: usize,

    /// The rewrites that turn one side of the inequality into the other.
    pub rewrite_chain: Vec<(Term, Term, RewriteStep)>,
}

// Each term has a Decomposition that describes how it is created.
#[derive(Debug, Eq, Hash, PartialEq, Clone)]
enum Decomposition {
    // The term is just equal to an atom
    Atomic(Atom),

    // Head and args
    Compound(TermId, Vec<TermId>),
}

#[derive(Clone)]
struct TermInfo {
    term: Term,
    group: GroupId,
    decomp: Decomposition,

    // The terms that this one can be directly turned into.
    // When the step id is not provided, we concluded it from composition.
    adjacent: Vec<(TermId, Option<RewriteStep>)>,
}

// Each term belongs to a group.
// Terms that belong to the same group are equal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct GroupId(u32);

impl fmt::Display for GroupId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone)]
struct GroupInfo {
    // All of the terms that belong to this group, in the order they were added.
    terms: Vec<TermId>,

    // Each way to create a term of this group by composing subterms from other groups.
    // This might include references to deleted compounds. They are only cleaned up lazily.
    compounds: Vec<CompoundId>,

    // The other groups that we know are not equal to this one.
    // For each inequality, we store the two terms that we know are not equal,
    // along with the step that we know it from.
    inequalities: HashMap<GroupId, (TermId, TermId, StepId)>,

    // The clauses that are related to this group.
    // Keyed by the group that is on the other side of the literal from this one.
    // THis might include references to deleted clauses. They are only cleaned up lazily.
    clauses: HashMap<GroupId, Vec<ClauseId>>,
}

impl GroupInfo {
    fn heuristic_size(&self) -> usize {
        self.terms.len() + self.compounds.len()
    }
}

// Each composition relation between terms implies a composition relation between groups.
// The composition relations between groups each get their own id, so we can update them when
// we combine groups.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct CompoundId(u32);

impl fmt::Display for CompoundId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Eq, Hash, PartialEq, Clone)]
struct CompoundKey {
    head: GroupId,
    args: Vec<GroupId>,
}

impl CompoundKey {
    fn remap_group(&mut self, small_group: GroupId, large_group: GroupId) {
        if self.head == small_group {
            self.head = large_group;
        }
        for arg in &mut self.args {
            if *arg == small_group {
                *arg = large_group;
            }
        }
    }

    fn groups(&self) -> Vec<GroupId> {
        let mut answer = vec![self.head];
        answer.extend(self.args.iter().copied());
        answer.sort();
        answer.dedup();
        answer
    }

    fn touches_group(&self, group: GroupId) -> bool {
        if self.head == group {
            return true;
        }
        self.args.contains(&group)
    }
}

impl fmt::Display for CompoundKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.head)?;
        if !self.args.is_empty() {
            write!(f, "(")?;
            for (i, arg) in self.args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", arg)?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}

#[derive(Clone)]
struct CompoundInfo {
    key: CompoundKey,
    result_term: TermId,
}

impl fmt::Display for CompoundInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "key {} -> term {}", self.key, self.result_term)
    }
}

// We represent literals based on their terms.
// This isn't quite enough to have good tracking information, so we might need to expand on this.
#[derive(Clone)]
struct LiteralInfo {
    positive: bool,
    left: TermId,
    right: TermId,
}

#[derive(Clone)]
struct ClauseInfo {
    // The literals that make up the clause.
    literals: Vec<LiteralInfo>,

    // The step in which we added this clause to the graph.
    step: StepId,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
struct ClauseId(usize);

impl fmt::Display for ClauseId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// In general, there are two sorts of operations that are performed on the graph.
//
// "Integrity" operations are to keep the graph valid. A lot of the data is denormalized,
// so we have to update it in multiple places to keep it consistent.
// Integrity operations are performed immediately. Integrity operations should not trigger
// other integrity operations recursively.
//
// "Semantic" operations are to reflect the underlying meaning of the terms, like
// declaring that two terms are identical, or representing that some clause is true.
// It's hard to do a semantic operation in the middle of performing an integrity operation,
// because you can't recurse and do a huge number of operations when the graph is in
// an inconsistent state. It's okay if semantic operations trigger other semantic operations.
//
// Thus, our strategy is to finish any integrity operations immediately, but leave semantic
// operations in this queue. The SemanticOperation represents an element in this queue.
#[derive(Clone)]
enum SemanticOperation {
    // We have discovered that two terms are equal.
    TermEquality(TermId, TermId, Option<RewriteStep>),

    // We have discovered that two terms are not equal.
    TermInequality(TermId, TermId, StepId),

    // We have discovered that a clause can be reduced.
    ClauseReduction(ClauseId),
}

/// The TermGraph stores concrete terms, along with relationships between them that represent
/// equality, inequality, and subterm relationships.
#[derive(Clone)]
pub struct TermGraph {
    // terms maps TermId to TermInfo.
    terms: Vec<TermInfo>,

    // groups maps GroupId to GroupInfo.
    groups: Vec<Option<GroupInfo>>,

    // compounds maps CompoundId to CompoundInfo.
    // When a compound is deleted, we replace it with None.
    compounds: Vec<Option<CompoundInfo>>,

    // clauses maps ClauseId to ClauseInfo.
    // When a clause is eliminated, we replace it with None.
    clauses: Vec<Option<ClauseInfo>>,

    // Keying the compounds so that we can check if a composition belongs to an existing group.
    compound_map: HashMap<CompoundKey, TermId>,

    // Each term has its decomposition stored so that we can look it back up again
    decompositions: HashMap<Decomposition, TermId>,

    // The pending semantic operations on the graph.
    pending: Vec<SemanticOperation>,

    // A flag for whether there is a contradiction.
    // Separate from contradiction_info to encode the awkward case where we know there
    // is a contradiction, but we don't know how to extract a trace for it.
    has_contradiction: bool,

    // Set when we discover a contradiction, if we know how to extract a trace for it.
    // When set, this indicates that the provided step sets these terms to be unequal.
    // But there is a chain of rewrites that proves that they are equal. This is a contradiction.
    contradiction_info: Option<(TermId, TermId, StepId)>,
}

impl TermGraph {
    pub fn new() -> TermGraph {
        TermGraph {
            terms: Vec::new(),
            groups: Vec::new(),
            compounds: Vec::new(),
            clauses: Vec::new(),
            compound_map: HashMap::new(),
            decompositions: HashMap::new(),
            pending: Vec::new(),
            has_contradiction: false,
            contradiction_info: None,
        }
    }

    /// Returns None if this term isn't in the graph.
    pub fn get_term_id(&self, term: &Term) -> Option<TermId> {
        // Look up the head
        let head_key = Decomposition::Atomic(term.head.clone());
        let head_id = *self.decompositions.get(&head_key)?;

        if term.args.is_empty() {
            return Some(head_id);
        }

        // Look up the args
        let mut arg_ids = Vec::new();
        for arg in &term.args {
            arg_ids.push(self.get_term_id(arg)?);
        }

        let compound_key = Decomposition::Compound(head_id, arg_ids);
        self.decompositions.get(&compound_key).copied()
    }

    pub fn get_term(&self, term_id: TermId) -> &Term {
        &self.terms[term_id.0 as usize].term
    }

    fn get_group_id(&self, term_id: TermId) -> GroupId {
        self.terms[term_id.0 as usize].group
    }

    /// Whether there is any sort of contradiction at all.
    pub fn has_contradiction(&self) -> bool {
        self.has_contradiction
    }

    /// Whether there is a contradiction with trace information.
    pub fn has_contradiction_trace(&self) -> bool {
        self.contradiction_info.is_some()
    }

    /// Used to explain which steps lead to a contradiction.
    /// Returns None if there is no contradiction trace.
    pub fn get_contradiction_trace(&self) -> Option<TermGraphContradiction> {
        let (term1, term2, inequality_id) = self.contradiction_info?;
        let mut rewrite_chain = vec![];
        self.expand_steps(term1, term2, &mut rewrite_chain);
        Some(TermGraphContradiction {
            inequality_id: inequality_id.get(),
            rewrite_chain,
        })
    }

    fn get_group_info(&self, group_id: GroupId) -> &GroupInfo {
        match &self.groups[group_id.0 as usize] {
            None => panic!("group is remapped"),
            Some(info) => info,
        }
    }

    fn get_clause_info(&self, clause_id: ClauseId) -> &Option<ClauseInfo> {
        &self.clauses[clause_id.0]
    }

    // Inserts the head of the provided term as an atom.
    // If it's already in the graph, return the existing term id.
    // Otherwise, make a new term id and give it a new group.
    fn insert_head(&mut self, term: &Term) -> TermId {
        let key = Decomposition::Atomic(term.head.clone());
        if let Some(&id) = self.decompositions.get(&key) {
            return id;
        }

        // Make a new term and group
        let term_id = TermId(self.terms.len() as u32);
        let group_id = GroupId(self.groups.len() as u32);

        let head = Term {
            term_type: term.head_type,
            head_type: term.head_type,
            head: term.head.clone(),
            args: vec![],
        };
        let term_info = TermInfo {
            term: head,
            group: group_id,
            decomp: key.clone(),
            adjacent: vec![],
        };
        self.terms.push(term_info);
        let group_info = Some(GroupInfo {
            terms: vec![term_id],
            compounds: vec![],
            inequalities: HashMap::new(),
            clauses: HashMap::new(),
        });
        self.groups.push(group_info);
        self.decompositions.insert(key, term_id);
        term_id
    }

    // Inserts a term composition relationship.
    // If it's already in the graph, return the existing term id.
    // Otherwise, make a new term and group.
    fn insert_term_compound(&mut self, term: &Term, head: TermId, args: Vec<TermId>) -> TermId {
        let key = Decomposition::Compound(head, args);
        if let Some(&id) = self.decompositions.get(&key) {
            return id;
        }

        // Make a new term and group
        let term_id = TermId(self.terms.len() as u32);
        let group_id = GroupId(self.groups.len() as u32);
        let term_info = TermInfo {
            term: term.clone(),
            group: group_id,
            decomp: key.clone(),
            adjacent: vec![],
        };
        self.terms.push(term_info);
        let group_info = Some(GroupInfo {
            terms: vec![term_id],
            compounds: vec![],
            inequalities: HashMap::new(),
            clauses: HashMap::new(),
        });
        self.groups.push(group_info);
        self.decompositions.insert(key, term_id);
        term_id
    }

    // Adds a group composition relationship.
    // If we should combine groups, add them to the pending list.
    fn insert_group_compound(&mut self, head: GroupId, args: Vec<GroupId>, result_term: TermId) {
        let result_group = self.get_group_id(result_term);
        let key = CompoundKey { head, args };
        if let Some(&existing_result_term) = self.compound_map.get(&key) {
            let existing_result_group = self.get_group_id(existing_result_term);
            if existing_result_group != result_group {
                self.pending.push(SemanticOperation::TermEquality(
                    existing_result_term,
                    result_term,
                    None,
                ));
            }
            return;
        }

        // We need to make a new relatinoship
        let compound_info = CompoundInfo {
            key: key.clone(),
            result_term,
        };
        for group in key.groups() {
            match &mut self.groups[group.0 as usize] {
                None => {
                    panic!("compound info refers to a remapped group");
                }
                Some(info) => {
                    info.compounds.push(CompoundId(self.compounds.len() as u32));
                }
            }
        }
        self.compounds.push(Some(compound_info));
        self.compound_map.insert(key, result_term);
        return;
    }

    /// Inserts a term.
    /// Makes a new term, group, and compound if necessary.
    pub fn insert_term(&mut self, term: &Term) -> TermId {
        let head_term_id = self.insert_head(term);
        if term.args.is_empty() {
            return head_term_id;
        }
        let head_group_id = self.get_group_id(head_term_id);

        let mut arg_term_ids = vec![];
        let mut arg_group_ids = vec![];
        for arg in &term.args {
            let arg_term_id = self.insert_term(arg);
            arg_term_ids.push(arg_term_id);
            let arg_group_id = self.get_group_id(arg_term_id);
            arg_group_ids.push(arg_group_id);
        }

        let result_term_id = self.insert_term_compound(term, head_term_id, arg_term_ids);
        self.insert_group_compound(head_group_id, arg_group_ids, result_term_id);
        self.process_pending();
        result_term_id
    }

    /// Inserts a clause into the graph.
    /// All terms in the clause are inserted if not already present.
    /// The clause is indexed by all groups that appear in its literals.
    /// Don't insert clauses with no literals.
    pub fn insert_clause(&mut self, clause: &Clause, step: StepId) {
        // First, insert all terms and collect their IDs
        let mut literal_infos = Vec::new();
        for literal in &clause.literals {
            let left_id = self.insert_term(&literal.left);
            let right_id = self.insert_term(&literal.right);
            if clause.literals.len() == 1 {
                // If this is a single literal, we can just set the terms equal or not equal
                if literal.positive {
                    self.set_terms_equal(left_id, right_id, step, None);
                } else {
                    self.set_terms_not_equal(left_id, right_id, step);
                }
                return;
            }
            literal_infos.push(LiteralInfo {
                positive: literal.positive,
                left: left_id,
                right: right_id,
            });
        }

        // Create the clause info
        let clause_info = ClauseInfo {
            literals: literal_infos.clone(),
            step,
        };

        // Add the clause to the clauses vector
        let clause_id = ClauseId(self.clauses.len());
        self.clauses.push(Some(clause_info));

        // For each literal, add the clause to both groups involved
        for literal_info in &literal_infos {
            let left_group = self.get_group_id(literal_info.left);
            let right_group = self.get_group_id(literal_info.right);

            // Add to left group's clauses, indexed by right group
            if let Some(left_group_info) = &mut self.groups[left_group.0 as usize] {
                left_group_info
                    .clauses
                    .entry(right_group)
                    .or_insert_with(Vec::new)
                    .push(clause_id.clone());
            }

            // Add to right group's clauses, indexed by left group
            if let Some(right_group_info) = &mut self.groups[right_group.0 as usize] {
                right_group_info
                    .clauses
                    .entry(left_group)
                    .or_insert_with(Vec::new)
                    .push(clause_id.clone());
            }
        }
    }

    // Merge the small group into the large group.
    fn remap_group(
        &mut self,
        old_term: TermId,
        old_group: GroupId,
        new_term: TermId,
        new_group: GroupId,
        step: Option<RewriteStep>,
    ) {
        let old_info = self.groups[old_group.0 as usize]
            .take()
            .expect("group is remapped");

        for &term_id in &old_info.terms {
            self.terms[term_id.0 as usize].group = new_group;
        }

        let mut keep_compounds = vec![];
        for compound_id in old_info.compounds {
            {
                let compound = match &mut self.compounds[compound_id.0 as usize] {
                    Some(compound) => compound,
                    None => {
                        // This compound has already been deleted.
                        // Time to lazily delete the reference to it.
                        continue;
                    }
                };
                self.compound_map.remove(&compound.key);
                compound.key.remap_group(old_group, new_group);
            }
            let compound = self.compounds[compound_id.0 as usize]
                .as_ref()
                .expect("how does this happen?");

            if let Some(&existing_result_term) = self.compound_map.get(&compound.key) {
                // An compound for the new relationship already exists.
                // Instead of inserting compound.result, we need to delete this compound, and merge the
                // intended result with result_group.
                self.pending.push(SemanticOperation::TermEquality(
                    compound.result_term,
                    existing_result_term,
                    None,
                ));
                self.compounds[compound_id.0 as usize] = None;
            } else {
                self.compound_map
                    .insert(compound.key.clone(), compound.result_term);
                keep_compounds.push(compound_id);
            }
        }

        // Rekey the inequalities that refer to this group from elsewhere
        for &unequal_group in old_info.inequalities.keys() {
            let unequal_info = self.groups[unequal_group.0 as usize]
                .as_mut()
                .expect("group is remapped");
            let value = unequal_info
                .inequalities
                .remove(&old_group)
                .expect("inequality not there");
            if unequal_group == new_group {
                // We found a contradiction.
                self.has_contradiction = true;
                self.contradiction_info = Some(value);
            }
            if !unequal_info.inequalities.contains_key(&new_group) {
                unequal_info.inequalities.insert(new_group, value);
            }
        }

        // Merge the old info into the new info
        let new_info = self.groups[new_group.0 as usize]
            .as_mut()
            .expect("group is remapped");
        new_info.terms.extend(old_info.terms);
        new_info.compounds.extend(keep_compounds);
        for (group, value) in old_info.inequalities {
            if !new_info.inequalities.contains_key(&group) {
                new_info.inequalities.insert(group, value);
            }
        }

        // First, merge clauses from old_group into new_group and track which other groups need updates
        let mut other_groups_to_update = Vec::new();
        for (other_group, mut clause_ids) in old_info.clauses {
            let key_group = if other_group == old_group {
                // Self-referential: old_group -> old_group becomes new_group -> new_group
                new_group
            } else {
                // Track that this other group needs to be updated
                if other_group != new_group {
                    other_groups_to_update.push(other_group);
                }
                other_group
            };

            // If key_group == new_group, these clauses now compare a group to itself
            // and need reduction
            if key_group == new_group {
                for &clause_id in &clause_ids {
                    self.pending
                        .push(SemanticOperation::ClauseReduction(clause_id));
                }
            }

            new_info
                .clauses
                .entry(key_group)
                .or_insert_with(Vec::new)
                .append(&mut clause_ids);
        }

        // Now update the other groups to point to new_group instead of old_group
        for other_group in other_groups_to_update {
            if let Some(other_info) = self.groups[other_group.0 as usize].as_mut() {
                if let Some(clauses) = other_info.clauses.remove(&old_group) {
                    // If other_group == new_group, these clauses now compare a group to itself
                    if other_group == new_group {
                        for &clause_id in &clauses {
                            self.pending
                                .push(SemanticOperation::ClauseReduction(clause_id));
                        }
                    }

                    other_info
                        .clauses
                        .entry(new_group)
                        .or_insert_with(Vec::new)
                        .extend(clauses);
                }
            }
        }
        
        // Also need to remove old_group from new_group's clauses if it exists
        // Do this after the loop to avoid borrow checker issues
        let new_info = self.groups[new_group.0 as usize]
            .as_mut()
            .expect("group is remapped");
        if let Some(clauses) = new_info.clauses.remove(&old_group) {
            // These clauses now compare a group to itself and need reduction
            for &clause_id in &clauses {
                self.pending.push(SemanticOperation::ClauseReduction(clause_id));
            }
        }

        self.terms[old_term.0 as usize]
            .adjacent
            .push((new_term, step));
        self.terms[new_term.0 as usize]
            .adjacent
            .push((old_term, step));
    }

    fn process_pending(&mut self) {
        while let Some(operation) = self.pending.pop() {
            // We can stop processing when we find a contradiction.
            if self.has_contradiction {
                break;
            }

            match operation {
                SemanticOperation::TermEquality(term1, term2, step) => {
                    self.set_terms_equal_once(term1, term2, step);
                }
                SemanticOperation::TermInequality(term1, term2, step) => {
                    self.set_terms_not_equal_once(term1, term2, step);
                }
                SemanticOperation::ClauseReduction(clause_id) => {
                    self.reduce_clause(clause_id);
                }
            }
        }
    }

    /// Reduces a clause by checking if any of its literals can be evaluated.
    fn reduce_clause(&mut self, clause_id: ClauseId) {
        // Taking the clause info. Don't forget to put it back.
        let Some(mut clause_info) = self.clauses[clause_id.0].take() else {
            return;
        };

        let mut literals = vec![];
        std::mem::swap(&mut clause_info.literals, &mut literals);
        for literal in literals {
            let left_group = self.get_group_id(literal.left);
            let right_group = self.get_group_id(literal.right);
            let sides_equal = if left_group == right_group {
                true
            } else {
                let left_info = self.get_group_info(left_group);
                if left_info.inequalities.contains_key(&right_group) {
                    false
                } else {
                    // We can't evaluate this literal. Put it back.
                    clause_info.literals.push(literal);
                    continue;
                }
            };
            if literal.positive == sides_equal {
                // This literal is true, so the whole clause is redundant.
                return;
            }
        }

        if clause_info.literals.len() >= 2 {
            // This clause is still valid. Put it back.
            self.clauses[clause_id.0] = Some(clause_info);
            return;
        }

        // This clause is toast, but now what?

        if clause_info.literals.len() == 1 {
            let literal = &clause_info.literals[0];
            if literal.positive {
                self.set_terms_equal(literal.left, literal.right, clause_info.step, None);
            } else {
                self.set_terms_not_equal(literal.left, literal.right, clause_info.step);
            }
        } else {
            self.has_contradiction = true;
        }
    }

    // Set two terms to be equal.
    // Doesn't repeat to find the logical closure.
    // For that, use identify_terms.
    fn set_terms_equal_once(&mut self, term1: TermId, term2: TermId, step: Option<RewriteStep>) {
        let group1 = self.get_group_id(term1);
        let group2 = self.get_group_id(term2);
        if group1 == group2 {
            // They already are equal
            return;
        }
        let info1 = self.get_group_info(group1);
        let info2 = self.get_group_info(group2);

        // Keep around the smaller number, as a tiebreak
        if (info1.heuristic_size(), group2) < (info2.heuristic_size(), group1) {
            self.remap_group(term1, group1, term2, group2, step)
        } else {
            self.remap_group(term2, group2, term1, group1, step)
        };
    }

    pub fn set_terms_equal(
        &mut self,
        term1: TermId,
        term2: TermId,
        pattern_id: StepId,
        inspiration_id: Option<StepId>,
    ) {
        let step = RewriteStep {
            pattern_id,
            inspiration_id,
        };
        self.pending
            .push(SemanticOperation::TermEquality(term1, term2, Some(step)));
        self.process_pending();
    }

    pub fn set_terms_not_equal(&mut self, term1: TermId, term2: TermId, step: StepId) {
        self.pending
            .push(SemanticOperation::TermInequality(term1, term2, step));
        self.process_pending();
    }

    // Set two terms to be not equal.
    // Doesn't repeat to find the logical closure.
    fn set_terms_not_equal_once(&mut self, term1: TermId, term2: TermId, step: StepId) {
        let group1 = self.get_group_id(term1);
        let group2 = self.get_group_id(term2);
        if group1 == group2 {
            self.has_contradiction = true;
            self.contradiction_info = Some((term1, term2, step));
            return;
        }

        let info1 = &mut self.groups[group1.0 as usize]
            .as_mut()
            .expect("group is remapped");
        if info1.inequalities.contains_key(&group2) {
            return;
        }
        info1.inequalities.insert(group2, (term1, term2, step));
        let info2 = &mut self.groups[group2.0 as usize]
            .as_mut()
            .expect("group is remapped");
        let prev = info2.inequalities.insert(group1, (term1, term2, step));
        if prev.is_some() {
            panic!("asymmetry in group inequalities");
        }
    }

    fn as_compound(&self, term: TermId) -> (TermId, &Vec<TermId>) {
        match &self.terms[term.0 as usize].decomp {
            Decomposition::Compound(head, args) => (*head, args),
            _ => panic!("not a compound"),
        }
    }

    // Gets a step of edges that demonstrate that term1 and term2 are equal.
    // The step is None if the edge is composite.
    // Panics if there is no path.
    fn get_path(&self, term1: TermId, term2: TermId) -> Vec<(TermId, TermId, Option<RewriteStep>)> {
        if term1 == term2 {
            return vec![];
        }

        // Find paths that lead to term2 from everywhere.
        // predecessor maps term_a -> (term_b, step) where the edge
        //   (term_a, term_b, step)
        // is the first edge to get to term2 from term_a.
        let mut next_edge = HashMap::new();

        let mut queue = vec![term2];
        'outer: loop {
            let term_b = queue.pop().expect("no path between terms");
            for (term_a, step) in &self.terms[term_b.0 as usize].adjacent {
                if next_edge.contains_key(term_a) {
                    // We already have a way to get from term_a to term2
                    continue;
                }
                next_edge.insert(*term_a, (term_b, *step));
                if *term_a == term1 {
                    break 'outer;
                }
                queue.push(*term_a);
            }
        }

        let mut answer = vec![];
        let mut term_a = term1;
        while term_a != term2 {
            let (term_b, step) = next_edge[&term_a];
            answer.push((term_a, term_b, step));
            term_a = term_b;
        }
        answer
    }

    // For every step from term1 to term2, show the rewritten subterms, as well as the
    // id of the rule that enabled it, if there is one.
    // This is "postorder" in the sense that we show a rewritten compound term after showing
    // the rewrites for the subterms.
    // The compound rewrites have a step id of None.
    // The rewritten subterms have a step id with the rule that they are based on.
    fn expand_steps(
        &self,
        term1: TermId,
        term2: TermId,
        output: &mut Vec<(Term, Term, RewriteStep)>,
    ) {
        if term1 == term2 {
            return;
        }
        let path = self.get_path(term1, term2);
        for (a_id, b_id, step) in path {
            if step.is_none() {
                // We have a compound relationship between a_id and b_id
                let (head_a, args_a) = self.as_compound(a_id);
                let (head_b, args_b) = self.as_compound(b_id);
                assert_eq!(args_a.len(), args_b.len());
                self.expand_steps(head_a, head_b, output);
                for (arg_a, arg_b) in args_a.iter().zip(args_b.iter()) {
                    self.expand_steps(*arg_a, *arg_b, output);
                }
            }

            let term_a = self.get_term(a_id);
            let term_b = self.get_term(b_id);

            if let Some(step) = step {
                output.push((term_a.clone(), term_b.clone(), step));
            }
        }
    }

    fn get_step_ids_helper(&self, term1: TermId, term2: TermId, output: &mut BTreeSet<StepId>) {
        if term1 == term2 {
            return;
        }
        let path = self.get_path(term1, term2);
        for (term_a, term_b, step) in path {
            match step {
                Some(step) => {
                    output.insert(step.pattern_id);
                }
                None => {
                    let (head_a, args_a) = self.as_compound(term_a);
                    let (head_b, args_b) = self.as_compound(term_b);
                    assert_eq!(args_a.len(), args_b.len());
                    self.get_step_ids_helper(head_a, head_b, output);
                    for (arg_a, arg_b) in args_a.iter().zip(args_b.iter()) {
                        self.get_step_ids_helper(*arg_a, *arg_b, output);
                    }
                }
            }
        }
    }

    /// Extract a list of steps ids that we used to prove that these two terms are equal.
    /// This does deduplicate.
    pub fn get_step_ids(&self, term1: TermId, term2: TermId) -> Vec<usize> {
        let mut answer = BTreeSet::new();
        self.get_step_ids_helper(term1, term2, &mut answer);
        answer.into_iter().map(|id| id.0).collect()
    }

    pub fn show_graph(&self) {
        println!("terms:");
        for (i, term_info) in self.terms.iter().enumerate() {
            println!("term {}, group {}: {}", i, term_info.group, term_info.term);
        }
        println!("compounds:");
        for compound in &self.compounds {
            if let Some(compound) = compound {
                println!("{}", compound);
            }
        }
    }

    // Checks that the group id has not been remapped
    fn validate_group_id(&self, group_id: GroupId) -> &GroupInfo {
        assert!(group_id < GroupId(self.groups.len() as u32));
        match &self.groups[group_id.0 as usize] {
            None => {
                panic!("group {} is remapped", group_id)
            }
            Some(info) => info,
        }
    }

    // Checks that this clause contains a term from this group.
    // It's also okay if the clause has ceased to exist, because we clean up lazily.
    fn check_clause_has_group(&self, clause_id: ClauseId, group_id: GroupId) {
        let Some(clause_info) = self.get_clause_info(clause_id) else {
            return;
        };
        for literal in &clause_info.literals {
            let left_group = self.get_group_id(literal.left);
            let right_group = self.get_group_id(literal.right);
            if left_group == group_id || right_group == group_id {
                return; // Found a term from the group
            }
        }
        panic!(
            "clause {} does not contain a term from group {}",
            clause_id, group_id
        );
    }

    /// Panics if it finds a consistency problem.
    pub fn validate(&self) {
        // Validation should only be called when there are no pending operations
        assert!(self.pending.is_empty(), "validate() called with {} pending operations", self.pending.len());
        for (term_id, term_info) in self.terms.iter().enumerate() {
            let info = self.validate_group_id(term_info.group);
            assert!(info.terms.contains(&TermId(term_id as u32)));
        }

        for (group_id, group_info) in self.groups.iter().enumerate() {
            let group_id = GroupId(group_id as u32);
            let group_info = match group_info {
                None => {
                    continue;
                }
                Some(info) => info,
            };
            for term_id in &group_info.terms {
                let term_group = self.terms[term_id.0 as usize].group;
                assert_eq!(term_group, group_id);
            }
            for compound_id in &group_info.compounds {
                let compound = &self.compounds[compound_id.0 as usize];
                let compound = match compound {
                    Some(compound) => compound,
                    None => continue,
                };
                assert!(compound.key.touches_group(group_id));
            }

            for (other_group_id, clause_ids) in &group_info.clauses {
                // The same clause ids should be stored in both direction
                let other_info = self.validate_group_id(*other_group_id);
                let alt_clause_ids = other_info.clauses.get(&group_id).unwrap();
                assert_eq!(clause_ids, alt_clause_ids);

                for clause_id in clause_ids {
                    self.check_clause_has_group(*clause_id, group_id);
                }
            }
        }

        for (compound_id, compound) in self.compounds.iter().enumerate() {
            let compound = match compound {
                Some(compound) => compound,
                None => continue,
            };
            let groups = compound.key.groups();
            for group in groups {
                let info = self.validate_group_id(group);
                assert!(info.compounds.contains(&CompoundId(compound_id as u32)));
            }
        }

        for (clause_id, clause_info) in self.clauses.iter().enumerate() {
            let clause_id = ClauseId(clause_id);
            let Some(clause_info) = clause_info else {
                continue;
            };
            assert!(clause_info.literals.len() > 1);
            for literal in &clause_info.literals {
                let left_group = self.get_group_id(literal.left);
                let right_group = self.get_group_id(literal.right);

                let left_info = self.validate_group_id(left_group);
                let clause_ids = left_info.clauses.get(&right_group).unwrap();
                assert!(clause_ids.contains(&clause_id));

                let right_info = self.validate_group_id(right_group);
                let clause_ids = right_info.clauses.get(&left_group).unwrap();
                assert!(clause_ids.contains(&clause_id));
            }
        }
    }
}

// Methods for testing.
impl TermGraph {
    #[cfg(test)]
    fn insert_term_str(&mut self, s: &str) -> TermId {
        let id = self.insert_term(&Term::parse(s));
        self.validate();
        id
    }

    #[cfg(test)]
    fn insert_clause_str(&mut self, s: &str, step: StepId) {
        use crate::clause::Clause;
        let clause = Clause::parse(s);
        self.insert_clause(&clause, step);
        self.validate();
    }

    #[cfg(test)]
    fn assert_eq(&self, t1: TermId, t2: TermId) {
        assert_eq!(self.get_group_id(t1), self.get_group_id(t2));
    }

    #[cfg(test)]
    fn set_eq(&mut self, t1: TermId, t2: TermId, pattern_id: StepId) {
        self.set_terms_equal(t1, t2, pattern_id, None);
        self.validate();
        self.assert_eq(t1, t2);
    }

    #[cfg(test)]
    fn assert_ne(&self, t1: TermId, t2: TermId) {
        assert_ne!(self.get_group_id(t1), self.get_group_id(t2));
    }

    #[cfg(test)]
    fn get_str(&self, s: &str) -> TermId {
        self.get_term_id(&Term::parse(s)).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_identifying_atomic_subterms() {
        let mut g = TermGraph::new();
        let id1 = g.insert_term_str("c1(c2, c3)");
        let id2 = g.insert_term_str("c1(c4, c3)");
        g.assert_ne(id1, id2);
        let c2id = g.get_str("c2");
        let c4id = g.get_str("c4");
        g.assert_ne(c2id, c4id);
        g.set_eq(c2id, c4id, StepId(0));
        g.assert_eq(id1, id2);
        assert_eq!(g.get_step_ids(id1, id2), vec![0]);
    }

    #[test]
    fn test_multilevel_cascade() {
        let mut g = TermGraph::new();
        let term1 = g.insert_term_str("c1(c2(c3, c4), c2(c4, c3))");
        let term2 = g.insert_term_str("c1(c5, c5)");
        g.assert_ne(term1, term2);
        let sub1 = g.insert_term_str("c2(c3, c3)");
        let sub2 = g.get_str("c5");
        g.assert_ne(sub1, sub2);
        g.set_eq(sub1, sub2, StepId(0));
        let c3 = g.get_str("c3");
        let c4 = g.get_str("c4");
        g.assert_ne(c3, c4);
        g.set_eq(c3, c4, StepId(1));
        g.assert_eq(term1, term2);
        assert_eq!(g.get_step_ids(term1, term2), vec![0, 1]);
    }

    #[test]
    fn test_identifying_heads() {
        let mut g = TermGraph::new();
        let id1 = g.insert_term_str("c1(c2, c3)");
        let id2 = g.insert_term_str("c4(c2, c3)");
        g.assert_ne(id1, id2);
        let c1 = g.get_str("c1");
        let c4 = g.get_str("c4");
        g.set_eq(c1, c4, StepId(0));
        g.assert_eq(id1, id2);
        assert_eq!(g.get_step_ids(id1, id2), vec![0]);
    }

    #[test]
    fn test_skipping_unneeded_steps() {
        let mut g = TermGraph::new();
        let c0 = g.insert_term_str("c0");
        let c1 = g.insert_term_str("c1");
        let c2 = g.insert_term_str("c2");
        let c3 = g.insert_term_str("c3");
        let c4 = g.insert_term_str("c4");
        let c5 = g.insert_term_str("c5");
        g.set_eq(c1, c2, StepId(0));
        g.set_eq(c4, c5, StepId(1));
        g.set_eq(c0, c1, StepId(2));
        g.set_eq(c3, c4, StepId(3));
        g.set_eq(c0, c3, StepId(4));
        g.show_graph();
        assert_eq!(g.get_step_ids(c0, c3), vec![4]);
    }

    #[test]
    fn test_finding_contradiction() {
        let mut g = TermGraph::new();
        let term1 = g.insert_term_str("c1(c2, c3)");
        let term2 = g.insert_term_str("c4(c5, c6)");
        g.set_terms_not_equal(term1, term2, StepId(0));
        assert!(!g.has_contradiction_trace());
        let c1 = g.get_str("c1");
        let c4 = g.get_str("c4");
        g.set_eq(c1, c4, StepId(1));
        assert!(!g.has_contradiction_trace());
        let c2 = g.get_str("c2");
        let c5 = g.get_str("c5");
        g.set_eq(c2, c5, StepId(2));
        assert!(!g.has_contradiction_trace());
        let c3 = g.get_str("c3");
        let c6 = g.get_str("c6");
        g.set_eq(c3, c6, StepId(3));
        assert!(g.has_contradiction_trace());
    }

    #[test]
    fn test_clause_reduction() {
        let mut g = TermGraph::new();
        g.insert_clause_str("c1 = c2 or c3 != c4 or c5 != c6", StepId(0));
        assert!(!g.has_contradiction);
        g.insert_clause_str("c1 != c2", StepId(1));
        assert!(!g.has_contradiction);
        g.insert_clause_str("c3 = c4", StepId(2));
        // assert!(!g.has_contradiction);
        // g.insert_clause_str("c5 = c6", StepId(3));
        // assert!(g.has_contradiction);
    }
}

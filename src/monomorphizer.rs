use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, ConstantInstance};
use crate::constant_map::ConstantKey;
use crate::fact::Fact;
use crate::proof_step::Truthiness;

// The type variables used in a generic fact, along with the types they map to.
// Can be a partial instantiation.
// If it isn't fully instantiated, the strings map to generic types.
// Should always be sorted by string, so that we have some canonical order.
#[derive(PartialEq, Eq, Clone)]
struct FactParams {
    params: Vec<(String, AcornType)>,
}

impl fmt::Display for FactParams {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, (name, t)) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{} => {}", name, t)?;
        }
        Ok(())
    }
}

impl FactParams {
    fn new(params: impl IntoIterator<Item = (String, AcornType)>) -> FactParams {
        let mut params: Vec<_> = params.into_iter().collect();
        assert!(!params.is_empty());
        params.sort();
        FactParams { params }
    }
}

// The instantiation of a constant.
// Ordered the same way as the constant's parameters.
#[derive(PartialEq, Eq, Clone)]
struct ConstantParams {
    params: Vec<AcornType>,
}

impl fmt::Display for ConstantParams {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, name) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", name)?;
        }
        Ok(())
    }
}

impl ConstantParams {
    fn new(params: Vec<AcornType>) -> ConstantParams {
        assert!(!params.is_empty());
        ConstantParams { params }
    }

    // Checks that this is a full instantiation, replacing all type variables.
    fn assert_full(&self) {
        for t in &self.params {
            if t.is_generic() {
                panic!("bad monomorphization: {}", self);
            }
        }
    }
}

// A helper structure to determine which monomorphs are necessary.
#[derive(Clone)]
pub struct Monomorphizer {
    // Facts that have some type variable in them.
    // The type variables aren't consistent between different facts.
    generic_facts: Vec<Fact>,

    // This works like an output buffer.
    // Each output fact is fully monomorphized.
    // The Monomorphizer only writes to this, never reads.
    output_facts: Vec<Fact>,

    // The parameters we have already used to monomorphize each fact.
    // Parallel to generic_facts.
    // So fact_params[i][j] has been used to monomorphize generic_facts[i].
    // Currently, all of these instantiations are monomorphizations, because
    // we don't handle the case where it requires matching multiple constants
    // to determine a useful monomorphization for a fact.
    // But we might do more than these "single-shot" monomorphizations in the future.
    instantiations_for_fact: Vec<Vec<FactParams>>,

    // The instantiations we have done for each constant.
    // Indexed by constant id.
    // Again, all of these instantiations are monomorphizations.
    instantiations_for_constant: HashMap<ConstantKey, Vec<ConstantParams>>,

    // An index tracking wherever a generic constant is instantiated in the generic facts.
    // This is updated whenever we add a generic fact.
    // Lists (index in generic_facts, instantiation for the constant) for each occurrence.
    // The types could have all sorts of generic variables; it's whatever was in the fact.
    generic_constants: HashMap<ConstantKey, Vec<(usize, ConstantParams)>>,
}

impl Monomorphizer {
    pub fn new() -> Monomorphizer {
        Monomorphizer {
            generic_facts: vec![],
            output_facts: vec![],
            instantiations_for_fact: vec![],
            instantiations_for_constant: HashMap::new(),
            generic_constants: HashMap::new(),
        }
    }

    // Adds a fact. It might or might not be generic.
    pub fn add_fact(&mut self, fact: Fact) {
        if fact.truthiness != Truthiness::Factual {
            // We don't match to global facts because that would combinatorially explode.
            self.add_monomorphs(&fact.value);
        }

        let i = self.generic_facts.len();
        let mut generic_constants = vec![];
        fact.value
            .find_constants(&|c| c.is_generic(), &mut generic_constants);
        if generic_constants.is_empty() {
            if let AcornValue::ForAll(args, _) = &fact.value {
                if args.iter().any(|arg| arg.is_generic()) {
                    // This is a generic fact with no generic functions.
                    // It could be something trivial and purely propositional, like
                    // forall(x: T) { x = x }
                    // Just skip it.
                    return;
                }
            }

            // The fact is already monomorphic. Just output it.
            self.output_facts.push(fact);
            return;
        }

        self.generic_facts.push(fact);
        self.instantiations_for_fact.push(vec![]);

        // Store a reference to our generic constants in the index
        for c in generic_constants.clone() {
            let key = c.key();
            let params = ConstantParams::new(c.params);
            self.generic_constants
                .entry(key)
                .or_insert(vec![])
                .push((i, params));
        }

        // Check how this new generic fact should be monomorphized
        for c in generic_constants {
            let key = c.key();
            let instance_params = ConstantParams::new(c.params);
            if let Some(monomorphs) = self.instantiations_for_constant.get(&key) {
                for monomorph_params in monomorphs.clone() {
                    self.try_to_monomorphize_fact(i, &monomorph_params, &instance_params);
                }
            }
        }
    }

    // Extract monomorphic facts from the prover.
    pub fn take_facts(&mut self) -> Vec<Fact> {
        std::mem::take(&mut self.output_facts)
    }

    // Call this on any value that we want to use in proofs.
    // Makes sure that we are generating any monomorphizations that are used in this value.
    pub fn add_monomorphs(&mut self, value: &AcornValue) {
        let mut monomorphs = vec![];
        value.find_constants(
            &|c| !c.params.is_empty() && !c.is_generic(),
            &mut monomorphs,
        );
        for c in monomorphs {
            self.monomorphize_matching_facts(&c);
        }
    }

    // Monomorphizes our facts to create this particular monomorphic constant wherever possible.
    // This is idempotent, because we only need to do each particular monomorphization once.
    fn monomorphize_matching_facts(&mut self, constant: &ConstantInstance) {
        let params = ConstantParams::new(constant.params.clone());
        params.assert_full();
        let monomorphs = self
            .instantiations_for_constant
            .entry(constant.key())
            .or_insert(vec![]);
        if monomorphs.contains(&params) {
            // We already have this monomorph
            return;
        }

        // This is a new monomorph. Add it to the list.
        monomorphs.push(params.clone());

        // For every fact that mentions this constant, try to monomorphize the fact to match it.
        if let Some(generic_constant) = self.generic_constants.get(&constant.key()) {
            for (fact_id, generic_params) in generic_constant.clone() {
                self.try_to_monomorphize_fact(fact_id, &generic_params, &params);
            }
        }
    }

    // Try to monomorphize the given fact to turn the generic params into the monomorph params.
    // The generic params are the way this constant is instantiated in the given fact.
    // The generic params do have to be generic.
    //
    // The monomorph params are how we would like to instantiate the constant.
    // It may or may not be possible to match them up.
    // For example, this may be a fact about foo<Bool, T>, and our goal
    // is saying something about foo<Nat, Nat>.
    // Then we can't match them up.
    fn try_to_monomorphize_fact(
        &mut self,
        fact_id: usize,
        generic_params: &ConstantParams,
        monomorph_params: &ConstantParams,
    ) {
        // Our goal is to find the "fact params", a way in which we can instantiate
        // the whole fact so that the instance params become the monomorph params.
        assert_eq!(generic_params.params.len(), monomorph_params.params.len());
        let mut fact_params = HashMap::new();
        for (generic_type, monomorph_type) in generic_params
            .params
            .iter()
            .zip(monomorph_params.params.iter())
        {
            generic_type.match_instance(monomorph_type, &mut fact_params);
        }
        let fact_params = FactParams::new(fact_params);

        if self.instantiations_for_fact[fact_id].contains(&fact_params) {
            // We already have this monomorph
            return;
        }

        let monomorphic_fact = self.generic_facts[fact_id].instantiate(&fact_params.params);
        if monomorphic_fact.value.is_generic() {
            // This is a little awkward. Completely monomorphizing this instance
            // still doesn't monomorphize the whole fact.
            // TODO: if we could handle partial monomorphizations, we would take some action here.
            return;
        }
        self.instantiations_for_fact[fact_id].push(fact_params);

        self.output_facts.push(monomorphic_fact);
    }
}

use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::constant_map::ConstantKey;
use crate::fact::Fact;
use crate::proof_step::Truthiness;

// A partial instantiation is a way to instantiate a generic type,
// which may or may not have all its type variables filled in.
#[derive(PartialEq, Eq, Hash, Clone)]
struct Instantiation {
    // The strings are the names of the generic types, relative to a particular fact or constant.
    // For facts, they are sorted. For constants, they are in the same order as in the definition.
    // The AcornType is whatever the generic type is instantiated to.
    // XXX: What about when it isn't instantiated yet?
    params: Vec<(String, AcornType)>,
}

impl fmt::Display for Instantiation {
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

impl Instantiation {
    fn new(params: Vec<(String, AcornType)>) -> Instantiation {
        assert!(!params.is_empty());
        Instantiation { params }
    }

    // Checks that this partial instantiation is a full instantiation, replacing all type variables.
    fn assert_full(&self) {
        for (name, t) in &self.params {
            if t.is_generic() {
                panic!("bad monomorphization: {} = {}", name, t);
            }
        }
    }
}

// A helper structure to determine which monomorphs are necessary.
#[derive(Clone)]
pub struct Monomorphizer {
    // Facts that have some type variable in them.
    generic_facts: Vec<Fact>,

    // Facts that are fully monomorphized.
    // This works like an output buffer.
    // The Monomorphizer only writes to this, never reads.
    monomorphic_facts: Vec<Fact>,

    // The instantiations that we have already created for each fact.
    // XXX: does this have the "identity instantiation"?
    // Parallel to generic_facts.
    instantiations_for_fact: Vec<Vec<Instantiation>>,

    // The instantiations we have done each constant.
    // Indexed by constant id.
    instantiations_for_constant: HashMap<ConstantKey, Vec<Instantiation>>,

    // An index tracking wherever a generic constant is used in the generic facts.
    // This is updated whenever we add a fact.
    // Lists (index in generic_facts, params for the constant) for each occurrence.
    generic_constants: HashMap<ConstantKey, Vec<(usize, Instantiation)>>,
}

impl Monomorphizer {
    pub fn new() -> Monomorphizer {
        Monomorphizer {
            generic_facts: vec![],
            monomorphic_facts: vec![],
            instantiations_for_fact: vec![],
            instantiations_for_constant: HashMap::new(),
            generic_constants: HashMap::new(),
        }
    }

    // Adds a fact. It might or might not be generic.
    pub fn add_fact(&mut self, fact: Fact) {
        if fact.truthiness != Truthiness::Factual {
            // We don't match to global facts because that would combinatorially explode.
            self.match_constants(&fact.value);
        }

        let i = self.generic_facts.len();
        let mut generic_constants = vec![];
        fact.value.find_generic_constants(&mut generic_constants);
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
            self.monomorphic_facts.push(fact);
            return;
        }

        self.generic_facts.push(fact);
        self.instantiations_for_fact.push(vec![]);

        // Store a reference to our generic constants in the index
        for (constant_key, params) in generic_constants.clone() {
            let params = Instantiation::new(params);
            self.generic_constants
                .entry(constant_key)
                .or_insert(vec![])
                .push((i, params));
        }

        // Check how this new generic fact should be monomorphized
        for (constant_key, params) in generic_constants {
            let instance_params = Instantiation::new(params);
            if let Some(monomorphs) = self.instantiations_for_constant.get(&constant_key) {
                for monomorph_params in monomorphs.clone() {
                    self.try_monomorphize(i, &monomorph_params, &instance_params);
                }
            }
        }
    }

    // Extract monomorphic facts from the prover.
    pub fn take_facts(&mut self) -> Vec<Fact> {
        std::mem::take(&mut self.monomorphic_facts)
    }

    // Make sure that we are generating any monomorphizations that are used in this value.
    pub fn match_constants(&mut self, value: &AcornValue) {
        let mut monomorphs = vec![];
        value.find_monomorphic_constants(&mut monomorphs);
        for (constant_key, params) in monomorphs {
            if params.is_empty() {
                continue;
            }
            self.monomorphize_constant(&constant_key, &Instantiation::new(params));
        }
    }

    // Monomorphizes a generic constant.
    // For every fact that uses this constant, we want to monomorphize the fact to use this
    // form of the generic constant.
    fn monomorphize_constant(
        &mut self,
        constant_key: &ConstantKey,
        monomorph_params: &Instantiation,
    ) {
        monomorph_params.assert_full();
        let monomorphs = self
            .instantiations_for_constant
            .entry(constant_key.clone())
            .or_insert(vec![]);
        if monomorphs.contains(&monomorph_params) {
            // We already have this monomorph
            return;
        }
        monomorphs.push(monomorph_params.clone());

        // Handle all the facts that mention this constant without monomorphizing it.
        if let Some(instances) = self.generic_constants.get(&constant_key) {
            for (fact_id, instance_params) in instances.clone() {
                self.try_monomorphize(fact_id, monomorph_params, &instance_params);
            }
        }
    }

    // Try to monomorphize the given fact so that the given params match.
    // The instance params are the way this constant is instantiated in the given fact.
    //
    // TODO: But shouldn't it depend on what the constant was?
    //
    // The monomorph params are how we would like to instantiate the constant.
    // It may or may not be possible to match them up.
    // For example, this may be a fact about foo<bool, T>, and our goal
    // is saying something about foo<Nat, Nat>.
    // Then we can't match them up.
    fn try_monomorphize(
        &mut self,
        fact_id: usize,
        monomorph_params: &Instantiation,
        instance_params: &Instantiation,
    ) {
        // Our goal is to find the "fact params", a way in which we can instantiate
        // the whole fact so that the instance params become the monomorph params.
        assert_eq!(instance_params.params.len(), monomorph_params.params.len());
        let mut fact_params = HashMap::new();
        for ((i_name, instance_type), (m_name, monomorph_type)) in instance_params
            .params
            .iter()
            .zip(monomorph_params.params.iter())
        {
            assert_eq!(i_name, m_name);
            instance_type.match_instance(monomorph_type, &mut fact_params);
        }

        // We sort because there's no inherently canonical order.
        let mut fact_params: Vec<_> = fact_params.into_iter().collect();
        fact_params.sort();
        let fact_params = Instantiation::new(fact_params);

        if self.instantiations_for_fact[fact_id].contains(&fact_params) {
            // We already have this monomorph
            return;
        }

        let monomorphic_fact = self.generic_facts[fact_id].instantiate(&fact_params.params);
        if monomorphic_fact.value.is_generic() {
            // This is a little awkward. Completely monomorphizing this instance
            // still doesn't monomorphize the whole fact.
            // TODO: instead of bailing out, partially monomorphize, and continue.
            return;
        }
        self.instantiations_for_fact[fact_id].push(fact_params);

        self.monomorphic_facts.push(monomorphic_fact);
    }
}

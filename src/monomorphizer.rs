use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::constant_map::ConstantKey;
use crate::fact::Fact;
use crate::proof_step::Truthiness;

// A parameter list corresponds to a monomorphization.
#[derive(PartialEq, Eq, Hash, Clone)]
struct ParamList {
    // Sorted
    params: Vec<(String, AcornType)>,
}

impl fmt::Display for ParamList {
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

impl ParamList {
    fn new(params: Vec<(String, AcornType)>) -> ParamList {
        ParamList { params }
    }

    fn assert_monomorph(&self) {
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
    // The Monomorphizer only writes to this, never reads.
    monomorphic_facts: Vec<Fact>,

    // The parameters we have already used to monomorphize each fact.
    // Parallel to generic_facts.
    monomorphs_for_fact: Vec<Vec<ParamList>>,

    // The parameters we have already used to monomorphize each constant.
    // Indexed by constant id.
    monomorphs_for_constant: HashMap<ConstantKey, Vec<ParamList>>,

    // An index tracking where each constant is used in the generic facts.
    // This is updated whenever we add a fact.
    // Lists (index in generic_facts, params for the constant) for each occurrence.
    generic_instances: HashMap<ConstantKey, Vec<(usize, ParamList)>>,
}

impl Monomorphizer {
    // Populates monomorphs_for_constant, and puts None vs Some([]) in the right place for
    // monomorphs_for_fact.
    pub fn new() -> Monomorphizer {
        Monomorphizer {
            generic_facts: vec![],
            monomorphic_facts: vec![],
            monomorphs_for_fact: vec![],
            monomorphs_for_constant: HashMap::new(),
            generic_instances: HashMap::new(),
        }
    }

    // Adds a fact. It might or might not be generic.
    pub fn add_fact(&mut self, fact: Fact) {
        if fact.truthiness != Truthiness::Factual {
            // We don't match to global facts because that would combinatorially explode.
            self.match_constants(&fact.value);
        }

        let i = self.generic_facts.len();
        let mut instances = vec![];
        fact.value.find_generic_constants(&mut instances);
        if instances.is_empty() {
            if let AcornValue::ForAll(args, _) = &fact.value {
                if args.iter().any(|arg| arg.is_generic()) {
                    // This is a generic fact with no generic functions.
                    // It could be something trivial and purely propositional, like
                    // forall(x: T) { x = x }
                    // Just skip it.
                    return;
                }
            }

            // There's nothing to monomorphize here. Just output it.
            self.monomorphic_facts.push(fact);
            return;
        }

        self.generic_facts.push(fact);
        self.monomorphs_for_fact.push(vec![]);

        // Store a reference to our generic instances in the index
        for (constant_key, params) in instances.clone() {
            let params = ParamList::new(params);
            self.generic_instances
                .entry(constant_key)
                .or_insert(vec![])
                .push((i, params));
        }

        // Check how this new generic fact should be monomorphized
        for (constant_key, params) in instances {
            let instance_params = ParamList::new(params);
            if let Some(monomorphs) = self.monomorphs_for_constant.get(&constant_key) {
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
            self.monomorphize_constant(&constant_key, &ParamList::new(params));
        }
    }

    // Monomorphizes a generic constant.
    // For every fact that uses this constant, we want to monomorphize the fact to use this
    // form of the generic constant.
    fn monomorphize_constant(&mut self, constant_key: &ConstantKey, monomorph_params: &ParamList) {
        monomorph_params.assert_monomorph();
        let monomorphs = self
            .monomorphs_for_constant
            .entry(constant_key.clone())
            .or_insert(vec![]);
        if monomorphs.contains(&monomorph_params) {
            // We already have this monomorph
            return;
        }
        monomorphs.push(monomorph_params.clone());

        // Handle all the facts that mention this constant without monomorphizing it.
        if let Some(instances) = self.generic_instances.get(&constant_key) {
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
        monomorph_params: &ParamList,
        instance_params: &ParamList,
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
        let fact_params = ParamList::new(fact_params);

        if self.monomorphs_for_fact[fact_id].contains(&fact_params) {
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
        self.monomorphs_for_fact[fact_id].push(fact_params);

        self.monomorphic_facts.push(monomorphic_fact);
    }
}

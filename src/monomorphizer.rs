use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::acorn_type::{AcornType, Class, Typeclass};
use crate::acorn_value::{AcornValue, ConstantInstance};
use crate::constant_name::GlobalConstantName;
use crate::fact::Fact;
use crate::proof_step::Truthiness;
use crate::proposition::Proposition;

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

// All the information that the monomorphizer tracks for a single generic fact.
#[derive(Clone)]
struct GenericFactInfo {
    // The fact itself.
    fact: Fact,

    // All of the instantiations that we have done for this fact.
    // Currently, all of these instantiations are monomorphizations.
    instantiations: Vec<FactParams>,
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
            if t.has_generic() {
                panic!("bad monomorphization: {}", self);
            }
        }
    }
}

// All the information that the monomorphizer tracks for a single generic constant.
#[derive(Clone)]
struct GenericConstantInfo {
    // All of the instantiations that we have done for this constant.
    // Currently, all of these instantiations are monomorphizations.
    instantiations: Vec<ConstantParams>,

    // There is one occurrence for every time a generic constant is used in a fact.
    // This is a list of (fact id, instantiation parameters for this constant).
    // The types could have all sorts of generic variables; it's whatever was in the fact.
    occurrences: Vec<(usize, ConstantParams)>,
}

impl GenericConstantInfo {
    fn new() -> GenericConstantInfo {
        GenericConstantInfo {
            instantiations: vec![],
            occurrences: vec![],
        }
    }
}

// A helper structure to determine which monomorphs are necessary.
#[derive(Clone)]
pub struct Monomorphizer {
    // The generic facts we have seen so far.
    // Generic facts implicitly get a "fact id" which is their index in this vector.
    fact_info: Vec<GenericFactInfo>,

    // This works like an output buffer.
    // Each output proposition is fully monomorphized.
    // The Monomorphizer only writes to this, never reads.
    output: Vec<(Proposition, Truthiness)>,

    // An index tracking wherever a generic constant is located in the generic facts.
    // This is updated whenever we add a generic fact.
    // Lists (fact id, instantiation for the constant) for each occurrence.
    constant_info: HashMap<GlobalConstantName, GenericConstantInfo>,

    // A set of all the instance relations we know about.
    // Monomorphization is only allowed with valid instance relations.
    instance_of: HashMap<Class, HashSet<Typeclass>>,
}

impl Monomorphizer {
    pub fn new() -> Monomorphizer {
        Monomorphizer {
            fact_info: vec![],
            output: vec![],
            constant_info: HashMap::new(),
            instance_of: HashMap::new(),
        }
    }

    pub fn add_instance_of(&mut self, class: Class, typeclass: Typeclass) {
        self.instance_of
            .entry(class)
            .or_insert_with(HashSet::new)
            .insert(typeclass);
    }

    // TODO: unpublicize
    pub fn is_instance_of(&self, class: &Class, typeclass: &Typeclass) -> bool {
        if let Some(set) = self.instance_of.get(class) {
            set.contains(typeclass)
        } else {
            false
        }
    }

    // Adds a fact. It might or might not be generic.
    pub fn add_fact(&mut self, fact: Fact) {
        // We don't monomorphize to match constants in global facts, because it would blow up.
        if fact.truthiness != Truthiness::Factual {
            self.add_monomorphs(&fact.proposition.value);
        }

        let i = self.fact_info.len();
        let mut generic_constants = vec![];
        fact.proposition
            .value
            .find_constants(&|c| c.has_generic(), &mut generic_constants);
        if generic_constants.is_empty() {
            if let AcornValue::ForAll(args, _) = &fact.proposition.value {
                if args.iter().any(|arg| arg.has_generic()) {
                    // This is a generic fact with no generic constants in it.
                    // It could be something trivial and purely propositional, like
                    // forall(x: T) { x = x }
                    // Just skip it.
                    return;
                }
            }

            // The fact is already monomorphic. Just output it.
            self.output.push((fact.proposition, fact.truthiness));
            return;
        }

        self.fact_info.push(GenericFactInfo {
            fact,
            instantiations: vec![],
        });

        // Store a reference to our generic constants in the index
        for c in generic_constants.clone() {
            self.constant_info
                .entry(c.name)
                .or_insert_with(GenericConstantInfo::new)
                .occurrences
                .push((i, ConstantParams::new(c.params)));
        }

        // Check how this new generic fact should be monomorphized
        for c in generic_constants {
            let instance_params = ConstantParams::new(c.params);
            if let Some(info) = self.constant_info.get(&c.name) {
                for monomorph_params in info.instantiations.clone() {
                    self.try_to_monomorphize_fact(i, &monomorph_params, &instance_params);
                }
            }
        }
    }

    // Extract monomorphic facts from the prover.
    pub fn take_output(&mut self) -> Vec<(Proposition, Truthiness)> {
        std::mem::take(&mut self.output)
    }

    // Call this on any value that we want to use in proofs.
    // Makes sure that we are generating any monomorphizations that are used in this value.
    pub fn add_monomorphs(&mut self, value: &AcornValue) {
        let mut monomorphs = vec![];
        value.find_constants(
            &|c| !c.params.is_empty() && !c.has_generic(),
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
        let info = self
            .constant_info
            .entry(constant.name.clone())
            .or_insert_with(GenericConstantInfo::new);
        if info.instantiations.contains(&params) {
            // We already have this monomorph
            return;
        }

        // This is a new monomorph. Add it to the list.
        info.instantiations.push(params.clone());

        // For every fact that mentions this constant, try to monomorphize the fact to match it.
        if let Some(info) = self.constant_info.get(&constant.name) {
            for (fact_id, generic_params) in info.occurrences.clone() {
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
            generic_type.match_instance(monomorph_type, &|_, _| true, &mut fact_params);
        }
        let fact_params = FactParams::new(fact_params);
        let info = &mut self.fact_info[fact_id];
        if info.instantiations.contains(&fact_params) {
            // We already have this monomorph
            return;
        }

        let monomorphic_fact = info.fact.instantiate(&fact_params.params);
        if monomorphic_fact.proposition.value.has_generic() {
            // This is a little awkward. Completely monomorphizing this instance
            // still doesn't monomorphize the whole fact.
            // TODO: if we could handle partial monomorphizations, we would take some action here.
            return;
        }
        info.instantiations.push(fact_params);

        self.output
            .push((monomorphic_fact.proposition, monomorphic_fact.truthiness));
    }
}

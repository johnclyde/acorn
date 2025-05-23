use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::acorn_type::{AcornType, Class, Typeclass};
use crate::acorn_value::{AcornValue, ConstantInstance};
use crate::fact::Fact;
use crate::names::NameShim;
use crate::potential_value::PotentialValue;
use crate::proof_step::Truthiness;
use crate::proposition::{MonomorphicProposition, Proposition};
use crate::type_unifier::{self, TypeUnifier, TypeclassRegistry};

/// The type variables used in a generic proposition, along with the types they map to.
/// Can be a partial instantiation.
/// If it isn't fully instantiated, the strings map to generic types.
/// Should always be sorted by string, so that we have some canonical order.
#[derive(PartialEq, Eq, Clone)]
struct PropParams {
    params: Vec<(String, AcornType)>,
}

impl fmt::Display for PropParams {
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

impl PropParams {
    fn new(params: impl IntoIterator<Item = (String, AcornType)>) -> PropParams {
        let mut params: Vec<_> = params.into_iter().collect();
        assert!(!params.is_empty());
        params.sort();
        PropParams { params }
    }
}

/// All the information that the monomorphizer tracks for a single generic proposition.
#[derive(Clone)]
struct GenericPropInfo {
    /// A generic value that is true, along with information about where it came from.
    proposition: Proposition,

    /// All of the instantiations that we have done for this proposition.
    /// Currently, all of these instantiations are monomorphizations.
    instantiations: Vec<PropParams>,
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

    /// Checks that this is a full instantiation, replacing all type variables.
    fn assert_full(&self) {
        for t in &self.params {
            if t.has_generic() {
                panic!("bad monomorphization: {}", self);
            }
        }
    }
}

/// All the information that the monomorphizer tracks for a single generic constant.
#[derive(Clone)]
struct GenericConstantInfo {
    /// All of the instantiations that we have done for this constant.
    /// Currently, all of these instantiations are monomorphizations.
    instantiations: Vec<ConstantParams>,

    /// There is one occurrence for every time a generic constant is used in a proposition.
    /// This is a list of (prop id, instantiation parameters for this constant).
    /// The types could have all sorts of generic variables; it's whatever was in the proposition.
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

///
#[derive(Clone)]
struct InstantiationFailure {
    prop_id: usize,
    generic_params: ConstantParams,
    monomorph_params: ConstantParams,
}

/// A helper structure to determine which monomorphs are necessary.
#[derive(Clone)]
pub struct Monomorphizer {
    /// The generic propositions we have seen so far.
    /// Generic props implicitly get a "prop id" which is their index in this vector.
    prop_info: Vec<GenericPropInfo>,

    /// This works like an output buffer.
    /// Each output proposition is fully monomorphized.
    /// The Monomorphizer only writes to this, never reads.
    output: Vec<MonomorphicProposition>,

    /// An index tracking wherever a generic constant is located in the generic props.
    /// This is updated whenever we add a generic prop.
    /// Lists (prop id, instantiation for the constant) for each occurrence.
    constant_info: HashMap<NameShim, GenericConstantInfo>,

    /// Extends maps each typeclass to the typeclasses it extends.
    /// This includes indirect extensions.
    extends: HashMap<Typeclass, HashSet<Typeclass>>,

    /// All the instance relations we know about.
    /// Monomorphization is only allowed with valid instance relations.
    instances: HashMap<Typeclass, HashSet<Class>>,

    /// When we call try_to_monomorphize_prop, and it fails, but just because a type doesn't match
    /// a typeclass, we put an entry here.
    /// Later, if we discover that the type is actually an instance of the typeclass,
    /// we can monomorphize the proposition.
    instantiation_failures: HashMap<(Class, Typeclass), Vec<InstantiationFailure>>,
}

impl Monomorphizer {
    pub fn new() -> Monomorphizer {
        Monomorphizer {
            prop_info: vec![],
            output: vec![],
            constant_info: HashMap::new(),
            extends: HashMap::new(),
            instances: HashMap::new(),
            instantiation_failures: HashMap::new(),
        }
    }

    fn unifier(&self) -> TypeUnifier {
        TypeUnifier::new(self)
    }

    fn add_instance_of(&mut self, class: Class, typeclass: Typeclass) {
        let key = (class, typeclass);
        let failures = self.instantiation_failures.remove(&key);
        let (class, typeclass) = key;

        self.instances
            .entry(typeclass)
            .or_insert_with(HashSet::new)
            .insert(class);

        // Check if we have any instantiation failures that can be resolved now.
        if let Some(failures) = failures {
            for failure in failures {
                self.try_to_monomorphize_prop(
                    failure.prop_id,
                    &failure.generic_params,
                    &failure.monomorph_params,
                );
            }
        }
    }

    fn add_extends(&mut self, tc: Typeclass, base_set: HashSet<Typeclass>) {
        match self.extends.entry(tc) {
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(base_set);
            }
            std::collections::hash_map::Entry::Occupied(e) => {
                panic!(
                    "Adding extends to an already existing typeclass: {}",
                    e.key().name
                );
            }
        }
    }

    // Adds a fact. It might or might not be generic.
    pub fn add_fact(&mut self, fact: Fact) {
        match fact {
            Fact::Proposition(proposition) => {
                self.add_proposition(proposition);
            }
            Fact::Extends(tc, base_set, _) => {
                self.add_extends(tc, base_set);
            }
            Fact::Instance(class, typeclass, _) => {
                self.add_instance_of(class, typeclass);
            }
            Fact::Definition(potential, definition, source) => {
                let (params, constant) = match potential {
                    PotentialValue::Unresolved(u) => (u.params.clone(), u.to_generic_value()),
                    PotentialValue::Resolved(c) => (vec![], c.clone()),
                };

                let claim = constant.inflate_function_definition(definition);
                let prop = Proposition::new(claim, params, source);
                self.add_proposition(prop);
            }
        }
    }

    fn add_proposition(&mut self, proposition: Proposition) {
        // We don't monomorphize to match constants in global facts, because it would blow up.
        if proposition.source.truthiness() != Truthiness::Factual {
            self.add_monomorphs(&proposition.value);
        }

        if let Some(mp) = proposition.as_monomorphic() {
            // This is already monomorphic. Just add it to the output.
            self.output.push(mp);
            return;
        }

        let mut generic_constants = vec![];
        proposition
            .value
            .find_constants(&|c| c.has_generic(), &mut generic_constants);
        if generic_constants.is_empty() {
            // We can never instantiate this, anyway.
            return;
        }

        let i = self.prop_info.len();
        self.prop_info.push(GenericPropInfo {
            proposition,
            instantiations: vec![],
        });

        // Store a reference to our generic constants in the index
        for c in generic_constants.clone() {
            self.constant_info
                .entry(c.name_shim().clone())
                .or_insert_with(GenericConstantInfo::new)
                .occurrences
                .push((i, ConstantParams::new(c.params)));
        }

        // Check how this new generic proposition should be monomorphized
        for c in generic_constants {
            let c_name = c.name_shim().clone();
            let instance_params = ConstantParams::new(c.params);
            if let Some(info) = self.constant_info.get(&c_name) {
                for monomorph_params in info.instantiations.clone() {
                    self.try_to_monomorphize_prop(i, &monomorph_params, &instance_params);
                }
            }
        }
    }

    /// Extract monomorphic propositions from the prover.
    pub fn take_output(&mut self) -> Vec<MonomorphicProposition> {
        std::mem::take(&mut self.output)
    }

    /// Call this on any value that we want to use in proofs.
    /// Makes sure that we are generating any monomorphizations that are used in this value.
    fn add_monomorphs(&mut self, value: &AcornValue) {
        let mut monomorphs = vec![];
        value.find_constants(
            &|c| !c.params.is_empty() && !c.has_generic(),
            &mut monomorphs,
        );
        for c in monomorphs {
            self.monomorphize_matching_props(&c);
        }
    }

    /// Monomorphizes our props to create this particular monomorphic constant wherever possible.
    /// This is idempotent, because we only need to do each particular monomorphization once.
    fn monomorphize_matching_props(&mut self, constant: &ConstantInstance) {
        let params = ConstantParams::new(constant.params.clone());
        params.assert_full();
        let info = self
            .constant_info
            .entry(constant.name_shim().clone())
            .or_insert_with(GenericConstantInfo::new);
        if info.instantiations.contains(&params) {
            // We already have this monomorph
            return;
        }

        // This is a new monomorph. Add it to the list.
        info.instantiations.push(params.clone());

        // For every prop that mentions this constant, try to monomorphize the prop to match it.
        if let Some(info) = self.constant_info.get(&constant.name_shim()) {
            for (prop_id, generic_params) in info.occurrences.clone() {
                self.try_to_monomorphize_prop(prop_id, &generic_params, &params);
            }
        }
    }

    /// Try to monomorphize the given prop to turn the generic params into the monomorph params.
    /// The generic params are the way this constant is instantiated in the given prop.
    /// The generic params do have to be generic.
    ///
    /// The monomorph params are how we would like to instantiate the constant.
    /// It may or may not be possible to match them up.
    /// For example, this may be a proposition about foo<Bool, T>, and our goal
    /// is saying something about foo<Nat, Nat>.
    /// Then we can't match them up.
    fn try_to_monomorphize_prop(
        &mut self,
        prop_id: usize,
        generic_params: &ConstantParams,
        monomorph_params: &ConstantParams,
    ) {
        if generic_params.params.len() != self.prop_info[prop_id].proposition.params.len() {
            // We don't have enough parameters, based on this constant, to
            // monomorphize the whole proposition.
            // Just give up. In theory, maybe we could do something here.
            return;
        }

        // Our goal is to find the "prop params", a way in which we can instantiate
        // the whole proposition so that the instance params become the monomorph params.
        assert_eq!(generic_params.params.len(), monomorph_params.params.len());
        let mut unifier = self.unifier();
        for (generic_type, monomorph_type) in generic_params
            .params
            .iter()
            .zip(monomorph_params.params.iter())
        {
            match unifier.match_instance(generic_type, monomorph_type) {
                Ok(()) => {}
                Err(type_unifier::Error::Class(class, typeclass)) => {
                    // This is a failure based on a typeclass relation.
                    // We can try again later if we find out that the typeclass is valid.
                    let failure_key = (class, typeclass);
                    self.instantiation_failures
                        .entry(failure_key)
                        .or_insert_with(Vec::new)
                        .push(InstantiationFailure {
                            prop_id,
                            generic_params: generic_params.clone(),
                            monomorph_params: monomorph_params.clone(),
                        });
                    return;
                }
                Err(_) => {
                    // For this sort of error, there's no point in ever trying again.
                    return;
                }
            }
        }

        let prop_params = PropParams::new(unifier.mapping);
        let info = &mut self.prop_info[prop_id];
        if info.instantiations.contains(&prop_params) {
            // We already have this monomorph
            return;
        }

        let monomorphic_prop = info.proposition.instantiate(&prop_params.params);
        if monomorphic_prop.value.has_generic() {
            // This is a little awkward. Completely monomorphizing this instance
            // still doesn't monomorphize the whole proposition.
            // TODO: if we could handle partial monomorphizations, we would take some action here.
            return;
        }
        info.instantiations.push(prop_params);

        self.add_monomorphs(&monomorphic_prop.value);
        self.output.push(monomorphic_prop);
    }
}

impl TypeclassRegistry for Monomorphizer {
    fn is_instance_of(&self, class: &Class, typeclass: &Typeclass) -> bool {
        if let Some(set) = self.instances.get(typeclass) {
            set.contains(class)
        } else {
            false
        }
    }

    fn extends(&self, typeclass: &Typeclass, base: &Typeclass) -> bool {
        let Some(base_set) = self.extends.get(typeclass) else {
            return false;
        };
        base_set.contains(base)
    }
}

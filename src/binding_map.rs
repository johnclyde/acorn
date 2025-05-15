use core::panic;
use std::collections::{BTreeMap, HashMap, HashSet};

use tower_lsp::lsp_types::{CompletionItem, CompletionItemKind};

use crate::acorn_type::{AcornType, Class, PotentialType, TypeParam, Typeclass, UnresolvedType};
use crate::acorn_value::{AcornValue, BinaryOp};
use crate::code_gen_error::CodeGenError;
use crate::compilation::{self, ErrorSource, PanicOnError};
use crate::evaluator::Evaluator;
use crate::expression::{Declaration, Expression, Terminator, TypeParamExpr};
use crate::module::{Module, ModuleId};
use crate::named_entity::NamedEntity;
use crate::names::{DefinedName, GlobalName, InstanceName, LocalName};
use crate::potential_value::PotentialValue;
use crate::project::Project;
use crate::proposition::Proposition;
use crate::stack::Stack;
use crate::termination_checker::TerminationChecker;
use crate::token::{self, Token, TokenIter, TokenType};
use crate::type_unifier::{TypeUnifier, TypeclassRegistry};
use crate::unresolved_constant::UnresolvedConstant;

/// In order to convert an Expression to an AcornValue, we need to convert the string representation
/// of types, variable names, and constant names into numeric identifiers, detect name collisions,
/// and typecheck everything.
/// The BindingMap handles this. It does not handle Statements, just Expressions.
/// It does not have to be efficient enough to run in the inner loop of the prover.
#[derive(Clone)]
pub struct BindingMap {
    /// The module all these names are in.
    pub module_id: ModuleId,

    /// Maps the name of a constant defined in this scope to information about it.
    /// Doesn't handle variables defined on the stack, only ones that will be in scope for the
    /// entirety of this environment.
    /// This also includes aliases.
    pub constant_info: HashMap<LocalName, ConstantInfo>,

    /// Maps the name of a type to the type object.
    /// Includes unresolved names like List that don't have enough information
    /// to get a specific type.
    pub typename_to_type: BTreeMap<String, PotentialType>,

    /// Maps the type object to its name in this environment.
    pub type_to_typename: HashMap<PotentialType, String>,

    /// Stores information about every class accessible from this module.
    pub class_info: HashMap<Class, ClassInfo>,

    /// Maps the name of a typeclass to the typeclass.
    /// Includes typeclasses that were imported from other modules.
    name_to_typeclass: BTreeMap<String, Typeclass>,

    /// Stores information about every typeclass accessible from this module.
    pub typeclass_info: HashMap<Typeclass, TypeclassInfo>,

    /// A map whose keys are the unqualified constants in this module.
    /// Used for completion.
    unqualified: BTreeMap<String, ()>,

    /// Whenever a name from some other scope has a local alias in this one,
    /// if we're generating code, we prefer to use the local name.
    /// This contains constants, types, and typenames.
    /// For this reason, canonical_to_alias maps the global name to the preferred local alias.
    pub canonical_to_alias: HashMap<GlobalName, String>,

    /// Names that refer to other modules.
    /// After "import foo", "foo" refers to a module.
    /// It's important that these are in alphabetical order, so that dependency hashes are consistent.
    pub name_to_module: BTreeMap<String, ModuleId>,

    /// The local name for imported modules.
    pub module_to_name: HashMap<ModuleId, String>,

    /// The default data type to use for numeric literals.
    pub numerals: Option<Class>,

    /// The definitions of the instance attributes defined in this module.
    /// Alias-type definitions are stored here just like anything else, because the monomorphizer
    /// is going to need to see them in their parametrized form.
    instance_definitions: HashMap<InstanceName, AcornValue>,
}

/// Information about a class that is accessible from this module.
#[derive(Clone, Debug)]
pub struct ClassInfo {
    /// What module defines each of the attributes of this class.
    pub attributes: BTreeMap<String, ModuleId>,

    /// Maps typeclasses this class is an instance of to the module with the instance statement.
    typeclasses: HashMap<Typeclass, ModuleId>,
}

impl ClassInfo {
    fn new() -> Self {
        ClassInfo {
            attributes: BTreeMap::new(),
            typeclasses: HashMap::new(),
        }
    }

    fn import(
        &mut self,
        info: &ClassInfo,
        typename: &str,
        source: &dyn ErrorSource,
    ) -> compilation::Result<()> {
        for (attr, other_module_id) in info.attributes.iter() {
            match self.attributes.get(attr) {
                None => {
                    self.attributes.insert(attr.clone(), *other_module_id);
                }
                Some(module_id) => {
                    if *module_id != *other_module_id {
                        return Err(source.error(&format!(
                            "attribute {}.{} is defined in two different modules",
                            typename, attr
                        )));
                    }
                }
            }
        }
        for (typeclass, other_module_id) in info.typeclasses.iter() {
            if let Some(module_id) = self.typeclasses.insert(typeclass.clone(), *other_module_id) {
                if module_id != *other_module_id {
                    return Err(source.error(&format!(
                        "instance relation {}: {} is defined in two different modules",
                        typename, typeclass.name
                    )));
                }
            }
        }
        Ok(())
    }
}

/// Information about a typeclass that is defined in this module.
#[derive(Clone, Debug)]
pub struct TypeclassInfo {
    /// The attributes available to this typeclass.
    /// The value stores the typeclass on which this attribute was originally defined.
    /// (This can be the typeclass itself.)
    pub attributes: BTreeMap<String, Typeclass>,

    /// The typeclasses that this typeclass extends.
    extends: HashSet<Typeclass>,
}

impl TypeclassInfo {
    pub fn new() -> Self {
        TypeclassInfo {
            attributes: BTreeMap::new(),
            extends: HashSet::new(),
        }
    }
}

/// Information that the BindingMap stores about a constant.
#[derive(Clone)]
pub struct ConstantInfo {
    /// The value for this constant. Not the definition, but the constant itself.
    /// If this is a generic constant, this value is unresolved.
    value: PotentialValue,

    /// The definition of this constant, if it has one.
    /// Not included for aliases.
    definition: Option<AcornValue>,

    /// Whether this is the canonical name for a constant, as opposed to an alias or an import.
    canonical: bool,

    /// Whether this is a theorem.
    theorem: bool,

    /// If this constant is a constructor and this is its canonical name, store:
    ///   the class it constructs
    ///   an index of which constructor it is
    ///   how many total constructors there are
    /// Not included for aliases.
    pub constructor: Option<(Class, usize, usize)>,
}

fn keys_with_prefix<'a, T>(
    map: &'a BTreeMap<String, T>,
    prefix: &'a str,
) -> impl Iterator<Item = &'a String> {
    map.range(prefix.to_string()..)
        .take_while(move |(key, _)| key.starts_with(prefix))
        .map(|(key, _)| key)
}

impl BindingMap {
    pub fn new(module: ModuleId) -> Self {
        assert!(module >= Module::FIRST_NORMAL);
        let mut answer = BindingMap {
            module_id: module,
            constant_info: HashMap::new(),
            typename_to_type: BTreeMap::new(),
            type_to_typename: HashMap::new(),
            name_to_typeclass: BTreeMap::new(),
            typeclass_info: HashMap::new(),
            unqualified: BTreeMap::new(),
            canonical_to_alias: HashMap::new(),
            name_to_module: BTreeMap::new(),
            module_to_name: HashMap::new(),
            numerals: None,
            instance_definitions: HashMap::new(),
            class_info: HashMap::new(),
        };
        answer.add_type_alias("Bool", PotentialType::Resolved(AcornType::Bool));
        answer
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Simple helper functions.
    ////////////////////////////////////////////////////////////////////////////////

    pub fn local_name_in_use(&self, local_name: &LocalName) -> bool {
        if self.constant_info.contains_key(local_name) {
            return true;
        }
        match local_name {
            LocalName::Unqualified(word) => {
                self.unqualified.contains_key(word) || self.name_to_module.contains_key(word)
            }
            LocalName::Attribute(receiver, attr) => {
                if let Some(t) = self.typename_to_type.get(receiver) {
                    if let Some(class) = t.as_base_class() {
                        return self.has_type_attribute(class, attr);
                    }
                }
                false
            }
        }
    }

    pub fn check_local_name_available(
        &self,
        local_name: &LocalName,
        source: &dyn ErrorSource,
    ) -> compilation::Result<()> {
        if self.local_name_in_use(local_name) {
            return Err(source.error(&format!("local name {} is already in use", local_name)));
        }
        Ok(())
    }

    pub fn constant_name_in_use(&self, name: &DefinedName) -> bool {
        match name {
            DefinedName::Local(local_name) => self.local_name_in_use(local_name),
            DefinedName::Instance(instance_name) => {
                self.instance_definitions.contains_key(instance_name)
            }
        }
    }

    /// Checks against names for both types and typeclasses because they can conflict.
    pub fn check_typename_available(
        &self,
        name: &str,
        source: &dyn ErrorSource,
    ) -> compilation::Result<()> {
        if self.typename_to_type.contains_key(name) || self.name_to_typeclass.contains_key(name) {
            return Err(source.error(&format!("typename {} is already in use", name)));
        }
        Ok(())
    }

    /// Returns an error if this name is already in use.
    pub fn check_unqualified_name_available(
        &self,
        name: &str,
        source: &dyn ErrorSource,
    ) -> compilation::Result<()> {
        self.check_local_name_available(&LocalName::unqualified(name), source)
    }

    /// Adds both directions for a name <-> type correspondence.
    /// Panics if the name is already bound.
    fn insert_type_name(&mut self, name: String, potential_type: PotentialType) {
        // There can be multiple names for a type.
        // If we already have a name for the reverse lookup, we don't overwrite it.
        if !self.type_to_typename.contains_key(&potential_type) {
            self.type_to_typename
                .insert(potential_type.clone(), name.clone());
        }

        match self.typename_to_type.entry(name) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(potential_type);
            }
            std::collections::btree_map::Entry::Occupied(entry) => {
                panic!("typename {} already bound", entry.key());
            }
        }
    }

    /// Adds a new data type to the binding map.
    /// Panics if the name is already bound.
    pub fn add_data_type(&mut self, name: &str) -> AcornType {
        let class = Class {
            module_id: self.module_id,
            name: name.to_string(),
        };
        let t = AcornType::Data(class, vec![]);
        self.insert_type_name(name.to_string(), PotentialType::Resolved(t.clone()));
        t
    }

    /// Panics if the name is already bound.
    pub fn add_potential_type(
        &mut self,
        name: &str,
        params: Vec<Option<Typeclass>>,
    ) -> PotentialType {
        if params.len() == 0 {
            return PotentialType::Resolved(self.add_data_type(name));
        }
        let class = Class {
            module_id: self.module_id,
            name: name.to_string(),
        };
        let ut = UnresolvedType { class, params };
        let potential = PotentialType::Unresolved(ut);
        self.insert_type_name(name.to_string(), potential.clone());
        potential
    }

    /// Adds an arbitrary type to the binding map.
    /// This indicates a type parameter that is coming into scope.
    /// Panics if the param name is already bound.
    pub fn add_arbitrary_type(&mut self, param: TypeParam) -> AcornType {
        let name = param.name.to_string();
        let arbitrary_type = AcornType::Arbitrary(param);
        let potential = PotentialType::Resolved(arbitrary_type.clone());
        self.insert_type_name(name, potential);
        arbitrary_type
    }

    /// Adds a new type name that's an alias for an existing type.
    /// Bindings are the bindings that we are importing the type from.
    /// If the alias is a local one, bindings is None.
    /// Panics if the alias is already bound.
    pub fn add_type_alias(&mut self, alias: &str, potential: PotentialType) {
        // Local type aliases for concrete types should be preferred.
        if let PotentialType::Resolved(AcornType::Data(class, params)) = &potential {
            if params.is_empty() {
                let global_name =
                    GlobalName::new(class.module_id, LocalName::unqualified(&class.name));
                self.canonical_to_alias
                    .entry(global_name)
                    .or_insert(alias.to_string());
            }
        }

        // Local type aliases should also be preferred to the canonical name for
        // unresolved generic types.
        if let PotentialType::Unresolved(u) = &potential {
            let global_name =
                GlobalName::new(u.class.module_id, LocalName::unqualified(&u.class.name));
            self.canonical_to_alias
                .entry(global_name)
                .or_insert(alias.to_string());
        }

        self.insert_type_name(alias.to_string(), potential);
    }

    /// Adds a newly-defined typeclass to this environment.
    /// Panics if the typeclass is already defined - that should be checked before calling this.
    pub fn add_typeclass(
        &mut self,
        name: &str,
        extends: Vec<Typeclass>,
        project: &Project,
        source: &dyn ErrorSource,
    ) -> compilation::Result<()> {
        let mut info = TypeclassInfo::new();
        for base in extends {
            info.extends.insert(base.clone());
            let bindings = self.get_bindings(base.module_id, project);
            let base_info = bindings.typeclass_info.get(&base).unwrap();
            for base_base in &base_info.extends {
                if !info.extends.contains(base_base) {
                    info.extends.insert(base_base.clone());
                }
            }
            for (attr, original) in base_info.attributes.iter() {
                if let Some(current) = info.attributes.get(attr) {
                    if current != original {
                        return Err(source.error(&format!(
                            "attribute {} is defined in both {} and {}",
                            attr, &current.name, &original.name
                        )));
                    }
                } else {
                    info.attributes.insert(attr.clone(), original.clone());
                }
            }
        }

        let typeclass = Typeclass {
            module_id: self.module_id,
            name: name.to_string(),
        };
        match self.typeclass_info.entry(typeclass.clone()) {
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(info);
            }
            std::collections::hash_map::Entry::Occupied(entry) => {
                panic!("typeclass {} is already bound", entry.key().name);
            }
        }
        self.add_typeclass_name(&name, typeclass);
        Ok(())
    }

    /// Adds a local name for this typeclass.
    /// Panics if the name is already bound - that should be checked before calling this.
    fn add_typeclass_name(&mut self, name: &str, typeclass: Typeclass) {
        // There can be multiple names for a typeclass.
        // If we already have a name for the reverse lookup, we don't overwrite it.
        let canonical_name =
            GlobalName::new(typeclass.module_id, LocalName::unqualified(&typeclass.name));
        self.canonical_to_alias
            .entry(canonical_name)
            .or_insert(name.to_string());

        match self.name_to_typeclass.entry(name.to_string()) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(typeclass);
            }
            std::collections::btree_map::Entry::Occupied(entry) => {
                panic!("typeclass name {} is already bound", entry.key());
            }
        }
    }

    /// A helper to get the bindings from the project if needed bindings.
    pub fn get_bindings<'a>(&'a self, module_id: ModuleId, project: &'a Project) -> &'a BindingMap {
        if module_id == self.module_id {
            self
        } else {
            project.get_bindings(module_id).unwrap()
        }
    }

    pub fn get_typeclass_attributes<'a>(
        &'a self,
        typeclass: &Typeclass,
        project: &'a Project,
    ) -> &'a BTreeMap<String, Typeclass> {
        &self
            .get_bindings(typeclass.module_id, project)
            .typeclass_info
            .get(&typeclass)
            .unwrap()
            .attributes
    }

    /// Call this after an instance attribute has been defined to typecheck it.
    /// Returns (resolved typeclass attribute, defined instance attribute).
    /// The resolved typeclass attribute is like
    /// Ring.add<Int>
    /// and the defined instance attribute is the one that we defined, before
    /// proving that Int was actually a Ring.
    pub fn check_instance_attribute(
        &self,
        instance_type: &AcornType,
        typeclass: &Typeclass,
        attr_name: &str,
        project: &Project,
        source: &dyn ErrorSource,
    ) -> compilation::Result<(AcornValue, AcornValue)> {
        // Get the relevant properties of the typeclass.
        let typeclass_attr_name = DefinedName::attribute(&typeclass.name, attr_name);
        let typeclass_attr = self
            .get_bindings(typeclass.module_id, &project)
            .get_constant_value(&typeclass_attr_name, source)?;
        let uc = typeclass_attr.as_unresolved(source)?;
        let resolved_attr = uc.resolve(source, vec![instance_type.clone()])?;
        let resolved_attr_type = resolved_attr.get_type();

        // Get the relevant properties of the instance class.
        let instance_class = instance_type.get_class(source)?;
        let instance_attr_name =
            DefinedName::instance(typeclass.clone(), attr_name, instance_class.clone());
        let instance_attr = self.get_constant_value(&instance_attr_name, source)?;
        let instance_attr = instance_attr.as_value(source)?;
        let instance_attr_type = instance_attr.get_type();
        if instance_attr_type != resolved_attr_type {
            return Err(source.error(&format!(
                "type mismatch for attribute '{}': expected {}, found {}",
                attr_name, resolved_attr_type, instance_attr_type
            )));
        }
        Ok((resolved_attr, instance_attr))
    }

    pub fn add_instance_of(&mut self, class: Class, typeclass: Typeclass) {
        self.class_info
            .entry(class)
            .or_insert_with(ClassInfo::new)
            .typeclasses
            .insert(typeclass, self.module_id);
    }

    /// Returns a PotentialValue representing this name, if there is one.
    /// This can be either a resolved or unresolved value.
    /// This function assumes that you are calling the correct binding map.
    pub fn get_constant_value(
        &self,
        name: &DefinedName,
        source: &dyn ErrorSource,
    ) -> compilation::Result<PotentialValue> {
        match name {
            DefinedName::Local(local_name) => match self.constant_info.get(local_name) {
                Some(info) => Ok(info.value.clone()),
                None => Err(source.error(&format!("local constant {} not found", name))),
            },
            DefinedName::Instance(instance_name) => {
                let definition = self
                    .instance_definitions
                    .get(instance_name)
                    .ok_or_else(|| {
                        source.error(&format!("instance constant {} not found", name))
                    })?;
                let value =
                    AcornValue::instance_constant(instance_name.clone(), definition.get_type());
                Ok(PotentialValue::Resolved(value))
            }
        }
    }

    /// Gets the type for a type name, not for an identifier.
    pub fn get_type_for_typename(&self, type_name: &str) -> Option<&PotentialType> {
        self.typename_to_type.get(type_name)
    }

    pub fn has_typename(&self, type_name: &str) -> bool {
        self.typename_to_type.contains_key(type_name)
    }

    pub fn get_typeclass_for_name(&self, typeclass_name: &str) -> Option<&Typeclass> {
        self.name_to_typeclass.get(typeclass_name)
    }

    pub fn has_typeclass_name(&self, typeclass_name: &str) -> bool {
        self.name_to_typeclass.contains_key(typeclass_name)
    }

    /// Just use this for testing.
    pub fn has_constant_name(&self, name: &str) -> bool {
        let name = LocalName::guess(name);
        self.constant_info.contains_key(&name)
    }

    /// Returns the defined value, if there is a defined value.
    /// If there isn't, returns None.
    pub fn get_definition(&self, name: &DefinedName) -> Option<&AcornValue> {
        match name {
            DefinedName::Local(local_name) => {
                self.constant_info.get(local_name)?.definition.as_ref()
            }
            DefinedName::Instance(instance_name) => self.instance_definitions.get(instance_name),
        }
    }

    /// Returns the defined value and its parameters in their canonical order.
    /// Returns None if there is no definition.
    pub fn get_definition_and_params(
        &self,
        local_name: &LocalName,
    ) -> Option<(&AcornValue, &[TypeParam])> {
        let info = self.constant_info.get(local_name)?;
        Some((info.definition.as_ref()?, info.value.unresolved_params()))
    }

    /// All other modules that we directly depend on, besides this one.
    /// Sorted by the name of the import, so that the order will be consistent.
    pub fn direct_dependencies(&self) -> Vec<ModuleId> {
        self.name_to_module.values().copied().collect()
    }

    pub fn set_numerals(&mut self, class: Class) {
        self.numerals = Some(class);
    }

    /// Adds a constant.
    /// Panics if the name is already bound.
    /// The type and definition can be generic. If so, the parameters must be listed in params.
    /// Don't call this for aliases, this doesn't handle aliases intelligently.
    /// Returns the value for the newly created constant.
    pub fn add_constant(
        &mut self,
        defined_name: DefinedName,
        params: Vec<TypeParam>,
        constant_type: AcornType,
        definition: Option<AcornValue>,
        constructor: Option<(Class, usize, usize)>,
    ) -> PotentialValue {
        match defined_name {
            DefinedName::Local(local_name) => {
                self.add_local_constant(local_name, params, constant_type, definition, constructor)
            }
            DefinedName::Instance(instance_name) => {
                let definition = definition.expect("instance must have a definition");
                if !params.is_empty() {
                    panic!("instance may not have parameters");
                }
                if constructor.is_some() {
                    panic!("instance may not be a constructor");
                }
                self.instance_definitions
                    .insert(instance_name.clone(), definition);
                let value = AcornValue::instance_constant(instance_name, constant_type);
                PotentialValue::Resolved(value)
            }
        }
    }

    /// Adds a constant where we already know it has a local name.
    pub fn add_local_constant(
        &mut self,
        local_name: LocalName,
        params: Vec<TypeParam>,
        constant_type: AcornType,
        definition: Option<AcornValue>,
        constructor: Option<(Class, usize, usize)>,
    ) -> PotentialValue {
        if let Some(definition) = &definition {
            if let Err(e) = definition.validate() {
                panic!("invalid definition for constant {}: {}", local_name, e);
            }
            if params.is_empty() && definition.has_generic() {
                panic!("there should not be generic types in non-parametrized definitions");
            }
            if !params.is_empty() && definition.has_arbitrary() {
                panic!("there should not be arbitrary types in parametrized definitions");
            }
        }
        let global_name = GlobalName::new(self.module_id, local_name.clone());

        let value = if params.is_empty() {
            if constant_type.has_generic() {
                panic!("there should not be generic types in non-parametrized constant types");
            }
            PotentialValue::Resolved(AcornValue::constant(global_name, vec![], constant_type))
        } else {
            if constant_type.has_arbitrary() {
                panic!("there should not be arbitrary types in parametrized constant types");
            }
            let global_name = GlobalName::new(self.module_id, local_name.clone());
            PotentialValue::Unresolved(UnresolvedConstant {
                name: global_name,
                params,
                generic_type: constant_type,
            })
        };

        // New constants start out not being theorems and are marked as a theorem later.
        let info = ConstantInfo {
            value: value.clone(),
            canonical: true,
            definition,
            theorem: false,
            constructor,
        };

        self.add_constant_info(local_name, info);
        value
    }

    /// Adds information for either a newly defined constant, or an alias.
    fn add_constant_info(&mut self, local_name: LocalName, info: ConstantInfo) {
        match &local_name {
            LocalName::Attribute(entity_name, attribute) => {
                if let Some(t) = self.typename_to_type.get(entity_name) {
                    if let Some(class) = t.as_base_class() {
                        // We are defining a new class attribute.
                        self.class_info
                            .entry(class.clone())
                            .or_insert_with(ClassInfo::new)
                            .attributes
                            .insert(attribute.clone(), self.module_id);
                    } else {
                        panic!("cannot figure out receiver: {:?}", t);
                    }
                } else {
                    let typeclass = Typeclass {
                        module_id: self.module_id,
                        name: entity_name.clone(),
                    };
                    self.typeclass_info
                        .entry(typeclass.clone())
                        .or_insert_with(TypeclassInfo::new)
                        .attributes
                        .insert(attribute.clone(), typeclass);
                }
            }
            LocalName::Unqualified(name) => {
                self.unqualified.insert(name.clone(), ());
            }
        }

        self.constant_info.insert(local_name, info);
    }

    /// Be really careful about this, it seems likely to break things.
    fn remove_constant(&mut self, local_name: &LocalName) {
        if let LocalName::Unqualified(word) = local_name {
            // Remove the unqualified name from the list of unqualified names.
            self.unqualified.remove(word);
        }
        self.constant_info
            .remove(&local_name)
            .expect("constant name not in use");
    }

    /// Adds a local alias for an already-existing constant value.
    /// TODO: is aliasing theorems supposed to work?
    pub fn add_alias(
        &mut self,
        local_name: LocalName,
        global_name: GlobalName,
        value: PotentialValue,
    ) {
        if global_name.module_id != self.module_id {
            // Prefer this alias locally to using the qualified, canonical name
            self.canonical_to_alias
                .entry(global_name.clone())
                .or_insert(local_name.to_string());
        }
        let info = ConstantInfo {
            value,
            canonical: false,
            theorem: false,
            definition: None,
            constructor: None,
        };
        self.add_constant_info(local_name, info);
    }

    pub fn mark_as_theorem(&mut self, name: &LocalName) {
        self.constant_info
            .get_mut(&name)
            .expect("marking theorem that doesn't exist")
            .theorem = true;
    }

    pub fn is_theorem(&self, name: &LocalName) -> bool {
        self.constant_info
            .get(&name)
            .map_or(false, |info| info.theorem)
    }

    /// Type variables and arbitrary variables should get removed when they go out of scope.
    /// Other sorts of types shouldn't be getting removed.
    pub fn remove_type(&mut self, name: &str) {
        match self.typename_to_type.remove(name) {
            Some(p) => match &p {
                PotentialType::Unresolved(ut) => {
                    panic!("removing type {} which is unresolved", ut.class.name);
                }
                PotentialType::Resolved(t) => {
                    match &t {
                        AcornType::Variable(..) | AcornType::Arbitrary(..) => {}
                        _ => panic!("unexpectedly removing type: {}", name),
                    }
                    self.type_to_typename.remove(&p);
                }
            },
            None => panic!("removing type {} which is already not present", name),
        }
    }

    /// Adds this name to the environment as a module.
    /// Copies over all the class_info from the module's bindings.
    /// This enables "mixins".
    /// Also copy over all the typeclass_info from the module's bindings.
    pub fn import_module(
        &mut self,
        name: &str,
        bindings: &BindingMap,
        source: &dyn ErrorSource,
    ) -> compilation::Result<()> {
        if self
            .name_to_module
            .insert(name.to_string(), bindings.module_id)
            .is_some()
        {
            return Err(source.error(&format!("name {} is already bound", name)));
        }
        self.module_to_name
            .insert(bindings.module_id, name.to_string());

        // Copy over the class info.
        for (class, imported_info) in bindings.class_info.iter() {
            let entry = self
                .class_info
                .entry(class.clone())
                .or_insert_with(ClassInfo::new);
            entry.import(imported_info, &class.name, source)?;
        }

        // Copy over the typeclass info.
        for (typeclass, imported_info) in bindings.typeclass_info.iter() {
            if !self.typeclass_info.contains_key(typeclass) {
                self.typeclass_info
                    .insert(typeclass.clone(), imported_info.clone());
            }
        }
        Ok(())
    }

    pub fn is_module(&self, name: &str) -> bool {
        self.name_to_module.contains_key(name)
    }

    /// Whether this value is calling a theorem on some arguments.
    pub fn is_citation(&self, claim: &AcornValue, project: &Project) -> bool {
        match claim.is_named_function_call() {
            Some(global_name) => {
                let bindings = self.get_bindings(global_name.module_id, project);
                bindings.is_theorem(&global_name.local_name)
            }
            None => false,
        }
    }

    fn get_typeclass_attribute_completions(
        &self,
        typeclass: &Typeclass,
        prefix: &str,
        project: &Project,
    ) -> Option<Vec<CompletionItem>> {
        let mut answer = vec![];
        if let Some(info) = self
            .get_bindings(typeclass.module_id, project)
            .typeclass_info
            .get(typeclass)
        {
            for key in keys_with_prefix(&info.attributes, &prefix) {
                let completion = CompletionItem {
                    label: key.clone(),
                    kind: Some(CompletionItemKind::FIELD),
                    ..Default::default()
                };
                answer.push(completion);
            }
        }
        Some(answer)
    }

    /// Gets completions when we are typing a member name.
    fn get_type_attribute_completions(
        &self,
        t: &AcornType,
        prefix: &str,
    ) -> Option<Vec<CompletionItem>> {
        if let AcornType::Data(class, _) = t {
            let info = self.class_info.get(class)?;
            let mut answer = vec![];
            for key in keys_with_prefix(&info.attributes, prefix) {
                let completion = CompletionItem {
                    label: key.clone(),
                    kind: Some(CompletionItemKind::FIELD),
                    ..Default::default()
                };
                answer.push(completion);
            }
            Some(answer)
        } else {
            None
        }
    }

    /// The prefix is just of a single identifier.
    /// If importing is true, we are looking for names to import. This means that we don't
    /// want to suggest names unless this is the canonical location for them, and we don't
    /// want to suggest theorems.
    pub fn get_completions(
        &self,
        prefix: &str,
        importing: bool,
        project: &Project,
    ) -> Option<Vec<CompletionItem>> {
        if prefix.contains('.') {
            if importing {
                // Syntactically invalid
                return None;
            }
            let mut name_chain = prefix.split('.').collect::<Vec<&str>>();
            let partial = name_chain.pop()?;
            let namespace = Evaluator::new(self, project).evaluate_name_chain(&name_chain)?;
            match namespace {
                NamedEntity::Module(module) => {
                    let bindings = project.get_bindings(module)?;
                    return bindings.get_completions(partial, true, project);
                }
                NamedEntity::Type(t) => {
                    return self.get_type_attribute_completions(&t, partial);
                }
                NamedEntity::Value(v) => {
                    let t = v.get_type();
                    return self.get_type_attribute_completions(&t, partial);
                }
                NamedEntity::Typeclass(tc) => {
                    return self.get_typeclass_attribute_completions(&tc, partial, project);
                }
                NamedEntity::UnresolvedValue(u) => {
                    return self.get_type_attribute_completions(&u.generic_type, partial);
                }
                NamedEntity::UnresolvedType(ut) => {
                    let display_type = ut.to_display_type();
                    return self.get_type_attribute_completions(&display_type, partial);
                }
            }
        }

        let first_char = prefix.chars().next();
        let mut answer = vec![];

        if first_char.map(|c| c.is_lowercase()).unwrap_or(true) {
            // Keywords
            if !importing {
                for key in token::keywords_with_prefix(prefix) {
                    let completion = CompletionItem {
                        label: key.to_string(),
                        kind: Some(CompletionItemKind::KEYWORD),
                        ..Default::default()
                    };
                    answer.push(completion);
                }
            }
            // Constants
            for key in keys_with_prefix(&self.unqualified, prefix) {
                if key.contains('.') {
                    continue;
                }
                let name = LocalName::unqualified(key);
                if importing {
                    match self.constant_info.get(&name) {
                        Some(info) => {
                            if !info.canonical || info.theorem {
                                // Don't suggest aliases or theorems when importing
                                continue;
                            }
                        }
                        None => continue,
                    }
                }
                let completion = CompletionItem {
                    label: key.clone(),
                    kind: Some(CompletionItemKind::CONSTANT),
                    ..Default::default()
                };
                answer.push(completion);
            }
        }

        if first_char.map(|c| c.is_uppercase()).unwrap_or(true) {
            // Types
            for key in keys_with_prefix(&self.typename_to_type, prefix) {
                if importing {
                    let data_type = self.typename_to_type.get(key)?;
                    match data_type {
                        PotentialType::Resolved(AcornType::Data(class, _)) => {
                            if class.module_id != self.module_id || &class.name != key {
                                continue;
                            }
                        }
                        _ => continue,
                    }
                }
                let completion = CompletionItem {
                    label: key.clone(),
                    kind: Some(CompletionItemKind::CLASS),
                    ..Default::default()
                };
                answer.push(completion);
            }
        }

        Some(answer)
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for parsing Expressions and similar structures
    ////////////////////////////////////////////////////////////////////////////////

    /// Evaluates an expression that represents a type.
    pub fn evaluate_type(
        &self,
        project: &Project,
        expression: &Expression,
    ) -> compilation::Result<AcornType> {
        let potential = self.evaluate_potential_type(project, expression)?;
        match potential {
            PotentialType::Resolved(t) => Ok(t),
            PotentialType::Unresolved(ut) => {
                Err(expression.error(&format!("type {} is unresolved", ut.class.name)))
            }
        }
    }

    /// Evaluates an expression that either represents a type, or represents a type that still needs params.
    pub fn evaluate_potential_type(
        &self,
        project: &Project,
        expression: &Expression,
    ) -> compilation::Result<PotentialType> {
        match expression {
            Expression::Singleton(token) => {
                if token.token_type == TokenType::Axiom {
                    return Err(token.error("axiomatic types can only be created at the top level"));
                }
                if let Some(t) = self.typename_to_type.get(token.text()) {
                    Ok(t.clone())
                } else {
                    Err(token.error("expected type name"))
                }
            }
            Expression::Unary(token, _) => {
                Err(token.error("unexpected unary operator in type expression"))
            }
            Expression::Binary(left, token, right) => match token.token_type {
                TokenType::RightArrow => {
                    let arg_exprs = left.flatten_list(true)?;
                    let mut arg_types = vec![];
                    for arg_expr in arg_exprs {
                        arg_types.push(self.evaluate_type(project, arg_expr)?);
                    }
                    let return_type = self.evaluate_type(project, right)?;
                    Ok(PotentialType::Resolved(AcornType::functional(
                        arg_types,
                        return_type,
                    )))
                }
                TokenType::Dot => {
                    let entity = self.evaluate_entity(&mut Stack::new(), project, expression)?;
                    Ok(entity.expect_potential_type(token)?)
                }
                _ => Err(token.error("unexpected binary operator in type expression")),
            },
            Expression::Concatenation(left, params) => {
                let param_exprs = if let Expression::Grouping(opening, expr, _) = params.as_ref() {
                    if opening.token_type != TokenType::LessThan {
                        return Err(opening.error("expected '<' for type params"));
                    }
                    expr.flatten_comma_separated_list()
                } else {
                    return Err(params.error("expected type parameters in type application"));
                };
                let mut instance_params = vec![];
                for param_expr in param_exprs {
                    instance_params.push(self.evaluate_type(project, param_expr)?);
                }
                let p = self.evaluate_potential_type(project, left)?;
                let t = p.resolve(instance_params, expression)?;
                Ok(PotentialType::Resolved(t))
            }
            Expression::Grouping(_, e, _) => self.evaluate_potential_type(project, e),
            Expression::Binder(token, _, _, _) | Expression::IfThenElse(token, _, _, _, _) => {
                Err(token.error("unexpected token in type expression"))
            }
            Expression::Match(token, _, _, _) => {
                Err(token.error("unexpected match token in type expression"))
            }
        }
    }

    /// Evaluates a list of types.
    pub fn evaluate_type_list(
        &self,
        project: &Project,
        expression: &Expression,
        output: &mut Vec<AcornType>,
    ) -> compilation::Result<()> {
        match expression {
            Expression::Grouping(_, e, _) => self.evaluate_type_list(project, e, output),
            Expression::Binary(left, token, right) if token.token_type == TokenType::Comma => {
                self.evaluate_type_list(project, left, output)?;
                self.evaluate_type_list(project, right, output)
            }
            e => {
                output.push(self.evaluate_type(project, e)?);
                Ok(())
            }
        }
    }

    /// Evaluates a variable declaration in this context.
    /// "self" declarations should be handled externally.
    pub fn evaluate_declaration(
        &self,
        project: &Project,
        declaration: &Declaration,
    ) -> compilation::Result<(String, AcornType)> {
        match declaration {
            Declaration::Typed(name_token, type_expr) => {
                let acorn_type = self.evaluate_type(project, &type_expr)?;
                return Ok((name_token.to_string(), acorn_type));
            }
            Declaration::SelfToken(name_token) => {
                return Err(name_token.error("cannot use 'self' as an argument here"));
            }
        };
    }

    /// Parses a list of named argument declarations and adds them to the stack.
    /// class_type should be provided if these are the arguments of a new member function.
    pub fn bind_args<'a, I>(
        &self,
        stack: &mut Stack,
        project: &Project,
        declarations: I,
        class_type: Option<&AcornType>,
    ) -> compilation::Result<(Vec<String>, Vec<AcornType>)>
    where
        I: IntoIterator<Item = &'a Declaration>,
    {
        let mut names = Vec::new();
        let mut types = Vec::new();
        for (i, declaration) in declarations.into_iter().enumerate() {
            if class_type.is_some() && i == 0 {
                match declaration {
                    Declaration::SelfToken(_) => {
                        names.push("self".to_string());
                        types.push(class_type.unwrap().clone());
                        continue;
                    }
                    _ => {
                        return Err(declaration
                            .token()
                            .error("first argument of a member function must be 'self'"));
                    }
                }
            }
            let (name, acorn_type) = self.evaluate_declaration(project, declaration)?;
            self.check_unqualified_name_available(&name, declaration.token())?;
            if names.contains(&name) {
                return Err(declaration
                    .token()
                    .error("cannot declare a name twice in one argument list"));
            }
            names.push(name);
            types.push(acorn_type);
        }
        for (name, acorn_type) in names.iter().zip(types.iter()) {
            stack.insert(name.to_string(), acorn_type.clone());
        }
        Ok((names, types))
    }

    /// Errors if the value is not a constructor of the expected type.
    /// Returns the index of which constructor this is, and the total number of constructors.
    fn expect_constructor(
        &self,
        project: &Project,
        expected_type: &AcornType,
        value: &AcornValue,
        source: &dyn ErrorSource,
    ) -> compilation::Result<(usize, usize)> {
        let info = match value {
            AcornValue::Constant(ci) => {
                let bindings = self.get_bindings(ci.name.module_id, project);
                bindings.constant_info.get(&ci.name.local_name).unwrap()
            }
            _ => {
                return Err(source.error("invalid pattern"));
            }
        };
        match &info.constructor {
            Some((constructor_type, i, total)) => {
                expected_type.check_instance(constructor_type, source)?;
                Ok((*i, *total))
            }
            None => Err(source.error("expected a constructor")),
        }
    }

    /// Evaluates a pattern match. Infers their types from the pattern.
    /// Returns an error if the pattern is not a constructor of the expected type.
    /// Returns:
    ///   a value for the constructor function
    ///   a list of (name, type) pairs
    ///   the index of which constructor this is
    ///   the total number of constructors
    pub fn evaluate_pattern(
        &self,
        project: &Project,
        expected_type: &AcornType,
        pattern: &Expression,
    ) -> compilation::Result<(AcornValue, Vec<(String, AcornType)>, usize, usize)> {
        let (fn_exp, args) = match pattern {
            Expression::Concatenation(function, args) if !args.is_type() => (function, args),
            _ => {
                // This can only be a no-argument constructor.
                let constructor = self.evaluate_value(pattern, Some(expected_type), project)?;
                let (i, total) =
                    self.expect_constructor(project, expected_type, &constructor, pattern)?;
                return Ok((constructor, vec![], i, total));
            }
        };
        let potential_constructor =
            self.evaluate_potential_value(&mut Stack::new(), fn_exp, None, project)?;
        let constructor = match potential_constructor {
            PotentialValue::Resolved(v) => v,
            PotentialValue::Unresolved(uc) => {
                if let AcornType::Data(class, params) = expected_type {
                    if !uc.name.is_attribute_of(&class) {
                        return Err(pattern.error(&format!(
                            "pattern {} is not an attribute of {}",
                            &uc.name.local_name, class.name
                        )));
                    }
                    uc.resolve(pattern, params.clone())?
                } else {
                    return Err(pattern.error("unmatchable datatype?"));
                }
            }
        };
        let (i, total) = self.expect_constructor(project, expected_type, &constructor, pattern)?;
        let arg_types = match constructor.get_type() {
            AcornType::Function(f) => {
                if &*f.return_type != expected_type {
                    return Err(pattern.error(&format!(
                        "the pattern has type {} but we are matching type {}",
                        &*f.return_type, expected_type
                    )));
                }
                f.arg_types
            }
            _ => return Err(fn_exp.error("expected a function")),
        };
        let name_exps = args.flatten_list(false)?;
        if name_exps.len() != arg_types.len() {
            return Err(args.error(&format!(
                "expected {} arguments but got {}",
                arg_types.len(),
                name_exps.len()
            )));
        }
        let mut args = vec![];
        for (name_exp, arg_type) in name_exps.into_iter().zip(arg_types.into_iter()) {
            let name = match name_exp {
                Expression::Singleton(token) => token.text().to_string(),
                _ => return Err(name_exp.error("expected a simple name in pattern")),
            };
            self.check_unqualified_name_available(&name, name_exp)?;
            // Check if we already saw this name
            if args.iter().any(|(n, _)| n == &name) {
                return Err(name_exp.error(&format!(
                    "cannot use the name '{}' twice in one pattern",
                    name
                )));
            }
            args.push((name, arg_type))
        }
        Ok((constructor, args, i, total))
    }

    /// This function evaluates numbers when we already know what type they are.
    /// token is the token to report errors with.
    /// s is the string to parse.
    fn evaluate_number_with_class(
        &self,
        token: &Token,
        project: &Project,
        class: &Class,
        s: &str,
    ) -> compilation::Result<AcornValue> {
        if self.has_type_attribute(&class, s) {
            return self
                .evaluate_type_attribute(&class, s, project, token)?
                .as_value(token);
        }

        if s.len() == 1 {
            return Err(token.error(&format!("digit {}.{} is not defined", &class.name, s)));
        }

        let last_str = &s[s.len() - 1..];
        let last_num = self.evaluate_number_with_class(token, project, class, last_str)?;
        let initial_str = &s[..s.len() - 1];
        let initial_num = self.evaluate_number_with_class(token, project, class, initial_str)?;
        let read_fn = match self.evaluate_type_attribute(&class, "read", project, token)? {
            PotentialValue::Resolved(f) => f,
            PotentialValue::Unresolved(_) => {
                return Err(token.error(&format!(
                    "read function {}.read has unresolved type",
                    &class.name
                )))
            }
        };
        let value = AcornValue::apply(read_fn, vec![initial_num, last_num]);
        Ok(value)
    }

    /// Whether this type has this attribute in the current context.
    pub fn has_type_attribute(&self, class: &Class, var_name: &str) -> bool {
        self.class_info
            .get(class)
            .map_or(false, |info| info.attributes.contains_key(var_name))
    }

    /// Evaluates a name scoped by a type name, like Nat.range
    fn evaluate_type_attribute(
        &self,
        class: &Class,
        attr_name: &str,
        project: &Project,
        source: &dyn ErrorSource,
    ) -> compilation::Result<PotentialValue> {
        let module_id = self
            .class_info
            .get(class)
            .and_then(|info| info.attributes.get(attr_name))
            .ok_or_else(|| source.error("attribute not found"))?;
        let bindings = self.get_bindings(*module_id, project);
        let constant_name = DefinedName::attribute(&class.name, attr_name);
        bindings.get_constant_value(&constant_name, source)
    }

    /// Evalutes a name scoped by a typeclass name, like Group.foo
    fn evaluate_typeclass_attribute(
        &self,
        typeclass: &Typeclass,
        attr_name: &str,
        project: &Project,
        source: &dyn ErrorSource,
    ) -> compilation::Result<PotentialValue> {
        let bindings = self.get_bindings(typeclass.module_id, project);

        // Check if this attribute is an inherited one.
        // Note that if we are in the definition of typeclass conditions, there is no info yet.
        if let Some(info) = self.typeclass_info.get(&typeclass) {
            if let Some(base_tc) = info.attributes.get(attr_name) {
                if base_tc != typeclass {
                    return self.evaluate_typeclass_attribute(&base_tc, attr_name, project, source);
                }
            }
        }

        let constant_name = DefinedName::attribute(&typeclass.name, attr_name);
        bindings.get_constant_value(&constant_name, source)
    }

    /// Evaluates an expression that is supposed to describe a value, with an empty stack.
    pub fn evaluate_value(
        &self,
        expression: &Expression,
        expected_type: Option<&AcornType>,
        project: &Project,
    ) -> compilation::Result<AcornValue> {
        self.evaluate_value_with_stack(&mut Stack::new(), expression, expected_type, project)
    }

    /// Evaluates an attribute of a value, like foo.bar.
    /// token is used for reporting errors but may not correspond to anything in particular.
    fn evaluate_value_attribute(
        &self,
        receiver: AcornValue,
        attr_name: &str,
        project: &Project,
        source: &dyn ErrorSource,
    ) -> compilation::Result<AcornValue> {
        let base_type = receiver.get_type();

        let function = match &base_type {
            AcornType::Data(class, _) => {
                self.evaluate_type_attribute(class, attr_name, project, source)?
            }
            AcornType::Arbitrary(param) | AcornType::Variable(param) => {
                let typeclass = match &param.typeclass {
                    Some(t) => t,
                    None => {
                        return Err(source.error(&format!(
                            "unqualified type {} has no attributes",
                            param.name
                        )));
                    }
                };
                self.evaluate_typeclass_attribute(typeclass, attr_name, project, source)?
            }
            _ => {
                return Err(source.error(&format!(
                    "objects of type {:?} have no attributes",
                    base_type
                )));
            }
        };
        self.apply_potential(function, vec![receiver], None, source)
    }

    /// Evaluates a single name, which may be namespaced to another named entity.
    /// In this situation, we don't know what sort of thing we expect the name to represent.
    /// We have the entity described by a chain of names, and we're adding one more name to the chain.
    fn evaluate_name(
        &self,
        name_token: &Token,
        project: &Project,
        stack: &Stack,
        namespace: Option<NamedEntity>,
    ) -> compilation::Result<NamedEntity> {
        let name = name_token.text();
        match namespace {
            Some(NamedEntity::Value(instance)) => {
                let value = self.evaluate_value_attribute(instance, name, project, name_token)?;
                Ok(NamedEntity::Value(value))
            }
            Some(NamedEntity::Type(t)) => {
                match &t {
                    AcornType::Data(class, params) => {
                        if name_token.token_type == TokenType::Numeral {
                            let value = self.evaluate_number_with_class(
                                name_token,
                                project,
                                &class,
                                name_token.text(),
                            )?;
                            return Ok(NamedEntity::Value(value));
                        }
                        match self.evaluate_type_attribute(class, name, project, name_token)? {
                            PotentialValue::Resolved(value) => {
                                if !params.is_empty() {
                                    return Err(
                                        name_token.error("unexpected double type resolution")
                                    );
                                }
                                Ok(NamedEntity::Value(value))
                            }
                            PotentialValue::Unresolved(u) => {
                                if params.is_empty() {
                                    // Leave it unresolved
                                    Ok(NamedEntity::UnresolvedValue(u))
                                } else {
                                    // Resolve it with the params from the class name
                                    let value = u.resolve(name_token, params.clone())?;
                                    Ok(NamedEntity::Value(value))
                                }
                            }
                        }
                    }
                    AcornType::Arbitrary(param) if param.typeclass.is_some() => {
                        let typeclass = param.typeclass.as_ref().unwrap();
                        match self
                            .evaluate_typeclass_attribute(&typeclass, name, project, name_token)?
                        {
                            PotentialValue::Resolved(value) => Ok(NamedEntity::Value(value)),
                            PotentialValue::Unresolved(u) => {
                                // Resolve it with the arbitrary type itself
                                let value = u.resolve(name_token, vec![t.clone()])?;
                                Ok(NamedEntity::Value(value))
                            }
                        }
                    }
                    _ => Err(name_token.error("this type cannot have attributes")),
                }
            }
            Some(NamedEntity::Module(module)) => {
                if let Some(bindings) = project.get_bindings(module) {
                    bindings.evaluate_name(name_token, project, stack, None)
                } else {
                    Err(name_token.error("could not load bindings for module"))
                }
            }
            Some(NamedEntity::Typeclass(tc)) => {
                match self.evaluate_typeclass_attribute(&tc, name, project, name_token)? {
                    PotentialValue::Resolved(value) => Ok(NamedEntity::Value(value)),
                    PotentialValue::Unresolved(u) => Ok(NamedEntity::UnresolvedValue(u)),
                }
            }
            Some(NamedEntity::UnresolvedValue(_)) => {
                Err(name_token.error("cannot access members of unresolved types"))
            }
            Some(NamedEntity::UnresolvedType(ut)) => {
                match self.evaluate_type_attribute(&ut.class, name, project, name_token)? {
                    PotentialValue::Resolved(value) => Ok(NamedEntity::Value(value)),
                    PotentialValue::Unresolved(u) => Ok(NamedEntity::UnresolvedValue(u)),
                }
            }
            None => {
                match name_token.token_type {
                    TokenType::Identifier => {
                        if self.is_module(name) {
                            match self.name_to_module.get(name) {
                                Some(module) => Ok(NamedEntity::Module(*module)),
                                None => Err(name_token.error("unknown module")),
                            }
                        } else if self.has_typename(name) {
                            match self.get_type_for_typename(name) {
                                Some(PotentialType::Resolved(t)) => {
                                    Ok(NamedEntity::Type(t.clone()))
                                }
                                Some(PotentialType::Unresolved(ut)) => {
                                    Ok(NamedEntity::UnresolvedType(ut.clone()))
                                }
                                _ => Err(name_token.error("unknown type")),
                            }
                        } else if self.has_typeclass_name(name) {
                            let tc = self.get_typeclass_for_name(name).unwrap();
                            Ok(NamedEntity::Typeclass(tc.clone()))
                        } else if let Some((i, t)) = stack.get(name) {
                            // This is a stack variable
                            Ok(NamedEntity::Value(AcornValue::Variable(*i, t.clone())))
                        } else {
                            let constant_name = DefinedName::unqualified(name);
                            Ok(NamedEntity::new(
                                self.get_constant_value(&constant_name, name_token)?,
                            ))
                        }
                    }
                    TokenType::Numeral => {
                        let class = match &self.numerals {
                            Some(c) => c,
                            None => {
                                return Err(name_token
                                    .error("you must set a default type for numeric literals"));
                            }
                        };
                        let value = self.evaluate_number_with_class(
                            name_token,
                            project,
                            class,
                            name_token.text(),
                        )?;
                        Ok(NamedEntity::Value(value))
                    }
                    TokenType::SelfToken => {
                        if let Some((i, t)) = stack.get(name) {
                            // This is a stack variable
                            Ok(NamedEntity::Value(AcornValue::Variable(*i, t.clone())))
                        } else {
                            Err(name_token.error("unexpected location for 'self'"))
                        }
                    }
                    t => Err(name_token.error(&format!("unexpected {:?} token", t))),
                }
            }
        }
    }

    /// Evaluates a single dot operator.
    fn evaluate_dot_expression(
        &self,
        stack: &mut Stack,
        project: &Project,
        left: &Expression,
        right: &Expression,
    ) -> compilation::Result<NamedEntity> {
        let right_token = match right {
            Expression::Singleton(token) => token,
            _ => return Err(right.error("expected an identifier after a dot")),
        };
        let left_entity = self.evaluate_entity(stack, project, left)?;
        self.evaluate_name(right_token, project, stack, Some(left_entity))
    }

    /// Evaluates an expression that could represent any sort of named entity.
    /// It could be a type, a value, or a module.
    fn evaluate_entity(
        &self,
        stack: &mut Stack,
        project: &Project,
        expression: &Expression,
    ) -> compilation::Result<NamedEntity> {
        // Handle a plain old name
        if let Expression::Singleton(token) = expression {
            return self.evaluate_name(token, project, stack, None);
        }

        // Dot expressions could be any sort of named entity
        if let Expression::Binary(left, token, right) = expression {
            if token.token_type == TokenType::Dot {
                return self.evaluate_dot_expression(stack, project, left, right);
            }
        }

        if expression.is_type() {
            let acorn_type = self.evaluate_type(project, expression)?;
            return Ok(NamedEntity::Type(acorn_type));
        }

        // If it isn't a name or a type, it must be a value.
        let value = self.evaluate_value_with_stack(stack, expression, None, project)?;
        Ok(NamedEntity::Value(value))
    }

    /// Evaluates an infix operator.
    /// name is the special alphanumeric name that corresponds to the operator, like "+" expands to "add".
    fn evaluate_infix(
        &self,
        stack: &mut Stack,
        project: &Project,
        expression: &Expression,
        left: &Expression,
        token: &Token,
        right: &Expression,
        name: &str,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<AcornValue> {
        let left_value = self.evaluate_value_with_stack(stack, left, None, project)?;
        let right_value = self.evaluate_value_with_stack(stack, right, None, project)?;

        // Get the partial application to the left
        let partial = self.evaluate_value_attribute(left_value, name, project, expression)?;
        let mut fa = match partial {
            AcornValue::Application(fa) => fa,
            _ => {
                return Err(expression.error(&format!(
                    "the '{}' operator requires a method named '{}'",
                    token, name
                )))
            }
        };
        match fa.function.get_type() {
            AcornType::Function(f) => {
                if f.arg_types.len() != 2 {
                    return Err(expression
                        .error(&format!("expected a binary function for '{}' method", name)));
                }
                right_value.check_type(Some(&f.arg_types[1]), expression)?;
            }
            _ => return Err(expression.error(&format!("unexpected type for '{}' method", name))),
        };

        fa.args.push(right_value);
        let value = AcornValue::apply(*fa.function, fa.args);
        value.check_type(expected_type, expression)?;
        Ok(value)
    }

    /// Imports a name from another module.
    /// The name could either be a type or a value.
    pub fn import_name(
        &mut self,
        project: &Project,
        module: ModuleId,
        name_token: &Token,
    ) -> compilation::Result<()> {
        let local_name = LocalName::unqualified(name_token.text());
        self.check_local_name_available(&local_name, name_token)?;
        let bindings = match project.get_bindings(module) {
            Some(b) => b,
            None => {
                return Err(
                    name_token.error(&format!("could not load bindings for imported module"))
                )
            }
        };
        let entity = bindings.evaluate_name(name_token, project, &Stack::new(), None)?;
        match entity {
            NamedEntity::Value(value) => {
                // Add a local alias that mirrors this constant's name in the imported module.
                if let Some(global_name) = value.as_simple_constant() {
                    self.add_alias(
                        local_name,
                        global_name.clone(),
                        PotentialValue::Resolved(value),
                    );
                    Ok(())
                } else {
                    // I don't see how this branch can be reached.
                    return Err(name_token.error("cannot import non-constant values"));
                }
            }
            NamedEntity::Type(acorn_type) => {
                self.add_type_alias(&name_token.text(), PotentialType::Resolved(acorn_type));
                Ok(())
            }
            NamedEntity::Module(_) => Err(name_token.error("cannot import modules indirectly")),
            NamedEntity::Typeclass(tc) => {
                self.add_typeclass_name(&name_token.text(), tc);
                Ok(())
            }

            NamedEntity::UnresolvedValue(uc) => {
                self.add_alias(local_name, uc.name.clone(), PotentialValue::Unresolved(uc));
                Ok(())
            }

            NamedEntity::UnresolvedType(u) => {
                self.add_type_alias(&name_token.text(), PotentialType::Unresolved(u));
                Ok(())
            }
        }
    }

    pub fn apply_potential(
        &self,
        potential: PotentialValue,
        args: Vec<AcornValue>,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorSource,
    ) -> compilation::Result<AcornValue> {
        let value = match potential {
            PotentialValue::Resolved(f) => f.check_apply(args, expected_type, source)?,
            PotentialValue::Unresolved(u) => {
                self.resolve_with_inference(u, args, expected_type, source)?
            }
        };
        Ok(value)
    }

    /// If we have an expected type and this is still a potential value, resolve it.
    pub fn maybe_resolve_value(
        &self,
        potential: PotentialValue,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorSource,
    ) -> compilation::Result<PotentialValue> {
        let expected_type = match expected_type {
            Some(t) => t,
            None => return Ok(potential),
        };
        let uc = match potential {
            PotentialValue::Unresolved(uc) => uc,
            p => return Ok(p),
        };
        let value = self.resolve_with_inference(uc, vec![], Some(expected_type), source)?;
        Ok(PotentialValue::Resolved(value))
    }

    /// Tries to match a generic type to a specific type, mapping the type variables.
    /// If it doesn't work, returns an error.
    /// If it does work, populates the unifier with the type variables.
    /// "what" is used for error reporting.
    fn match_instance(
        &self,
        unifier: &mut TypeUnifier,
        generic: &AcornType,
        specific: &AcornType,
        what: &str,
        source: &dyn ErrorSource,
    ) -> compilation::Result<()> {
        if !unifier.match_instance(generic, specific, self).is_ok() {
            return Err(source.error(&format!(
                "{} has type {} but we expected some sort of {}",
                what, specific, generic
            )));
        }
        Ok(())
    }

    /// Infer the type of an unresolved constant, based on its arguments (if it is a function)
    /// and the expected type.
    /// Returns a value that applies the function to the arguments.
    /// If the type cannot be inferred, returns an error.
    fn resolve_with_inference(
        &self,
        unresolved: UnresolvedConstant,
        args: Vec<AcornValue>,
        expected_return_type: Option<&AcornType>,
        source: &dyn ErrorSource,
    ) -> compilation::Result<AcornValue> {
        // Do type inference. Mapping is where the generic types go.
        let mut unifier = TypeUnifier::new();

        // Use the arguments to infer types
        let unresolved_return_type = if args.is_empty() {
            unresolved.generic_type.clone()
        } else if let AcornType::Function(unresolved_function_type) = &unresolved.generic_type {
            if unresolved_function_type.has_arbitrary() {
                return Err(source.error("unresolved function type has arbitrary"));
            }

            for (i, arg) in args.iter().enumerate() {
                if arg.has_generic() {
                    return Err(
                        source.error(&format!("argument {} ({}) has unresolved type", i, arg))
                    );
                }
                let arg_type: &AcornType = match &unresolved_function_type.arg_types.get(i) {
                    Some(t) => t,
                    None => {
                        return Err(source.error(&format!(
                            "expected {} arguments but got {}",
                            unresolved_function_type.arg_types.len(),
                            args.len()
                        )));
                    }
                };
                self.match_instance(
                    &mut unifier,
                    arg_type,
                    &arg.get_type(),
                    &format!("argument {}", i),
                    source,
                )?;
            }

            unresolved_function_type.applied_type(args.len())
        } else {
            return Err(source.error("expected a function type"));
        };

        if let Some(target_type) = expected_return_type {
            // Use the expected type to infer types
            self.match_instance(
                &mut unifier,
                &unresolved_return_type,
                target_type,
                "return value",
                source,
            )?;
        }

        // Determine the parameters for the instance
        let mut named_params = vec![];
        let mut instance_params = vec![];
        for param in &unresolved.params {
            match unifier.mapping.get(&param.name) {
                Some(t) => {
                    named_params.push((param.name.clone(), t.clone()));
                    instance_params.push(t.clone());
                }
                None => {
                    return Err(source.error(
                        "The arguments are insufficient to infer the type of this function. \
                        Try making its parameters explicit",
                    ));
                }
            }
        }

        // Resolve
        let instance_fn = unresolved.resolve(source, instance_params)?;
        let value = AcornValue::apply(instance_fn, args);
        value.check_type(expected_return_type, source)?;
        Ok(value)
    }

    /// Apply an unresolved name to arguments, inferring the types.
    pub fn infer_and_apply(
        &self,
        stack: &mut Stack,
        unresolved: UnresolvedConstant,
        arg_exprs: Vec<&Expression>,
        expected_type: Option<&AcornType>,
        project: &Project,
        source: &dyn ErrorSource,
    ) -> compilation::Result<AcornValue> {
        // Evaluate the arguments
        let mut args = vec![];
        for arg_expr in &arg_exprs {
            let arg = self.evaluate_value_with_stack(stack, arg_expr, None, project)?;
            args.push(arg);
        }

        self.resolve_with_inference(unresolved, args, expected_type, source)
    }

    /// This creates a version of a typeclass condition that is specialized to a particular
    /// class that isn't an instance of the typeclass.
    /// The *class* must be defined in this module. The typeclass may not be.
    ///
    /// We use this when we haven't proven that a type is an instance of a typeclass yet.
    /// So for example we can resolve:
    ///   Ring.add<T: Ring> -> Ring.add<Int>
    /// even though Int has not been proven to be an instance of Ring.
    ///
    /// TODO: does this work right for typeclasses outside this module?
    pub fn unsafe_instantiate_condition(
        &self,
        typeclass: &Typeclass,
        condition_name: &str,
        instance_type: &AcornType,
        project: &Project,
        source: &dyn ErrorSource,
    ) -> compilation::Result<AcornValue> {
        let tc_condition_name = LocalName::attribute(&typeclass.name, condition_name);
        let tc_bindings = self.get_bindings(typeclass.module_id, project);
        let (def, params) = match tc_bindings.get_definition_and_params(&tc_condition_name) {
            Some((def, params)) => (def, params),
            None => {
                return Err(source.error(&format!(
                    "could not find definition for typeclass condition {}",
                    tc_condition_name
                )));
            }
        };
        if params.len() != 1 {
            return Err(source.error(&format!(
                "typeclass condition {} should have one parameter",
                tc_condition_name
            )));
        }
        // We are explicitly instantiating in a way that would fail typechecking.
        let universal = match def.clone() {
            AcornValue::Lambda(args, val) => AcornValue::ForAll(args, val),
            v => v,
        };
        let unsafe_param = (params[0].name.clone(), instance_type.clone());
        let unsafe_instance = universal.instantiate(&[unsafe_param]);

        Ok(unsafe_instance)
    }

    /// Evaluates an expression that describes a value, with a stack given as context.
    /// This must resolve to a completed value, with all types inferred.
    pub fn evaluate_value_with_stack(
        &self,
        stack: &mut Stack,
        expression: &Expression,
        expected_type: Option<&AcornType>,
        project: &Project,
    ) -> compilation::Result<AcornValue> {
        let potential = self.evaluate_potential_value(stack, expression, expected_type, project)?;
        potential.as_value(expression)
    }

    /// Evaluates an expression that could describe a value, but could also describe
    /// a constant with an unresolved type.
    fn evaluate_potential_value(
        &self,
        stack: &mut Stack,
        expression: &Expression,
        expected_type: Option<&AcornType>,
        project: &Project,
    ) -> compilation::Result<PotentialValue> {
        let value = match expression {
            Expression::Singleton(token) => match token.token_type {
                TokenType::Axiom => panic!("axiomatic values should be handled elsewhere"),
                TokenType::ForAll | TokenType::Exists | TokenType::Function => {
                    return Err(token.error("binder keywords cannot be used as values"));
                }
                TokenType::True | TokenType::False => {
                    AcornType::Bool.check_eq(expected_type, token)?;
                    AcornValue::Bool(token.token_type == TokenType::True)
                }
                TokenType::Identifier | TokenType::Numeral | TokenType::SelfToken => {
                    let entity = self.evaluate_name(token, project, stack, None)?;
                    match entity {
                        NamedEntity::Value(value) => {
                            value.check_type(expected_type, expression)?;
                            value
                        }
                        NamedEntity::Type(_)
                        | NamedEntity::Module(_)
                        | NamedEntity::Typeclass(_)
                        | NamedEntity::UnresolvedType(_) => {
                            return Err(token.error("expected a value"));
                        }
                        NamedEntity::UnresolvedValue(u) => {
                            let potential = PotentialValue::Unresolved(u);
                            return self.maybe_resolve_value(potential, expected_type, token);
                        }
                    }
                }
                token_type => {
                    return Err(token.error(&format!(
                        "identifier expression has token type {:?}",
                        token_type
                    )))
                }
            },
            Expression::Unary(token, expr) => match token.token_type {
                TokenType::Not => {
                    AcornType::Bool.check_eq(expected_type, token)?;
                    let value = self.evaluate_value_with_stack(
                        stack,
                        expr,
                        Some(&AcornType::Bool),
                        project,
                    )?;
                    AcornValue::Not(Box::new(value))
                }
                token_type => match token_type.to_prefix_magic_method_name() {
                    Some(name) => {
                        let subvalue =
                            self.evaluate_value_with_stack(stack, expr, None, project)?;
                        let value =
                            self.evaluate_value_attribute(subvalue, name, project, token)?;
                        value.check_type(expected_type, token)?;
                        value
                    }
                    None => {
                        return Err(token.error("unexpected unary operator in value expression"))
                    }
                },
            },
            Expression::Binary(left, token, right) => match token.token_type {
                TokenType::RightArrow | TokenType::Implies => {
                    // We still allow right arrow in values for now, but eventually
                    // we should deprecate it.
                    // if token.token_type == TokenType::RightArrow {
                    //     return Err(token.error("RightArrow in values is deprecated"));
                    // }
                    AcornType::Bool.check_eq(expected_type, token)?;
                    let left_value = self.evaluate_value_with_stack(
                        stack,
                        left,
                        Some(&AcornType::Bool),
                        project,
                    )?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        right,
                        Some(&AcornType::Bool),
                        project,
                    )?;

                    AcornValue::Binary(
                        BinaryOp::Implies,
                        Box::new(left_value),
                        Box::new(right_value),
                    )
                }
                TokenType::Equals => {
                    AcornType::Bool.check_eq(expected_type, token)?;
                    let left_value = self.evaluate_value_with_stack(stack, left, None, project)?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        right,
                        Some(&left_value.get_type()),
                        project,
                    )?;
                    AcornValue::Binary(
                        BinaryOp::Equals,
                        Box::new(left_value),
                        Box::new(right_value),
                    )
                }
                TokenType::NotEquals => {
                    AcornType::Bool.check_eq(expected_type, token)?;
                    let left_value = self.evaluate_value_with_stack(stack, left, None, project)?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        right,
                        Some(&left_value.get_type()),
                        project,
                    )?;
                    AcornValue::Binary(
                        BinaryOp::NotEquals,
                        Box::new(left_value),
                        Box::new(right_value),
                    )
                }
                TokenType::And => {
                    AcornType::Bool.check_eq(expected_type, token)?;
                    let left_value = self.evaluate_value_with_stack(
                        stack,
                        left,
                        Some(&AcornType::Bool),
                        project,
                    )?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        right,
                        Some(&AcornType::Bool),
                        project,
                    )?;
                    AcornValue::Binary(BinaryOp::And, Box::new(left_value), Box::new(right_value))
                }
                TokenType::Or => {
                    AcornType::Bool.check_eq(expected_type, token)?;
                    let left_value = self.evaluate_value_with_stack(
                        stack,
                        left,
                        Some(&AcornType::Bool),
                        project,
                    )?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        right,
                        Some(&AcornType::Bool),
                        project,
                    )?;
                    AcornValue::Binary(BinaryOp::Or, Box::new(left_value), Box::new(right_value))
                }
                TokenType::Dot => {
                    let entity = self.evaluate_dot_expression(stack, project, left, right)?;
                    let potential = entity.expect_potential_value(expected_type, expression)?;
                    return self.maybe_resolve_value(potential, expected_type, token);
                }
                token_type => match token_type.to_infix_magic_method_name() {
                    Some(name) => self.evaluate_infix(
                        stack,
                        project,
                        expression,
                        left,
                        token,
                        right,
                        name,
                        expected_type,
                    )?,
                    None => {
                        let message =
                            &format!("unexpected operator '{}' in value expression", token);
                        return Err(expression.error(message));
                    }
                },
            },
            Expression::Concatenation(function_expr, args_expr) => {
                let function =
                    self.evaluate_potential_value(stack, function_expr, None, project)?;

                // Handle the case where the "args" are actually type parameters.
                let arg_exprs = match args_expr.as_ref() {
                    Expression::Grouping(left_delimiter, e, _) => {
                        let exprs = e.flatten_comma_separated_list();
                        if left_delimiter.token_type == TokenType::LessThan {
                            // This is a type parameter list
                            if let PotentialValue::Unresolved(unresolved) = function {
                                let mut type_params = vec![];
                                for expr in exprs {
                                    type_params.push(self.evaluate_type(project, expr)?);
                                }
                                let resolved = unresolved.resolve(left_delimiter, type_params)?;
                                resolved.check_type(expected_type, expression)?;
                                return Ok(PotentialValue::Resolved(resolved));
                            }
                            return Err(left_delimiter.error("unexpected type parameter list"));
                        } else {
                            exprs
                        }
                    }
                    _ => {
                        return Err(args_expr.error("expected a comma-separated list"));
                    }
                };

                // Typecheck the function
                let function_type = function.get_type();
                let function_type = match function_type {
                    AcornType::Function(f) => f,
                    _ => {
                        return Err(function_expr.error("cannot apply a non-function"));
                    }
                };
                if function_type.arg_types.len() < arg_exprs.len() {
                    return Err(args_expr.error(&format!(
                        "expected <= {} arguments, but got {}",
                        function_type.arg_types.len(),
                        arg_exprs.len()
                    )));
                }

                // Check if we have to do type inference.
                match function {
                    PotentialValue::Unresolved(unresolved) => self.infer_and_apply(
                        stack,
                        unresolved,
                        arg_exprs,
                        expected_type,
                        project,
                        expression,
                    )?,
                    PotentialValue::Resolved(function) => {
                        // Simple, no-type-inference-necessary construction
                        let mut args = vec![];
                        for (i, arg_expr) in arg_exprs.iter().enumerate() {
                            let arg_type: &AcornType = &function_type.arg_types[i];
                            let arg = self.evaluate_value_with_stack(
                                stack,
                                arg_expr,
                                Some(arg_type),
                                project,
                            )?;
                            args.push(arg);
                        }
                        let value = AcornValue::apply(function, args);
                        value.check_type(expected_type, expression)?;
                        value
                    }
                }
            }
            Expression::Grouping(_, e, _) => {
                self.evaluate_value_with_stack(stack, e, expected_type, project)?
            }
            Expression::Binder(token, args, body, _) => {
                if args.len() < 1 {
                    return Err(token.error("binders must have at least one argument"));
                }
                let (arg_names, arg_types) = self.bind_args(stack, project, args, None)?;
                let body_type = match token.token_type {
                    TokenType::ForAll => Some(&AcornType::Bool),
                    TokenType::Exists => Some(&AcornType::Bool),
                    _ => None,
                };
                let ret_val = match self.evaluate_value_with_stack(stack, body, body_type, project)
                {
                    Ok(value) => match token.token_type {
                        TokenType::ForAll => Ok(AcornValue::ForAll(arg_types, Box::new(value))),
                        TokenType::Exists => Ok(AcornValue::Exists(arg_types, Box::new(value))),
                        TokenType::Function => Ok(AcornValue::Lambda(arg_types, Box::new(value))),
                        _ => Err(token.error("expected a binder identifier token")),
                    },
                    Err(e) => Err(e),
                };
                stack.remove_all(&arg_names);
                if ret_val.is_ok() && token.token_type == TokenType::Function {
                    ret_val.as_ref().unwrap().check_type(expected_type, token)?;
                }
                ret_val?
            }
            Expression::IfThenElse(_, cond_exp, if_exp, else_exp, _) => {
                let cond = self.evaluate_value_with_stack(
                    stack,
                    cond_exp,
                    Some(&AcornType::Bool),
                    project,
                )?;
                let if_value =
                    self.evaluate_value_with_stack(stack, if_exp, expected_type, project)?;
                let else_value = self.evaluate_value_with_stack(
                    stack,
                    else_exp,
                    Some(&if_value.get_type()),
                    project,
                )?;
                AcornValue::IfThenElse(Box::new(cond), Box::new(if_value), Box::new(else_value))
            }
            Expression::Match(_, scrutinee_exp, case_exps, _) => {
                let mut expected_type: Option<AcornType> = expected_type.cloned();
                let scrutinee =
                    self.evaluate_value_with_stack(stack, scrutinee_exp, None, project)?;
                let scrutinee_type = scrutinee.get_type();
                let mut cases = vec![];
                let mut indices = vec![];
                let mut all_cases = false;
                for (pattern_exp, result_exp) in case_exps {
                    let (_, args, i, total) =
                        self.evaluate_pattern(project, &scrutinee_type, pattern_exp)?;
                    for (name, arg_type) in &args {
                        stack.insert(name.clone(), arg_type.clone());
                    }
                    if indices.contains(&i) {
                        return Err(pattern_exp
                            .error("cannot have multiple cases for the same constructor"));
                    }
                    indices.push(i);
                    if total == indices.len() {
                        all_cases = true;
                    }
                    let pattern = self.evaluate_value_with_stack(
                        stack,
                        pattern_exp,
                        Some(&scrutinee_type),
                        project,
                    )?;
                    let result = self.evaluate_value_with_stack(
                        stack,
                        result_exp,
                        expected_type.as_ref(),
                        project,
                    )?;
                    if expected_type.is_none() {
                        expected_type = Some(result.get_type());
                    }
                    let mut arg_types = vec![];
                    for (name, arg_type) in args {
                        stack.remove(&name);
                        arg_types.push(arg_type);
                    }
                    cases.push((arg_types, pattern, result));
                }
                if !all_cases {
                    return Err(expression.error("not all constructors are covered in this match"));
                }
                AcornValue::Match(Box::new(scrutinee), cases)
            }
        };
        Ok(PotentialValue::Resolved(value))
    }

    pub fn evaluate_typeclass(
        &self,
        project: &Project,
        expression: &Expression,
    ) -> compilation::Result<Typeclass> {
        let entity = self.evaluate_entity(&mut Stack::new(), project, expression)?;
        match entity {
            NamedEntity::Typeclass(tc) => Ok(tc),
            _ => Err(expression.error("expected a typeclass")),
        }
    }

    /// Evaluates a list of type parameter expressions.
    /// This does not bind them into the environment.
    pub fn evaluate_type_params(
        &self,
        exprs: &[TypeParamExpr],
        project: &Project,
    ) -> compilation::Result<Vec<TypeParam>> {
        let mut answer: Vec<TypeParam> = vec![];
        for expr in exprs {
            let name = expr.name.text().to_string();
            self.check_typename_available(&name, &expr.name)?;
            if answer.iter().any(|tp| tp.name == name) {
                return Err(expr.name.error("duplicate type parameter"));
            }
            let typeclass = match expr.typeclass.as_ref() {
                Some(e) => Some(self.evaluate_typeclass(project, e)?),
                None => None,
            };
            answer.push(TypeParam {
                name: expr.name.text().to_string(),
                typeclass,
            });
        }
        Ok(answer)
    }

    /// Evaluate an expression that creates a new scope for a single value inside it.
    /// This could be the statement of a theorem, the definition of a function, or other similar things.
    ///
    /// It has declarations, introducing new variables and types that exist just for this value,
    /// and it has the value itself, which can use those declarations.
    ///
    /// type_params is a list of tokens for the generic types introduced for this scope.
    /// args is a list of the new variables declared for this scope.
    /// value_type_expr is an optional expression for the type of the value.
    ///   (None means expect a boolean value.)
    /// value_expr is the expression for the value itself.
    /// function_name, when it is provided, can be used recursively.
    ///
    /// This function mutates the binding map but sets it back to its original state when finished.
    ///
    /// Returns a tuple with:
    ///   a list of type parameters
    ///   a list of argument names
    ///   a list of argument types
    ///   an optional unbound value. (None means axiom.)
    ///   the value type
    ///
    /// The type parameters are treated as arbitrary types internally to the new scope, but externally
    /// they are replaced with type variables.
    ///
    /// class_type should be provided, fully instantiated, if this is the definition of a member function.
    ///
    /// The return value is "unbound" in the sense that it has variable atoms that are not
    /// bound within any lambda, exists, or forall value. It also may have references to a
    /// recursive function that is not yet defined.
    pub fn evaluate_scoped_value(
        &mut self,
        type_param_exprs: &[TypeParamExpr],
        args: &[Declaration],
        value_type_expr: Option<&Expression>,
        value_expr: &Expression,
        class_type: Option<&AcornType>,
        function_name: Option<&LocalName>,
        project: &Project,
    ) -> compilation::Result<(
        Vec<TypeParam>,
        Vec<String>,
        Vec<AcornType>,
        Option<AcornValue>,
        AcornType,
    )> {
        // Bind all the type parameters and arguments
        let type_params = self.evaluate_type_params(&type_param_exprs, project)?;
        for param in &type_params {
            self.add_arbitrary_type(param.clone());
        }
        let mut stack = Stack::new();
        let (arg_names, internal_arg_types) =
            self.bind_args(&mut stack, project, args, class_type)?;

        // Figure out types.
        let internal_value_type = match value_type_expr {
            Some(e) => self.evaluate_type(project, e)?,
            None => AcornType::Bool,
        };

        if let Some(function_name) = function_name {
            let fn_type =
                AcornType::functional(internal_arg_types.clone(), internal_value_type.clone());
            // The function is bound to its name locally, to handle recursive definitions.
            // Internally to the definition, this function is not polymorphic.
            self.add_local_constant(function_name.clone(), vec![], fn_type, None, None);
        }

        // Evaluate the internal value using our modified bindings
        let internal_value = if value_expr.is_axiom() {
            None
        } else {
            let value = self.evaluate_value_with_stack(
                &mut stack,
                value_expr,
                Some(&internal_value_type),
                project,
            )?;

            if let Some(function_name) = function_name {
                let global_name = GlobalName::new(self.module_id, function_name.clone());
                let mut checker = TerminationChecker::new(global_name, internal_arg_types.len());
                if !checker.check(&value) {
                    return Err(
                        value_expr.error("the compiler thinks this looks like an infinite loop")
                    );
                }
            }

            Some(value)
        };

        // Reset the bindings
        for param in type_params.iter().rev() {
            self.remove_type(&param.name);
        }
        if let Some(function_name) = function_name {
            self.remove_constant(&function_name);
        }

        // We might have types parametrized on this function, or they might be parametrized on the
        // class definition. We only want to genericize the parameters that we created.
        if type_params.is_empty() {
            // Just keep the types as they are.
            Ok((
                type_params,
                arg_names,
                internal_arg_types,
                internal_value,
                internal_value_type,
            ))
        } else {
            // Convert to external type variables
            let external_value = if let Some(internal_value) = internal_value {
                if let Some(function_name) = function_name {
                    // We might have defined this function recursively.
                    // In this case, internally it's not polymorphic. It's just a constant
                    // with a type that depends on the arbitrary types we introduced.
                    // But, externally we need to make it polymorphic.
                    let global_name = GlobalName::new(self.module_id, function_name.clone());
                    let generic_params = type_params
                        .iter()
                        .map(|param| AcornType::Variable(param.clone()))
                        .collect();
                    let derecursed = internal_value.set_params(&global_name, &generic_params);
                    Some(derecursed.genericize(&type_params))
                } else {
                    // There's no name for this function so it can't possibly be recursive.
                    // This is simpler, but we still need to remove arbitrary local types.
                    Some(internal_value.genericize(&type_params))
                }
            } else {
                // No internal value, no external value.
                None
            };
            let external_arg_types = internal_arg_types
                .iter()
                .map(|t| t.genericize(&type_params))
                .collect();
            let external_value_type = internal_value_type.genericize(&type_params);

            Ok((
                type_params,
                arg_names,
                external_arg_types,
                external_value,
                external_value_type,
            ))
        }
    }

    /// Finds the names of all constants that are in this module but unknown to this binding map.
    /// The unknown constants may not be polymorphic.
    pub fn find_unknown_local_constants(
        &self,
        value: &AcornValue,
        answer: &mut HashMap<String, AcornType>,
    ) {
        match value {
            AcornValue::Variable(_, _) | AcornValue::Bool(_) => {}
            AcornValue::Constant(c) => {
                if c.name.module_id == self.module_id
                    && !self.constant_info.contains_key(&c.name.local_name)
                {
                    assert!(c.params.is_empty());
                    answer.insert(c.name.local_name.to_string(), c.instance_type.clone());
                }
            }

            AcornValue::Application(app) => {
                self.find_unknown_local_constants(&app.function, answer);
                for arg in &app.args {
                    self.find_unknown_local_constants(arg, answer);
                }
            }
            AcornValue::Lambda(_, value)
            | AcornValue::ForAll(_, value)
            | AcornValue::Exists(_, value) => {
                self.find_unknown_local_constants(value, answer);
            }
            AcornValue::Binary(_, left, right) => {
                self.find_unknown_local_constants(left, answer);
                self.find_unknown_local_constants(right, answer);
            }
            AcornValue::IfThenElse(cond, then_value, else_value) => {
                self.find_unknown_local_constants(cond, answer);
                self.find_unknown_local_constants(then_value, answer);
                self.find_unknown_local_constants(else_value, answer);
            }
            AcornValue::Match(scrutinee, cases) => {
                self.find_unknown_local_constants(scrutinee, answer);
                for (_, pattern, result) in cases {
                    self.find_unknown_local_constants(pattern, answer);
                    self.find_unknown_local_constants(result, answer);
                }
            }
            AcornValue::Not(value) => {
                self.find_unknown_local_constants(value, answer);
            }
        }
    }

    /// Replaces all theorems in the proposition with their definitions.
    /// This is admittedly weird.
    /// Note that it needs to work with templated theorems, which makes it tricky to do the
    /// type inference.
    pub fn expand_theorems(&self, proposition: Proposition, project: &Project) -> Proposition {
        proposition
            .value
            .validate()
            .unwrap_or_else(|e| panic!("invalid claim: {} ({})", proposition.value, e));

        let value = proposition.value.replace_constants(0, &|c| {
            let bindings = self.get_bindings(c.name.module_id, project);
            if bindings.is_theorem(&c.name.local_name) {
                match bindings.get_definition_and_params(&c.name.local_name) {
                    Some((def, params)) => {
                        let mut pairs = vec![];
                        for (param, t) in params.iter().zip(c.params.iter()) {
                            pairs.push((param.name.clone(), t.clone()));
                        }
                        Some(def.instantiate(&pairs))
                    }
                    None => None,
                }
            } else {
                None
            }
        });
        proposition.with_value(value)
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for going the other way, to create expressions and code strings from values and types.
    ////////////////////////////////////////////////////////////////////////////////

    /// Returns an error if this type can't be encoded as an expression.
    /// Currently this should only happen when it's defined in a module that isn't directly imported.
    /// In theory we could fix this, but we would have to track the web of dependencies.
    fn type_to_expr(&self, acorn_type: &AcornType) -> Result<Expression, CodeGenError> {
        if let AcornType::Function(ft) = acorn_type {
            let mut args = vec![];
            for arg_type in &ft.arg_types {
                args.push(self.type_to_expr(arg_type)?);
            }
            let lhs = if args.len() == 1 {
                args.pop().unwrap()
            } else {
                Expression::generate_paren_grouping(args)
            };
            let rhs = self.type_to_expr(&ft.return_type)?;
            return Ok(Expression::Binary(
                Box::new(lhs),
                TokenType::RightArrow.generate(),
                Box::new(rhs),
            ));
        }

        // Check if there's a local alias for this exact type
        if let Some(name) = self
            .type_to_typename
            .get(&PotentialType::Resolved(acorn_type.clone()))
        {
            return Ok(Expression::generate_identifier(name));
        }

        match acorn_type {
            AcornType::Data(class, params) => {
                // Check if it's a type from a module that we have imported
                // See if we have an alias
                let global_name =
                    GlobalName::new(class.module_id, LocalName::unqualified(&class.name));
                if let Some(name) = self.canonical_to_alias.get(&global_name) {
                    let base_expr = Expression::generate_identifier(name);
                    return self.parametrize_expr(base_expr, params);
                }

                // Reference this type via referencing the imported module
                if let Some(module_name) = self.module_to_name.get(&class.module_id) {
                    let base_expr =
                        Expression::generate_identifier_chain(&[module_name, &class.name]);
                    return self.parametrize_expr(base_expr, params);
                }
            }
            AcornType::Variable(param) | AcornType::Arbitrary(param) => {
                return Ok(Expression::generate_identifier(&param.name));
            }
            _ => {}
        }

        Err(CodeGenError::unnamed_type(acorn_type))
    }

    /// Adds parameters, if there are any, to an expression representing a type.
    fn parametrize_expr(
        &self,
        base_expr: Expression,
        params: &[AcornType],
    ) -> Result<Expression, CodeGenError> {
        if params.is_empty() {
            return Ok(base_expr);
        }
        let mut param_exprs = vec![];
        for param in params {
            param_exprs.push(self.type_to_expr(&param)?);
        }
        let params_expr = Expression::generate_params(param_exprs);
        let applied = Expression::Concatenation(Box::new(base_expr), Box::new(params_expr));
        Ok(applied)
    }

    /// We use variables named x0, x1, x2, etc when new temporary variables are needed.
    /// Find the next one that's available.
    fn next_indexed_var(&self, prefix: char, next_index: &mut u32) -> String {
        loop {
            let name = DefinedName::unqualified(&format!("{}{}", prefix, next_index));
            *next_index += 1;
            if !self.constant_name_in_use(&name) {
                return name.to_string();
            }
        }
    }

    /// If this value cannot be expressed in a single chunk of code, returns an error.
    /// For example, it might refer to a constant that is not in scope.
    pub fn value_to_code(&self, value: &AcornValue) -> Result<String, CodeGenError> {
        let mut var_names = vec![];
        let mut next_x = 0;
        let mut next_k = 0;
        let expr = self.value_to_expr(value, &mut var_names, &mut next_x, &mut next_k, false)?;
        Ok(expr.to_string())
    }

    /// Given a module and a name, find an expression that refers to the name.
    /// The name can be dotted, if it's a class member.
    /// Note that:
    ///   module, the canonical module of the entity we are trying to express
    /// is different from
    ///   self.module, the module we are trying to express the name in
    fn name_to_expr(&self, name: &GlobalName) -> Result<Expression, CodeGenError> {
        // We can't do skolems
        if name.module_id == Module::SKOLEM {
            return Err(CodeGenError::skolem(&name.local_name.to_string()));
        }

        // Handle numeric literals
        if let LocalName::Attribute(class, attr) = &name.local_name {
            if attr.chars().all(|ch| ch.is_ascii_digit()) {
                let numeral = TokenType::Numeral.new_token(attr);

                // If it's the default type, we don't need to scope it
                if let Some(numerals) = &self.numerals {
                    if numerals.module_id == name.module_id && &numerals.name == class {
                        return Ok(Expression::Singleton(numeral));
                    }
                }

                // Otherwise, we need to scope it by the type
                let type_name = GlobalName::new(name.module_id, LocalName::unqualified(class));
                let numeric_type = self.name_to_expr(&type_name)?;
                return Ok(Expression::generate_dot(
                    numeric_type,
                    Expression::Singleton(numeral),
                ));
            }
        }

        // Handle local constants
        if name.module_id == self.module_id {
            return Ok(match &name.local_name {
                LocalName::Unqualified(word) => Expression::generate_identifier(word),
                LocalName::Attribute(left, right) => Expression::generate_dot(
                    Expression::generate_identifier(left),
                    Expression::generate_identifier(right),
                ),
            });
        }

        // Check if there's a local alias for this constant.
        if let Some(alias) = self.canonical_to_alias.get(&name) {
            return Ok(Expression::generate_identifier(alias));
        }

        // If it's a member function, check if there's a local alias for its receiver.
        // Note that the receiver could be either a class or a typeclass.
        if let LocalName::Attribute(rname, attr) = &name.local_name {
            let receiver = GlobalName::new(name.module_id, LocalName::unqualified(rname));
            if let Some(alias) = self.canonical_to_alias.get(&receiver) {
                let lhs = Expression::generate_identifier(alias);
                let rhs = Expression::generate_identifier(attr);
                return Ok(Expression::generate_dot(lhs, rhs));
            }
        }

        // Refer to this constant using its module
        match self.module_to_name.get(&name.module_id) {
            Some(module_name) => {
                let mut parts: Vec<&str> = vec![module_name];
                parts.extend(name.local_name.name_chain().unwrap().into_iter());
                Ok(Expression::generate_identifier_chain(&parts))
            }
            None => Err(CodeGenError::UnimportedModule(
                name.module_id,
                name.local_name.to_string(),
            )),
        }
    }

    /// If use_x is true we use x-variables; otherwise we use k-variables.
    fn generate_quantifier_expr(
        &self,
        token_type: TokenType,
        quants: &Vec<AcornType>,
        value: &AcornValue,
        var_names: &mut Vec<String>,
        use_x: bool,
        next_x: &mut u32,
        next_k: &mut u32,
    ) -> Result<Expression, CodeGenError> {
        let initial_var_names_len = var_names.len();
        let mut decls = vec![];
        for arg_type in quants {
            let var_name = if use_x {
                self.next_indexed_var('x', next_x)
            } else {
                self.next_indexed_var('k', next_k)
            };
            let name_token = TokenType::Identifier.new_token(&var_name);
            var_names.push(var_name);
            let type_expr = self.type_to_expr(arg_type)?;
            let var_name = Declaration::Typed(name_token, type_expr);
            let decl = var_name;
            decls.push(decl);
        }
        let subresult = self.value_to_expr(value, var_names, next_x, next_k, false)?;
        var_names.truncate(initial_var_names_len);
        Ok(Expression::Binder(
            token_type.generate(),
            decls,
            Box::new(subresult),
            TokenType::RightBrace.generate(),
        ))
    }

    /// Convert an AcornValue to an Expression.
    /// var_names is the names we have assigned to indexed variables so far.
    /// We automatically generate variable names somtimes, using next_x and next_k.
    /// "inferrable" is true if the type of this value can be inferred, which means
    /// we don't need top level parameters.
    fn value_to_expr(
        &self,
        value: &AcornValue,
        var_names: &mut Vec<String>,
        next_x: &mut u32,
        next_k: &mut u32,
        inferrable: bool,
    ) -> Result<Expression, CodeGenError> {
        match value {
            AcornValue::Variable(i, _) => {
                Ok(Expression::generate_identifier(&var_names[*i as usize]))
            }
            AcornValue::Application(fa) => {
                let mut args = vec![];
                for arg in &fa.args {
                    // We currently never infer the type of arguments from the type of the function.
                    // Inference only goes the other way.
                    // We could improve this at some point.
                    args.push(self.value_to_expr(arg, var_names, next_x, next_k, false)?);
                }

                // Check if we could replace this with receiver+attribute syntax
                if let Some(name) = fa.function.as_attribute(&fa.args[0].get_type()) {
                    if args.len() == 1 {
                        // Prefix operators
                        if let Some(op) = TokenType::from_prefix_magic_method_name(&name) {
                            return Ok(Expression::generate_unary(op, args.pop().unwrap()));
                        }
                    }

                    if args.len() == 2 {
                        // Infix operators
                        if let Some(op) = TokenType::from_infix_magic_method_name(&name) {
                            let right = args.pop().unwrap();
                            let left = args.pop().unwrap();
                            return Ok(Expression::generate_binary(left, op, right));
                        }

                        // Long numeric literals
                        if name == "read" && args[0].is_number() {
                            if let Some(digit) = args[1].to_digit() {
                                let left = args.remove(0);
                                return Ok(Expression::generate_number(left, digit));
                            }
                        }
                    }

                    // General member functions
                    let instance = args.remove(0);
                    let bound = Expression::generate_binary(
                        instance,
                        TokenType::Dot,
                        Expression::generate_identifier(&name),
                    );
                    if args.len() == 0 {
                        // Like foo.bar
                        return Ok(bound);
                    } else {
                        // Like foo.bar(baz, qux)
                        let applied = Expression::Concatenation(
                            Box::new(bound),
                            Box::new(Expression::generate_paren_grouping(args)),
                        );
                        return Ok(applied);
                    }
                }

                let f = self.value_to_expr(&fa.function, var_names, next_x, next_k, true)?;
                let grouped_args = Expression::generate_paren_grouping(args);
                Ok(Expression::Concatenation(
                    Box::new(f),
                    Box::new(grouped_args),
                ))
            }
            AcornValue::Binary(op, left, right) => {
                let left = self.value_to_expr(left, var_names, next_x, next_k, false)?;
                let right = self.value_to_expr(right, var_names, next_x, next_k, false)?;
                let token = op.token_type().generate();
                Ok(Expression::Binary(Box::new(left), token, Box::new(right)))
            }
            AcornValue::Not(x) => {
                let x = self.value_to_expr(x, var_names, next_x, next_k, false)?;
                Ok(Expression::generate_unary(TokenType::Not, x))
            }
            AcornValue::ForAll(quants, value) => self.generate_quantifier_expr(
                TokenType::ForAll,
                quants,
                value,
                var_names,
                true,
                next_x,
                next_k,
            ),
            AcornValue::Exists(quants, value) => self.generate_quantifier_expr(
                TokenType::Exists,
                quants,
                value,
                var_names,
                false,
                next_x,
                next_k,
            ),
            AcornValue::Lambda(quants, value) => self.generate_quantifier_expr(
                TokenType::Function,
                quants,
                value,
                var_names,
                true,
                next_x,
                next_k,
            ),
            AcornValue::Bool(b) => {
                let token = if *b {
                    TokenType::True.generate()
                } else {
                    TokenType::False.generate()
                };
                Ok(Expression::Singleton(token))
            }
            AcornValue::Constant(c) => {
                if c.params.len() == 1 {
                    if let Some(typeclass) = c.params[0].as_typeclass_representative() {
                        if let Some(attribute) = c.name.as_typeclass_attribute(typeclass) {
                            // This type is an abstract representation of the typeclass, so we
                            // can represent this constant with dot syntax on the type rather than
                            // the typeclass.
                            let lhs = self.type_to_expr(&c.params[0])?;
                            let rhs = Expression::generate_identifier(&attribute);
                            return Ok(Expression::generate_dot(lhs, rhs));
                        }
                    }
                }

                let name_expr = self.name_to_expr(&c.name)?;

                if !inferrable && !c.params.is_empty() {
                    self.parametrize_expr(name_expr, &c.params)
                } else {
                    // We don't need to parametrize because it can be inferred
                    Ok(name_expr)
                }
            }
            AcornValue::IfThenElse(condition, if_value, else_value) => {
                let condition = self.value_to_expr(condition, var_names, next_x, next_k, false)?;
                let if_value = self.value_to_expr(if_value, var_names, next_x, next_k, false)?;
                let else_value =
                    self.value_to_expr(else_value, var_names, next_x, next_k, false)?;
                Ok(Expression::IfThenElse(
                    TokenType::If.generate(),
                    Box::new(condition),
                    Box::new(if_value),
                    Box::new(else_value),
                    TokenType::RightBrace.generate(),
                ))
            }
            AcornValue::Match(_scrutinee, _cases) => {
                todo!("codegen match expressions");
            }
        }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for testing.
    ////////////////////////////////////////////////////////////////////////////////

    fn str_to_type(&mut self, input: &str) -> AcornType {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        let (expression, _) =
            Expression::parse_type(&mut tokens, Terminator::Is(TokenType::NewLine)).unwrap();
        match self.evaluate_type(&Project::new_mock(), &expression) {
            Ok(t) => t,
            Err(error) => panic!("Error evaluating type expression: {}", error),
        }
    }

    pub fn assert_type_ok(&mut self, input_code: &str) {
        let acorn_type = self.str_to_type(input_code);
        let type_expr = self.type_to_expr(&acorn_type).unwrap();
        let reconstructed_code = type_expr.to_string();
        let reevaluated_type = self.str_to_type(&reconstructed_code);
        assert_eq!(acorn_type, reevaluated_type);
    }

    pub fn assert_type_bad(&mut self, input: &str) {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        let expression =
            match Expression::parse_type(&mut tokens, Terminator::Is(TokenType::NewLine)) {
                Ok((expression, _)) => expression,
                Err(_) => {
                    // We expect a bad type so this is fine
                    return;
                }
            };
        assert!(self
            .evaluate_potential_type(&Project::new_mock(), &expression)
            .is_err());
    }

    /// Check that the given name actually does have this type in the environment.
    pub fn expect_type(&self, name: &str, type_string: &str) {
        let name = DefinedName::guess(name);
        let value = self
            .get_constant_value(&name, &PanicOnError)
            .expect("no such constant");
        let env_type = value.get_type();
        assert_eq!(env_type.to_string(), type_string);
    }

    /// Check that this code, when converted to a value and back to code, is the same.
    pub fn expect_good_code(&self, input_code: &str) {
        let project = Project::new_mock();
        let expression = Expression::expect_value(input_code);
        let value = self
            .evaluate_value(&expression, None, &project)
            .expect("evaluate_value failed");
        let output_code = self.value_to_code(&value).expect("value_to_code failed");
        assert_eq!(input_code, output_code);
    }
}

impl TypeclassRegistry for BindingMap {
    fn is_instance_of(&self, class: &Class, typeclass: &Typeclass) -> bool {
        self.class_info
            .get(&class)
            .map_or(false, |info| info.typeclasses.contains_key(typeclass))
    }

    fn extends(&self, typeclass: &Typeclass, base: &Typeclass) -> bool {
        if let Some(info) = self.typeclass_info.get(typeclass) {
            info.extends.contains(base)
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_env_types() {
        let mut b = BindingMap::new(Module::FIRST_NORMAL);
        b.assert_type_ok("Bool");
        b.assert_type_ok("Bool -> Bool");
        b.assert_type_ok("Bool -> (Bool -> Bool)");
        b.assert_type_ok("(Bool -> Bool) -> (Bool -> Bool)");
        b.assert_type_ok("(Bool, Bool) -> Bool");
        b.assert_type_bad("Bool, Bool -> Bool");
        b.assert_type_bad("(Bool, Bool)");
    }
}

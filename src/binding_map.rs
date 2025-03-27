use std::collections::{BTreeMap, HashMap, HashSet};

use tower_lsp::lsp_types::{CompletionItem, CompletionItemKind};

use crate::acorn_type::{AcornType, PotentialType, TypeParam, Typeclass, UnresolvedType};
use crate::acorn_value::{AcornValue, BinaryOp};
use crate::atom::AtomId;
use crate::code_gen_error::CodeGenError;
use crate::compilation::{self, ErrorSource};
use crate::constant_name::LocalConstantName;
use crate::expression::{Declaration, Expression, Terminator, TypeParamExpr};
use crate::module::{ModuleId, FIRST_NORMAL};
use crate::named_entity::NamedEntity;
use crate::potential_value::PotentialValue;
use crate::project::Project;
use crate::termination_checker::TerminationChecker;
use crate::token::{self, Token, TokenIter, TokenType};
use crate::unresolved_constant::UnresolvedConstant;

// In order to convert an Expression to an AcornValue, we need to convert the string representation
// of types, variable names, and constant names into numeric identifiers, detect name collisions,
// and typecheck everything.
// The BindingMap handles this. It does not handle Statements, just Expressions.
// It does not have to be efficient enough to run in the inner loop of the prover.
#[derive(Clone)]
pub struct BindingMap {
    // The module all these names are in.
    module: ModuleId,

    // Maps the name of a type to the type object.
    // Includes unresolved names like List that don't have enough information
    // to get a specific type.
    typename_to_type: BTreeMap<String, PotentialType>,

    // Maps the type object to its name in this environment.
    type_to_typename: HashMap<PotentialType, String>,

    // Maps the name of a type to the typeclass.
    // Includes typeclasses that were imported from other modules.
    name_to_typeclass: BTreeMap<String, Typeclass>,

    // Maps the typeclass to its name in this environment.
    // Includes every typeclass that has a top-level name in this environment.
    typeclass_to_name: HashMap<Typeclass, String>,

    // Attribute names of both classes and typeclasses defined in this module.
    attributes: HashMap<String, HashSet<String>>,

    // Maps the name of a constant to the type of that constant.
    // This also includes entries for aliases.
    // For generic constants, this stores the type using the same type variables
    // that were used in the definition.
    constant_name_to_type: HashMap<String, AcornType>,

    // Maps the name of a constant defined in this scope to information about it.
    // Doesn't handle variables defined on the stack, only ones that will be in scope for the
    // entirety of this environment.
    // Doesn't handle aliases.
    // Includes "<datatype>.<constant>" for members.
    constant_info: BTreeMap<String, ConstantInfo>,

    // The canonical identifier of a constant value is the first place it is defined.
    // There may be other names in this environment that refer to the same thing.
    // When we create an AcornValue, we want to use the canonical name.
    // The alias -> canonical value mapping is stored here.
    alias_to_canonical: HashMap<String, PotentialValue>,

    // Whenever a name from some other scope has a local alias in this one,
    // if we're generating code, we prefer to use the local name.
    // For this reason, canonical_to_alias maps the canonical identifier to the preferred local alias.
    canonical_to_alias: HashMap<(ModuleId, String), String>,

    // Names that refer to other modules.
    // After "import foo", "foo" refers to a module.
    // It's important that these are in alphabetical order, so that dependency hashes are consistent.
    name_to_module: BTreeMap<String, ModuleId>,

    // The local name for imported modules.
    module_to_name: HashMap<ModuleId, String>,

    // The default data type to use for numeric literals.
    default: Option<(ModuleId, String)>,

    // Whether this constant is the name of a theorem in this context.
    // Inside the block containing the proof of a theorem, the name is not considered to
    // be a theorem.
    theorems: HashSet<String>,

    // Stores the instance-of relationships for classes that were defined in this module.
    instance_of: HashMap<String, HashSet<Typeclass>>,
}

// A representation of the variables on the stack.
pub struct Stack {
    // Maps the name of the variable to their depth and their type.
    vars: HashMap<String, (AtomId, AcornType)>,
}

impl Stack {
    pub fn new() -> Self {
        Stack {
            vars: HashMap::new(),
        }
    }

    pub fn names(&self) -> Vec<&str> {
        let mut answer: Vec<&str> = vec![""; self.vars.len()];
        for (name, (i, _)) in &self.vars {
            answer[*i as usize] = name;
        }
        answer
    }

    pub fn insert(&mut self, name: String, acorn_type: AcornType) -> AtomId {
        let i = self.vars.len() as AtomId;
        self.vars.insert(name, (i, acorn_type));
        i
    }

    fn remove(&mut self, name: &str) {
        self.vars.remove(name);
    }

    pub fn remove_all(&mut self, names: &[String]) {
        for name in names {
            self.remove(name);
        }
    }

    // Returns the depth and type of the variable with this name.
    fn get(&self, name: &str) -> Option<&(AtomId, AcornType)> {
        self.vars.get(name)
    }
}

// Information that the BindingMap stores about a constant.
#[derive(Clone)]
struct ConstantInfo {
    // The value for this constant. Not the definition, but the constant itself.
    // If this is a generic constant, this value is unresolved.
    value: PotentialValue,

    // The definition of this constant, if it has one.
    definition: Option<AcornValue>,

    // If this constant is a constructor, store:
    //   the type it constructs
    //   an index of which constructor it is
    //   how many total constructors there are
    constructor: Option<(AcornType, usize, usize)>,
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
        assert!(module >= FIRST_NORMAL);
        let mut answer = BindingMap {
            module,
            typename_to_type: BTreeMap::new(),
            type_to_typename: HashMap::new(),
            name_to_typeclass: BTreeMap::new(),
            typeclass_to_name: HashMap::new(),
            attributes: HashMap::new(),
            constant_name_to_type: HashMap::new(),
            constant_info: BTreeMap::new(),
            alias_to_canonical: HashMap::new(),
            canonical_to_alias: HashMap::new(),
            name_to_module: BTreeMap::new(),
            module_to_name: HashMap::new(),
            default: None,
            theorems: HashSet::new(),
            instance_of: HashMap::new(),
        };
        answer.add_type_alias("Bool", PotentialType::Resolved(AcornType::Bool));
        answer
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Simple helper functions.
    ////////////////////////////////////////////////////////////////////////////////

    pub fn check_constant_name_available(
        &self,
        source: &dyn ErrorSource,
        name: &LocalConstantName,
    ) -> compilation::Result<()> {
        if self.constant_name_in_use(&name) {
            return Err(source.error(&format!("constant name {} is already in use", name)));
        }
        Ok(())
    }

    // Returns an error if this name is already in use.
    pub fn check_unqualified_name_available(
        &self,
        source: &dyn ErrorSource,
        name: &str,
    ) -> compilation::Result<()> {
        self.check_constant_name_available(
            source,
            &LocalConstantName::Unqualified(name.to_string()),
        )
    }

    pub fn constant_name_in_use(&self, name: &LocalConstantName) -> bool {
        match name {
            LocalConstantName::Unqualified(name) => {
                // Module names and constant names can conflict.
                self.constant_name_to_type.contains_key(name)
                    || self.name_to_module.contains_key(name)
            }
            _ => self.constant_name_to_type.contains_key(&name.to_string()),
        }
    }

    // Checks against names for both types and typeclasses because they can conflict.
    pub fn check_typename_available(
        &self,
        source: &dyn ErrorSource,
        name: &str,
    ) -> compilation::Result<()> {
        if self.typename_to_type.contains_key(name) || self.name_to_typeclass.contains_key(name) {
            return Err(source.error(&format!("typename {} is already in use", name)));
        }
        Ok(())
    }

    // Adds both directions for a name <-> type correspondence.
    // Panics if the name is already bound.
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

    // Adds a new data type to the binding map.
    // Panics if the name is already bound.
    pub fn add_data_type(&mut self, name: &str) -> AcornType {
        let t = AcornType::Data(self.module, name.to_string(), vec![]);
        self.insert_type_name(name.to_string(), PotentialType::Resolved(t.clone()));
        t
    }

    // Panics if the name is already bound.
    pub fn add_potential_type(
        &mut self,
        name: &str,
        params: Vec<Option<Typeclass>>,
    ) -> PotentialType {
        if params.len() == 0 {
            return PotentialType::Resolved(self.add_data_type(name));
        }
        let ut = UnresolvedType {
            module_id: self.module,
            name: name.to_string(),
            params,
        };
        let potential = PotentialType::Unresolved(ut);
        self.insert_type_name(name.to_string(), potential.clone());
        potential
    }

    // Adds an arbitrary type to the binding map.
    // This indicates a type parameter that is coming into scope.
    // Panics if the param name is already bound.
    pub fn add_arbitrary_type(&mut self, param: TypeParam) -> AcornType {
        let name = param.name.to_string();
        let arbitrary_type = AcornType::Arbitrary(param);
        let potential = PotentialType::Resolved(arbitrary_type.clone());
        self.insert_type_name(name, potential);
        arbitrary_type
    }

    // Adds a new type name that's an alias for an existing type.
    // Panics if the alias is already bound.
    pub fn add_type_alias(&mut self, name: &str, potential: PotentialType) {
        // Local type aliases for concrete types should be preferred.
        if let PotentialType::Resolved(AcornType::Data(module, type_name, params)) = &potential {
            if params.is_empty() {
                self.canonical_to_alias
                    .entry((*module, type_name.clone()))
                    .or_insert(name.to_string());
            }
        }

        // Local type aliases should also be preferred to the canonical name for
        // unresolved generic types.
        if let PotentialType::Unresolved(u) = &potential {
            self.canonical_to_alias
                .entry((u.module_id, u.name.clone()))
                .or_insert(name.to_string());
        }

        self.insert_type_name(name.to_string(), potential);
    }

    // Adds a name for this typeclass.
    // Panics if the name is already bound.
    pub fn add_typeclass(&mut self, name: &str, typeclass: Typeclass) {
        // There can be multiple names for a typeclass.
        // If we already have a name for the reverse lookup, we don't overwrite it.
        if !self.typeclass_to_name.contains_key(&typeclass) {
            self.typeclass_to_name
                .insert(typeclass.clone(), name.to_string());
        }

        // self.name_to_typeclass.insert(name.to_string(), typeclass);
        match self.name_to_typeclass.entry(name.to_string()) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(typeclass);
            }
            std::collections::btree_map::Entry::Occupied(entry) => {
                panic!("typeclass name {} is already bound", entry.key());
            }
        }
    }

    // A helper to get the bindings from the project if needed bindings.
    fn get_bindings<'a>(&'a self, project: &'a Project, module_id: ModuleId) -> &'a BindingMap {
        if module_id == self.module {
            self
        } else {
            project.get_bindings(module_id).unwrap()
        }
    }

    pub fn get_attributes<'a>(
        &'a self,
        project: &'a Project,
        module_id: ModuleId,
        name: &str,
    ) -> &'a HashSet<String> {
        self.get_bindings(project, module_id)
            .attributes
            .get(name)
            .unwrap()
    }

    // Call this after an instance attribute has been defined to typecheck it.
    // Returns (resolved typeclass attribute, defined instance attribute).
    // The resolved typeclass attribute is like
    // Ring.add<Int>
    // and the defined instance attribute is the one that we defined, before
    // proving that Int was actually a Ring.
    pub fn check_instance_attribute(
        &self,
        source: &dyn ErrorSource,
        project: &Project,
        instance_name: &str,
        instance_type: &AcornType,
        typeclass: &Typeclass,
        attr_name: &str,
    ) -> compilation::Result<(AcornValue, AcornValue)> {
        let typeclass_attr_name = LocalConstantName::attribute(&typeclass.name, attr_name);
        let typeclass_attr = self
            .get_bindings(&project, typeclass.module_id)
            .get_constant_value(source, &typeclass_attr_name)?;
        let uc = typeclass_attr.as_unresolved(source)?;
        let resolved_attr = uc.resolve(source, vec![instance_type.clone()])?;
        let resolved_attr_type = resolved_attr.get_type();
        let instance_attr_name = LocalConstantName::instance(&typeclass, attr_name, instance_name);
        let instance_attr = self.get_constant_value(source, &instance_attr_name)?;
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

    pub fn set_instance_of(&mut self, instance_name: &str, typeclass: Typeclass) {
        if self.instance_of.contains_key(instance_name) {
            self.instance_of
                .get_mut(instance_name)
                .unwrap()
                .insert(typeclass);
        } else {
            let mut set = HashSet::new();
            set.insert(typeclass);
            self.instance_of.insert(instance_name.to_string(), set);
        }
    }

    fn has_constant_value(&self, name: &LocalConstantName) -> bool {
        let name = name.to_string();
        self.constant_name_to_type.contains_key(&name)
    }

    // Returns a PotentialValue representing this name, if there is one.
    // This can be either a resolved or unresolved value.
    pub fn get_constant_value<'a>(
        &self,
        source: &dyn ErrorSource,
        name: &LocalConstantName,
    ) -> compilation::Result<PotentialValue> {
        let string_name = name.to_string();

        // Look for aliases
        if let Some(pv) = self.alias_to_canonical.get(&string_name) {
            return Ok(pv.clone());
        }

        // Look at constants defined in this module
        match self.constant_info.get(&string_name) {
            Some(info) => Ok(info.value.clone()),
            None => Err(source.error(&format!("constant {} not found", name))),
        }
    }

    // Gets the type for an identifier, not for a type name.
    // E.g. if let x: Nat = 0, then get_type("x") will give you Nat.
    // XXX
    pub fn get_type_for_constant_name(&self, identifier: &str) -> Option<&AcornType> {
        self.constant_name_to_type.get(identifier)
    }

    pub fn unresolved_params(&self, identifier: &str) -> Vec<TypeParam> {
        match self.constant_info.get(identifier) {
            Some(info) => info.value.unresolved_params().to_vec(),
            None => vec![],
        }
    }

    // Gets the type for a type name, not for an identifier.
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

    pub fn has_constant_name(&self, identifier: &str) -> bool {
        self.constant_name_to_type.contains_key(identifier)
    }

    // Returns the defined value, if there is a defined value.
    // If there isn't, returns None.
    pub fn get_definition(&self, name: &str) -> Option<&AcornValue> {
        self.constant_info.get(name)?.definition.as_ref()
    }

    // Returns the defined value and its parameters in their canonical order.
    // Returns None if there is no definition.
    pub fn get_definition_and_params(&self, name: &str) -> Option<(&AcornValue, &[TypeParam])> {
        let info = self.constant_info.get(name)?;
        Some((info.definition.as_ref()?, info.value.unresolved_params()))
    }

    // All other modules that we directly depend on, besides this one.
    // Sorted by the name of the import, so that the order will be consistent.
    pub fn direct_dependencies(&self) -> Vec<ModuleId> {
        self.name_to_module.values().copied().collect()
    }

    pub fn set_default(&mut self, module: ModuleId, type_name: String) {
        self.default = Some((module, type_name));
    }

    // Adds a constant.
    // Panics if the name is already bound.
    // The type and definition can be generic. If so, the parameters must be listed in params.
    // This doesn't handle aliases intelligently.
    pub fn add_constant(
        &mut self,
        name: &LocalConstantName,
        params: Vec<TypeParam>,
        constant_type: AcornType,
        definition: Option<AcornValue>,
        constructor: Option<(AcornType, usize, usize)>,
    ) {
        if let Some(definition) = &definition {
            if let Err(e) = definition.validate() {
                panic!("invalid definition for constant {}: {}", name, e);
            }
            if params.is_empty() && definition.has_generic() {
                panic!("there should not be generic types in non-parametrized definitions");
            }
            if !params.is_empty() && definition.has_arbitrary() {
                panic!("there should not be arbitrary types in parametrized definitions");
            }
        }
        if params.is_empty() && constant_type.has_generic() {
            panic!("there should not be generic types in non-parametrized constant types");
        }
        if !params.is_empty() && constant_type.has_arbitrary() {
            panic!("there should not be arbitrary types in parametrized constant types");
        }

        let value =
            PotentialValue::constant(self.module, name, constant_type.clone(), params.clone());

        self.constant_name_to_type
            .insert(name.to_string(), constant_type)
            .map(|_| panic!("constant name {} already bound", name));

        let info = ConstantInfo {
            value,
            definition,
            constructor,
        };
        let name = name.to_string();
        self.constant_info.insert(name.to_string(), info);
        if let Some((entity_name, attribute)) = name.rsplit_once('.') {
            if self.attributes.contains_key(entity_name) {
                self.attributes
                    .get_mut(entity_name)
                    .unwrap()
                    .insert(attribute.to_string());
            } else {
                let mut set = HashSet::new();
                set.insert(attribute.to_string());
                self.attributes.insert(entity_name.to_string(), set);
            }
        }
    }

    // Be really careful about this, it seems likely to break things.
    fn remove_constant(&mut self, name: &LocalConstantName) {
        let name = name.to_string();
        self.constant_name_to_type
            .remove(&name)
            .expect("constant name not in use");
        self.constant_info
            .remove(&name)
            .expect("constant name not in use");
    }

    // Adds a local alias for an already-existing constant value.
    pub fn add_alias(
        &mut self,
        name: &str,
        canonical_module: ModuleId,
        canonical_name: String,
        value: PotentialValue,
    ) {
        self.constant_name_to_type
            .insert(name.to_string(), value.get_type())
            .map(|_| {
                panic!("alias {} is already bound", name);
            });
        let canonical = (canonical_module, canonical_name);
        if canonical_module != self.module {
            // Prefer this alias locally to using the qualified, canonical name
            self.canonical_to_alias
                .entry(canonical.clone())
                .or_insert(name.to_string());
        }
        self.alias_to_canonical.insert(name.to_string(), value);
    }

    pub fn is_constant(&self, name: &str) -> bool {
        self.constant_info.contains_key(name)
    }

    pub fn mark_as_theorem(&mut self, name: &str) {
        self.theorems.insert(name.to_string());
    }

    pub fn is_theorem(&self, name: &str) -> bool {
        self.theorems.contains(name)
    }

    // Type variables and arbitrary variables should get removed when they go out of scope.
    // Other sorts of types shouldn't be getting removed.
    pub fn remove_type(&mut self, name: &str) {
        match self.typename_to_type.remove(name) {
            Some(p) => match &p {
                PotentialType::Unresolved(ut) => {
                    panic!("removing type {} which is unresolved", ut.name);
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

    // Adds this name to the environment as a module.
    pub fn import_module(&mut self, name: &str, module: ModuleId) {
        self.name_to_module
            .insert(name.to_string(), module)
            .map(|_| {
                panic!("module name {} already bound", name);
            });
        self.module_to_name.insert(module, name.to_string());
    }

    pub fn is_module(&self, name: &str) -> bool {
        self.name_to_module.contains_key(name)
    }

    // Whether this value is calling a theorem on some arguments.
    pub fn is_citation(&self, project: &Project, claim: &AcornValue) -> bool {
        match claim.is_named_function_call() {
            Some((module_id, name)) => {
                if module_id == self.module {
                    self.is_theorem(&name)
                } else {
                    let bindings = project.get_bindings(module_id).unwrap();
                    bindings.is_theorem(&name)
                }
            }
            None => false,
        }
    }

    fn get_attribute_completions(
        &self,
        project: &Project,
        module: ModuleId,
        base_name: &str,
        prefix: &str,
    ) -> Option<Vec<CompletionItem>> {
        let bindings = if module == self.module {
            &self
        } else {
            project.get_bindings(module).unwrap()
        };
        let mut answer = vec![];
        let full_prefix = format!("{}.{}", base_name, prefix);
        for key in keys_with_prefix(&bindings.constant_info, &full_prefix) {
            let completion = CompletionItem {
                label: key.split('.').last()?.to_string(),
                kind: Some(CompletionItemKind::FIELD),
                ..Default::default()
            };
            answer.push(completion);
        }
        Some(answer)
    }

    // Gets completions when we are typing a member name.
    fn get_type_attribute_completions(
        &self,
        project: &Project,
        t: &AcornType,
        prefix: &str,
    ) -> Option<Vec<CompletionItem>> {
        if let AcornType::Data(module, type_name, _) = t {
            self.get_attribute_completions(project, *module, type_name, prefix)
        } else {
            None
        }
    }

    // The prefix is just of a single identifier.
    // If importing is true, we are looking for names to import. This means that we don't
    // want to suggest names unless this is the canonical location for them, and we don't
    // want to suggest theorems.
    pub fn get_completions(
        &self,
        project: &Project,
        prefix: &str,
        importing: bool,
    ) -> Option<Vec<CompletionItem>> {
        if prefix.contains('.') {
            if importing {
                // Syntactically invalid
                return None;
            }
            let mut name_chain = prefix.split('.').collect::<Vec<&str>>();
            let partial = name_chain.pop()?;
            let namespace = self.evaluate_name_chain(project, &name_chain)?;
            match namespace {
                NamedEntity::Module(module) => {
                    let bindings = project.get_bindings(module)?;
                    return bindings.get_completions(project, partial, true);
                }
                NamedEntity::Type(t) => {
                    return self.get_type_attribute_completions(project, &t, partial);
                }
                NamedEntity::Value(v) => {
                    let t = v.get_type();
                    return self.get_type_attribute_completions(project, &t, partial);
                }
                NamedEntity::Typeclass(tc) => {
                    return self.get_attribute_completions(
                        project,
                        tc.module_id,
                        &tc.name,
                        partial,
                    );
                }
                NamedEntity::UnresolvedValue(u) => {
                    return self.get_type_attribute_completions(project, &u.generic_type, partial);
                }
                NamedEntity::UnresolvedType(ut) => {
                    let display_type = ut.to_display_type();
                    return self.get_type_attribute_completions(project, &display_type, partial);
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
            for key in keys_with_prefix(&self.constant_info, prefix) {
                if key.contains('.') {
                    continue;
                }
                if importing {
                    if self.alias_to_canonical.contains_key(key) {
                        // Don't suggest aliases when importing
                        continue;
                    }
                    if self.theorems.contains(key) {
                        // Don't suggest theorems when importing
                        continue;
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
                        PotentialType::Resolved(AcornType::Data(module, name, _)) => {
                            if module != &self.module || name != key {
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

    // Evaluates an expression that represents a type.
    pub fn evaluate_type(
        &self,
        project: &Project,
        expression: &Expression,
    ) -> compilation::Result<AcornType> {
        let potential = self.evaluate_potential_type(project, expression)?;
        match potential {
            PotentialType::Resolved(t) => Ok(t),
            PotentialType::Unresolved(ut) => {
                Err(expression.error(&format!("type {} is unresolved", ut.name)))
            }
        }
    }

    // Evaluates an expression that either represents a type, or represents a type that still needs params.
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
            Expression::Apply(left, params) => {
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

    // Evaluates a list of types.
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

    // Evaluates a variable declaration in this context.
    // "self" declarations should be handled externally.
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

    // Parses a list of named argument declarations and adds them to the stack.
    // class_type should be provided if these are the arguments of a new member function.
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
            self.check_unqualified_name_available(declaration.token(), &name)?;
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

    // Errors if the value is not a constructor of the expected type.
    // Returns the index of which constructor this is, and the total number of constructors.
    fn expect_constructor(
        &self,
        project: &Project,
        expected_type: &AcornType,
        value: &AcornValue,
        source: &dyn ErrorSource,
    ) -> compilation::Result<(usize, usize)> {
        let info = match value.as_simple_constant() {
            Some((module, name)) => {
                let bindings = if module == self.module {
                    &self
                } else {
                    project.get_bindings(module).unwrap()
                };
                bindings.constant_info.get(name).unwrap()
            }
            None => return Err(source.error("invalid pattern")),
        };
        match &info.constructor {
            Some((constructor_type, i, total)) => {
                constructor_type.check_eq(source, Some(expected_type))?;
                Ok((*i, *total))
            }
            None => Err(source.error("expected a constructor")),
        }
    }

    // Evalutes a pattern match. Infers their types from the pattern.
    // Returns an error if the pattern is not a constructor of the expected type.
    // Returns:
    //   a value for the constructor function
    //   a list of (name, type) pairs
    //   the index of which constructor this is
    //   the total number of constructors
    pub fn evaluate_pattern(
        &self,
        project: &Project,
        expected_type: &AcornType,
        pattern: &Expression,
    ) -> compilation::Result<(AcornValue, Vec<(String, AcornType)>, usize, usize)> {
        let (fn_exp, args) = match pattern {
            Expression::Apply(function, args) => (function, args),
            _ => {
                // This could be a no-argument constructor.
                let constructor = self.evaluate_value(project, pattern, None)?;
                let (i, total) =
                    self.expect_constructor(project, expected_type, &constructor, pattern)?;
                return Ok((constructor, vec![], i, total));
            }
        };
        let constructor = self.evaluate_value(project, fn_exp, None)?;
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
            self.check_unqualified_name_available(name_exp, &name)?;
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

    // This function evaluates numbers when we already know what type they are.
    // token is the token to report errors with.
    // s is the string to parse.
    fn evaluate_number_with_type(
        &self,
        token: &Token,
        project: &Project,
        module: ModuleId,
        type_name: &str,
        s: &str,
    ) -> compilation::Result<AcornValue> {
        if self.has_type_attribute(project, module, type_name, s) {
            return self
                .evaluate_type_attribute(token, project, module, type_name, s)?
                .as_value(token);
        }

        if s.len() == 1 {
            return Err(token.error(&format!("digit {}.{} is not defined", type_name, s)));
        }

        let last_str = &s[s.len() - 1..];
        let last_num =
            self.evaluate_number_with_type(token, project, module, type_name, last_str)?;
        let initial_str = &s[..s.len() - 1];
        let initial_num =
            self.evaluate_number_with_type(token, project, module, type_name, initial_str)?;
        let read_fn =
            match self.evaluate_type_attribute(token, project, module, type_name, "read")? {
                PotentialValue::Resolved(f) => f,
                PotentialValue::Unresolved(_) => {
                    return Err(token.error(&format!(
                        "read function {}.read has unresolved type",
                        type_name
                    )))
                }
            };
        let value = AcornValue::apply(read_fn, vec![initial_num, last_num]);
        Ok(value)
    }

    fn has_type_attribute(
        &self,
        project: &Project,
        module: ModuleId,
        type_name: &str,
        var_name: &str,
    ) -> bool {
        let bindings = if module == self.module {
            &self
        } else {
            project.get_bindings(module).unwrap()
        };
        let constant_name = LocalConstantName::attribute(type_name, var_name);
        bindings.has_constant_value(&constant_name)
    }

    // Evaluates a name scoped by a class or typeclass name, like MyClass.foo
    fn evaluate_type_attribute(
        &self,
        source: &dyn ErrorSource,
        project: &Project,
        module: ModuleId,
        type_name: &str,
        var_name: &str,
    ) -> compilation::Result<PotentialValue> {
        let bindings = if module == self.module {
            &self
        } else {
            project.get_bindings(module).unwrap()
        };
        let constant_name = LocalConstantName::attribute(type_name, var_name);
        bindings.get_constant_value(source, &constant_name)
    }

    // Evaluates an expression that is supposed to describe a value, with an empty stack.
    pub fn evaluate_value(
        &self,
        project: &Project,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<AcornValue> {
        self.evaluate_value_with_stack(&mut Stack::new(), project, expression, expected_type)
    }

    // Evaluates an attribute of an instance, like foo.bar.
    // token is used for reporting errors but may not correspond to anything in particular.
    fn evaluate_instance_attribute(
        &self,
        source: &dyn ErrorSource,
        project: &Project,
        instance: AcornValue,
        attr_name: &str,
    ) -> compilation::Result<AcornValue> {
        let base_type = instance.get_type();

        let (module, type_name) = match &base_type {
            AcornType::Data(module, type_name, _) => (*module, type_name),
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
                (typeclass.module_id, &typeclass.name)
            }
            _ => {
                return Err(source.error(&format!(
                    "objects of type {:?} have no attributes",
                    base_type
                )));
            }
        };
        let constant_name = LocalConstantName::attribute(type_name, attr_name);
        let function = self
            .get_bindings(&project, module)
            .get_constant_value(source, &constant_name)?;
        self.apply_potential(source, project, function, vec![instance], None)
    }

    // Evaluates a single name, which may be namespaced to another named entity.
    // In this situation, we don't know what sort of thing we expect the name to represent.
    // We have the entity described by a chain of names, and we're adding one more name to the chain.
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
                let value =
                    self.evaluate_instance_attribute(name_token, project, instance, name)?;
                Ok(NamedEntity::Value(value))
            }
            Some(NamedEntity::Type(t)) => {
                match &t {
                    AcornType::Data(module, type_name, params) => {
                        if name_token.token_type == TokenType::Numeral {
                            let value = self.evaluate_number_with_type(
                                name_token,
                                project,
                                *module,
                                &type_name,
                                name_token.text(),
                            )?;
                            return Ok(NamedEntity::Value(value));
                        }
                        match self.evaluate_type_attribute(
                            name_token, project, *module, &type_name, name,
                        )? {
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
                        match self.evaluate_type_attribute(
                            name_token,
                            project,
                            typeclass.module_id,
                            &typeclass.name,
                            name,
                        )? {
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
                match self.evaluate_type_attribute(
                    name_token,
                    project,
                    tc.module_id,
                    &tc.name,
                    name,
                )? {
                    PotentialValue::Resolved(value) => Ok(NamedEntity::Value(value)),
                    PotentialValue::Unresolved(u) => Ok(NamedEntity::UnresolvedValue(u)),
                }
            }
            Some(NamedEntity::UnresolvedValue(_)) => {
                Err(name_token.error("cannot access members of unresolved types"))
            }
            Some(NamedEntity::UnresolvedType(ut)) => {
                match self.evaluate_type_attribute(
                    name_token,
                    project,
                    ut.module_id,
                    &ut.name,
                    name,
                )? {
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
                            let constant_name = LocalConstantName::unqualified(name);
                            Ok(NamedEntity::new(
                                self.get_constant_value(name_token, &constant_name)?,
                            ))
                        }
                    }
                    TokenType::Numeral => {
                        let (module, type_name) = match &self.default {
                            Some((module, type_name)) => (module, type_name),
                            None => {
                                return Err(name_token
                                    .error("you must set a default type for numeric literals"));
                            }
                        };
                        let value = self.evaluate_number_with_type(
                            name_token,
                            project,
                            *module,
                            type_name,
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

    // Evaluates a single dot operator.
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

    // Evaluate a string of names separated by dots.
    // Creates fake tokens to be used for error reporting.
    // Chain must not be empty.
    fn evaluate_name_chain(&self, project: &Project, chain: &[&str]) -> Option<NamedEntity> {
        let mut answer: Option<NamedEntity> = None;
        for name in chain {
            let token = TokenType::Identifier.new_token(name);
            answer = Some(
                self.evaluate_name(&token, project, &Stack::new(), answer)
                    .ok()?,
            );
        }
        answer
    }

    // Evaluates an expression that could represent any sort of named entity.
    // It could be a type, a value, or a module.
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
        let value = self.evaluate_value_with_stack(stack, project, expression, None)?;
        Ok(NamedEntity::Value(value))
    }

    // Evaluates an infix operator.
    // name is the special alphanumeric name that corresponds to the operator, like "+" expands to "add".
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
        let left_value = self.evaluate_value_with_stack(stack, project, left, None)?;
        let right_value = self.evaluate_value_with_stack(stack, project, right, None)?;

        // Get the partial application to the left
        let partial = self.evaluate_instance_attribute(expression, project, left_value, name)?;
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
                right_value.check_type(expression, Some(&f.arg_types[1]))?;
            }
            _ => return Err(expression.error(&format!("unexpected type for '{}' method", name))),
        };

        fa.args.push(right_value);
        let value = AcornValue::apply(*fa.function, fa.args);
        value.check_type(expression, expected_type)?;
        Ok(value)
    }

    // Imports a name from another module.
    // The name could either be a type or a value.
    pub fn import_name(
        &mut self,
        project: &Project,
        module: ModuleId,
        name_token: &Token,
    ) -> compilation::Result<()> {
        self.check_unqualified_name_available(name_token, &name_token.text())?;
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
                if let Some((ext_module, ext_name)) = value.as_simple_constant() {
                    self.add_alias(
                        &name_token.text(),
                        ext_module,
                        ext_name.to_string(),
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
            NamedEntity::Typeclass(_) => {
                Err(name_token.error("cannot import typeclasses indirectly"))
            }

            NamedEntity::UnresolvedValue(uc) => {
                self.add_alias(
                    &name_token.text(),
                    uc.module_id,
                    uc.name.clone(),
                    PotentialValue::Unresolved(uc),
                );
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
        source: &dyn ErrorSource,
        project: &Project,
        potential: PotentialValue,
        args: Vec<AcornValue>,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<AcornValue> {
        let value = match potential {
            PotentialValue::Resolved(f) => {
                let value = AcornValue::apply(f, args);
                value.check_type(source, expected_type)?;
                value
            }
            PotentialValue::Unresolved(u) => {
                self.resolve_function(source, project, u, args, expected_type)?
            }
        };
        Ok(value)
    }

    fn is_instance_of(
        &self,
        project: &Project,
        module_id: ModuleId,
        type_name: &str,
        typeclass: &Typeclass,
    ) -> bool {
        self.get_bindings(project, module_id)
            .instance_of
            .get(type_name)
            .map_or(false, |set| set.contains(typeclass))
    }

    fn resolve_function(
        &self,
        source: &dyn ErrorSource,
        project: &Project,
        unresolved: UnresolvedConstant,
        args: Vec<AcornValue>,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<AcornValue> {
        let unresolved_function_type = match &unresolved.generic_type {
            AcornType::Function(f) => f,
            _ => {
                return Err(source.error("expected a function"));
            }
        };
        if unresolved_function_type.has_arbitrary() {
            return Err(source.error("unresolved function type has arbitrary"));
        }

        // Do type inference. Mapping is where the generic types go.
        let mut mapping = HashMap::new();
        for (i, arg) in args.iter().enumerate() {
            if arg.has_generic() {
                return Err(source.error(&format!("argument {} ({}) has unresolved type", i, arg)));
            }
            let arg_type: &AcornType = &unresolved_function_type.arg_types[i];
            if !arg_type.match_instance(
                &arg.get_type(),
                &|module_id, type_name, typeclass| {
                    self.is_instance_of(&project, *module_id, type_name, typeclass)
                },
                &mut mapping,
            ) {
                return Err(source.error(&format!(
                    "for argument {}, expected type {:?}, but got {:?}",
                    i,
                    arg_type,
                    arg.get_type()
                )));
            }
        }

        // Determine the parameters for the instance function
        let mut named_params = vec![];
        let mut instance_params = vec![];
        for param in &unresolved.params {
            match mapping.get(&param.name) {
                Some(t) => {
                    named_params.push((param.name.clone(), t.clone()));
                    instance_params.push(t.clone());
                }
                None => {
                    return Err(
                        source.error(&format!("parameter {} could not be inferred", &param.name))
                    );
                }
            }
        }

        let instance_fn = unresolved.resolve(source, instance_params)?;

        let value = AcornValue::apply(instance_fn, args);
        value.check_type(source, expected_type)?;
        Ok(value)
    }

    // Apply an unresolved name to arguments, inferring the types.
    fn infer_and_apply(
        &self,
        stack: &mut Stack,
        project: &Project,
        source: &dyn ErrorSource,
        unresolved: UnresolvedConstant,
        arg_exprs: Vec<&Expression>,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<AcornValue> {
        // Evaluate the arguments
        let mut args = vec![];
        for arg_expr in &arg_exprs {
            let arg = self.evaluate_value_with_stack(stack, project, arg_expr, None)?;
            args.push(arg);
        }

        self.resolve_function(source, project, unresolved, args, expected_type)
    }

    // This creates a version of a typeclass condition that is specialized to a particular
    // class that isn't an instance of the typeclass.
    // The class must be defined in this module.
    //
    // We use this when we haven't proven that a type is an instance of a typeclass yet.
    // So for example instead of resolving:
    //   Ring.add<T> -> Ring.add<Int>
    // we resolve:
    //   Ring.add<T> -> Int.Ring.add
    //
    // TODO: does this work right for typeclasses outside this module?
    pub fn pseudo_instantiate_condition(
        &self,
        source: &dyn ErrorSource,
        instance_name: &str,
        instance_type: &AcornType,
        typeclass: &Typeclass,
        condition_name: &str,
    ) -> compilation::Result<AcornValue> {
        let tc_condition_name = format!("{}.{}", &typeclass.name, condition_name);
        let (def, params) = match self.get_definition_and_params(&tc_condition_name) {
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

        // Replace the bad Bar.baz<Foo> values with good Foo.Bar.baz values.
        let prefix = format!("{}.", typeclass.name);
        let safe_instance = unsafe_instance.replace_constants(0, &|c| {
            if c.module_id == typeclass.module_id
                && c.name.starts_with(&prefix)
                && c.params.len() == 1
                && &c.params[0] == instance_type
            {
                let full_name = format!("{}.{}", instance_name, tc_condition_name);
                Some(AcornValue::constant(
                    self.module,
                    full_name,
                    vec![],
                    c.instance_type.clone(),
                ))
            } else {
                None
            }
        });

        Ok(safe_instance)
    }

    // Evaluates an expression that describes a value, with a stack given as context.
    // This must resolve to a completed value, with all types inferred.
    pub fn evaluate_value_with_stack(
        &self,
        stack: &mut Stack,
        project: &Project,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<AcornValue> {
        let potential = self.evaluate_potential_value(stack, project, expression, expected_type)?;
        potential.as_value(expression)
    }

    // Evaluates an expression that could describe a value, but could also describe
    // a constant with an unresolved type.
    fn evaluate_potential_value(
        &self,
        stack: &mut Stack,
        project: &Project,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<PotentialValue> {
        let value = match expression {
            Expression::Singleton(token) => match token.token_type {
                TokenType::Axiom => panic!("axiomatic values should be handled elsewhere"),
                TokenType::ForAll | TokenType::Exists | TokenType::Function => {
                    return Err(token.error("binder keywords cannot be used as values"));
                }
                TokenType::True | TokenType::False => {
                    AcornType::Bool.check_eq(token, expected_type)?;
                    AcornValue::Bool(token.token_type == TokenType::True)
                }
                TokenType::Identifier | TokenType::Numeral | TokenType::SelfToken => {
                    let entity = self.evaluate_name(token, project, stack, None)?;
                    match entity {
                        NamedEntity::Value(value) => {
                            value.check_type(expression, expected_type)?;
                            value
                        }
                        NamedEntity::Type(_)
                        | NamedEntity::Module(_)
                        | NamedEntity::Typeclass(_)
                        | NamedEntity::UnresolvedType(_) => {
                            return Err(token.error("expected a value"));
                        }
                        NamedEntity::UnresolvedValue(u) => {
                            return Ok(PotentialValue::Unresolved(u));
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
                    AcornType::Bool.check_eq(token, expected_type)?;
                    let value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        expr,
                        Some(&AcornType::Bool),
                    )?;
                    AcornValue::Not(Box::new(value))
                }
                token_type => match token_type.to_prefix_magic_method_name() {
                    Some(name) => {
                        let subvalue =
                            self.evaluate_value_with_stack(stack, project, expr, None)?;
                        let value =
                            self.evaluate_instance_attribute(token, project, subvalue, name)?;
                        value.check_type(token, expected_type)?;
                        value
                    }
                    None => {
                        return Err(token.error("unexpected unary operator in value expression"))
                    }
                },
            },
            Expression::Binary(left, token, right) => match token.token_type {
                TokenType::RightArrow | TokenType::Implies => {
                    AcornType::Bool.check_eq(token, expected_type)?;
                    let left_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        left,
                        Some(&AcornType::Bool),
                    )?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&AcornType::Bool),
                    )?;

                    AcornValue::Binary(
                        BinaryOp::Implies,
                        Box::new(left_value),
                        Box::new(right_value),
                    )
                }
                TokenType::Equals => {
                    AcornType::Bool.check_eq(token, expected_type)?;
                    let left_value = self.evaluate_value_with_stack(stack, project, left, None)?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&left_value.get_type()),
                    )?;
                    AcornValue::Binary(
                        BinaryOp::Equals,
                        Box::new(left_value),
                        Box::new(right_value),
                    )
                }
                TokenType::NotEquals => {
                    AcornType::Bool.check_eq(token, expected_type)?;
                    let left_value = self.evaluate_value_with_stack(stack, project, left, None)?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&left_value.get_type()),
                    )?;
                    AcornValue::Binary(
                        BinaryOp::NotEquals,
                        Box::new(left_value),
                        Box::new(right_value),
                    )
                }
                TokenType::And => {
                    AcornType::Bool.check_eq(token, expected_type)?;
                    let left_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        left,
                        Some(&AcornType::Bool),
                    )?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&AcornType::Bool),
                    )?;
                    AcornValue::Binary(BinaryOp::And, Box::new(left_value), Box::new(right_value))
                }
                TokenType::Or => {
                    AcornType::Bool.check_eq(token, expected_type)?;
                    let left_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        left,
                        Some(&AcornType::Bool),
                    )?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&AcornType::Bool),
                    )?;
                    AcornValue::Binary(BinaryOp::Or, Box::new(left_value), Box::new(right_value))
                }
                TokenType::Dot => {
                    let entity = self.evaluate_dot_expression(stack, project, left, right)?;
                    return entity.expect_potential_value(expected_type, expression);
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
            Expression::Apply(function_expr, args_expr) => {
                let function =
                    self.evaluate_potential_value(stack, project, function_expr, None)?;

                // Handle the case where the "args" are actually type parameters.
                let arg_exprs = match args_expr.as_ref() {
                    Expression::Grouping(left_delimiter, e, _) => {
                        let exprs = e.flatten_comma_separated_list();
                        if left_delimiter.token_type == TokenType::LessThan {
                            // This is a type parameter list
                            if let PotentialValue::Unresolved(unresolved) = function {
                                if exprs.len() != unresolved.params.len() {
                                    return Err(left_delimiter.error(&format!(
                                        "expected {} type parameters, but got {}",
                                        unresolved.params.len(),
                                        exprs.len()
                                    )));
                                }
                                let mut named_params = vec![];
                                let mut instance_params = vec![];
                                for (param, expr) in unresolved.params.iter().zip(exprs.iter()) {
                                    let type_param = self.evaluate_type(project, expr)?;
                                    instance_params.push(type_param.clone());
                                    named_params.push((param.name.clone(), type_param));
                                }
                                let resolved_type =
                                    unresolved.generic_type.instantiate(&named_params);
                                let resolved = AcornValue::constant(
                                    unresolved.module_id,
                                    unresolved.name,
                                    instance_params,
                                    resolved_type,
                                );
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
                        project,
                        expression,
                        unresolved,
                        arg_exprs,
                        expected_type,
                    )?,
                    PotentialValue::Resolved(function) => {
                        // Simple, no-type-inference-necessary construction
                        let mut args = vec![];
                        for (i, arg_expr) in arg_exprs.iter().enumerate() {
                            let arg_type: &AcornType = &function_type.arg_types[i];
                            let arg = self.evaluate_value_with_stack(
                                stack,
                                project,
                                arg_expr,
                                Some(arg_type),
                            )?;
                            args.push(arg);
                        }
                        let value = AcornValue::apply(function, args);
                        value.check_type(expression, expected_type)?;
                        value
                    }
                }
            }
            Expression::Grouping(_, e, _) => {
                self.evaluate_value_with_stack(stack, project, e, expected_type)?
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
                let ret_val = match self.evaluate_value_with_stack(stack, project, body, body_type)
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
                    ret_val.as_ref().unwrap().check_type(token, expected_type)?;
                }
                ret_val?
            }
            Expression::IfThenElse(_, cond_exp, if_exp, else_exp, _) => {
                let cond = self.evaluate_value_with_stack(
                    stack,
                    project,
                    cond_exp,
                    Some(&AcornType::Bool),
                )?;
                let if_value =
                    self.evaluate_value_with_stack(stack, project, if_exp, expected_type)?;
                let else_value = self.evaluate_value_with_stack(
                    stack,
                    project,
                    else_exp,
                    Some(&if_value.get_type()),
                )?;
                AcornValue::IfThenElse(Box::new(cond), Box::new(if_value), Box::new(else_value))
            }
            Expression::Match(_, scrutinee_exp, case_exps, _) => {
                let mut expected_type: Option<AcornType> = expected_type.cloned();
                let scrutinee =
                    self.evaluate_value_with_stack(stack, project, scrutinee_exp, None)?;
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
                    let pattern =
                        self.evaluate_value_with_stack(stack, project, pattern_exp, None)?;
                    let result = self.evaluate_value_with_stack(
                        stack,
                        project,
                        result_exp,
                        expected_type.as_ref(),
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

    pub fn evaluate_type_params(
        &self,
        project: &Project,
        exprs: &[TypeParamExpr],
    ) -> compilation::Result<Vec<TypeParam>> {
        let mut answer: Vec<TypeParam> = vec![];
        for expr in exprs {
            let name = expr.name.text().to_string();
            self.check_typename_available(&expr.name, &name)?;
            if answer.iter().any(|tp| tp.name == name) {
                return Err(expr.name.error("duplicate type parameter"));
            }
            let typeclass = match expr.typeclass.as_ref() {
                Some(e) => Some(self.evaluate_typeclass(project, e).unwrap()),
                None => None,
            };
            answer.push(TypeParam {
                name: expr.name.text().to_string(),
                typeclass,
            });
        }
        Ok(answer)
    }

    // Evaluate an expression that creates a new scope for a single value inside it.
    // This could be the statement of a theorem, the definition of a function, or other similar things.
    //
    // It has declarations, introducing new variables and types that exist just for this value,
    // and it has the value itself, which can use those declarations.
    //
    // type_params is a list of tokens for the generic types introduced for this scope.
    // args is a list of the new variables declared for this scope.
    // value_type_expr is an optional expression for the type of the value.
    //   (None means expect a boolean value.)
    // value_expr is the expression for the value itself.
    // function_name, when it is provided, can be used recursively.
    //
    // This function mutates the binding map but sets it back to its original state when finished.
    //
    // Returns a tuple with:
    //   a list of type parameters
    //   a list of argument names
    //   a list of argument types
    //   an optional unbound value. (None means axiom.)
    //   the value type
    //
    // The type parameters are treated as arbitrary types internally to the new scope, but externally
    // they are replaced with type variables.
    //
    // class_type should be provided, fully instantiated, if this is the definition of a member function.
    //
    // The return value is "unbound" in the sense that it has variable atoms that are not
    // bound within any lambda, exists, or forall value. It also may have references to a
    // recursive function that is not yet defined.
    pub fn evaluate_scoped_value(
        &mut self,
        project: &Project,
        type_param_exprs: &[TypeParamExpr],
        args: &[Declaration],
        value_type_expr: Option<&Expression>,
        value_expr: &Expression,
        class_type: Option<&AcornType>,
        function_name: Option<&LocalConstantName>,
    ) -> compilation::Result<(
        Vec<TypeParam>,
        Vec<String>,
        Vec<AcornType>,
        Option<AcornValue>,
        AcornType,
    )> {
        // Bind all the type parameters and arguments
        let type_params = self.evaluate_type_params(project, &type_param_exprs)?;
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
            self.add_constant(function_name, vec![], fn_type, None, None);
        }

        // Evaluate the internal value using our modified bindings
        let internal_value = if value_expr.is_axiom() {
            None
        } else {
            let value = self.evaluate_value_with_stack(
                &mut stack,
                project,
                value_expr,
                Some(&internal_value_type),
            )?;

            if let Some(function_name) = function_name {
                let mut checker = TerminationChecker::new(
                    self.module,
                    function_name.to_string(),
                    internal_arg_types.len(),
                );
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

        // This part is awkward. We might have types parametrized on this function, or they
        // might be parametrized on the class definition. We only want to genericize the
        // parameters that we created. But, we are not quite doing that, we are just genericizing
        // all or nothing.
        // TODO: do this the right way.
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
                    let generic_params = type_params
                        .iter()
                        .map(|param| AcornType::Variable(param.clone()))
                        .collect();
                    let derecursed = internal_value.set_params(
                        self.module,
                        &function_name.to_string(),
                        &generic_params,
                    );
                    Some(derecursed.to_generic())
                } else {
                    // There's no name for this function so it can't possibly be recursive.
                    // This is simpler, but we still need to remove arbitrary local types.
                    Some(internal_value.to_generic())
                }
            } else {
                // No internal value, no external value.
                None
            };
            let external_arg_types = internal_arg_types.iter().map(|t| t.to_generic()).collect();
            let external_value_type = internal_value_type.to_generic();

            Ok((
                type_params,
                arg_names,
                external_arg_types,
                external_value,
                external_value_type,
            ))
        }
    }

    // Finds the names of all constants that are in this module but unknown to this binding map.
    // The unknown constants may not be polymorphic.
    pub fn find_unknown_local_constants(
        &self,
        value: &AcornValue,
        answer: &mut HashMap<String, AcornType>,
    ) {
        match value {
            AcornValue::Variable(_, _) | AcornValue::Bool(_) => {}
            AcornValue::Constant(c) => {
                if c.module_id == self.module && !self.constant_info.contains_key(&c.name) {
                    assert!(c.params.is_empty());
                    answer.insert(c.name.to_string(), c.instance_type.clone());
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

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for going the other way, to create expressions and code strings from values and types.
    ////////////////////////////////////////////////////////////////////////////////

    // Returns an error if this type can't be encoded as an expression.
    // Currently this should only happen when it's defined in a module that isn't directly imported.
    // In theory we could fix this, but we would have to track the web of dependencies.
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

        // Check if it's a type from a module that we have imported
        if let AcornType::Data(module, type_name, params) = acorn_type {
            // See if we have an alias
            let key = (*module, type_name.clone());
            if let Some(name) = self.canonical_to_alias.get(&key) {
                let base_expr = Expression::generate_identifier(name);
                return self.parametrize_expr(base_expr, params);
            }

            // Reference this type via referencing the imported module
            if let Some(module_name) = self.module_to_name.get(module) {
                let base_expr = Expression::generate_identifier_chain(&[module_name, type_name]);
                return self.parametrize_expr(base_expr, params);
            }
        }

        Err(CodeGenError::unnamed_type(acorn_type))
    }

    // Adds parameters, if there are any, to an expression representing a type.
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
        let applied = Expression::Apply(Box::new(base_expr), Box::new(params_expr));
        Ok(applied)
    }

    // We use variables named x0, x1, x2, etc when new temporary variables are needed.
    // Find the next one that's available.
    fn next_indexed_var(&self, prefix: char, next_index: &mut u32) -> String {
        loop {
            let name = LocalConstantName::Unqualified(format!("{}{}", prefix, next_index));
            *next_index += 1;
            if !self.constant_name_in_use(&name) {
                return name.to_string();
            }
        }
    }

    // If this value cannot be expressed in a single chunk of code, returns an error.
    // For example, it might refer to a constant that is not in scope.
    pub fn value_to_code(&self, value: &AcornValue) -> Result<String, CodeGenError> {
        let mut var_names = vec![];
        let mut next_x = 0;
        let mut next_k = 0;
        let expr = self.value_to_expr(value, &mut var_names, &mut next_x, &mut next_k)?;
        Ok(expr.to_string())
    }

    // Given a module and a name, find an expression that refers to the name.
    // The name can be dotted, if it's a class member.
    // Note that:
    //   module, the canonical module of the entity we are trying to express
    // is different from
    //   self.module, the module we are trying to express the name in
    fn name_to_expr(&self, module: ModuleId, name: &str) -> Result<Expression, CodeGenError> {
        let mut parts = name.split('.').collect::<Vec<_>>();

        // Handle numeric literals
        if parts.len() == 2 && parts[1].chars().all(|ch| ch.is_ascii_digit()) {
            let numeral = TokenType::Numeral.new_token(parts[1]);

            // If it's the default type, we don't need to scope it
            if let Some((default_module, default_type_name)) = &self.default {
                if *default_module == module && default_type_name == parts[0] {
                    return Ok(Expression::Singleton(numeral));
                }
            }

            // Otherwise, we need to scope it by the type
            let numeric_type = self.name_to_expr(module, parts[0])?;
            return Ok(Expression::Binary(
                Box::new(numeric_type),
                TokenType::Dot.generate(),
                Box::new(Expression::Singleton(numeral)),
            ));
        }

        if parts.len() > 2 {
            return Err(CodeGenError::UnhandledValue("unexpected dots".to_string()));
        }

        // Handle local constants
        if module == self.module {
            // TODO: this generates an identifier token with a dot, which is wrong
            return Ok(Expression::generate_identifier(name));
        }

        // Check if there's a local alias for this constant.
        let key = (module, name.to_string());
        if let Some(alias) = self.canonical_to_alias.get(&key) {
            return Ok(Expression::generate_identifier(alias));
        }

        // If it's a member function, check if there's a local alias for its struct.
        if parts.len() == 2 {
            let name = parts[0].to_string();
            let key = (module, name);
            if let Some(type_alias) = self.canonical_to_alias.get(&key) {
                let lhs = Expression::generate_identifier(type_alias);
                let rhs = Expression::generate_identifier(parts[1]);
                return Ok(Expression::Binary(
                    Box::new(lhs),
                    TokenType::Dot.generate(),
                    Box::new(rhs),
                ));
            }
        }

        // Refer to this constant using its module
        match self.module_to_name.get(&module) {
            Some(module_name) => {
                parts.insert(0, module_name);
                Ok(Expression::generate_identifier_chain(&parts))
            }
            None => Err(CodeGenError::UnimportedModule(module, name.to_string())),
        }
    }

    // If use_x is true we use x-variables; otherwise we use k-variables.
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
        let subresult = self.value_to_expr(value, var_names, next_x, next_k)?;
        var_names.truncate(initial_var_names_len);
        Ok(Expression::Binder(
            token_type.generate(),
            decls,
            Box::new(subresult),
            TokenType::RightBrace.generate(),
        ))
    }

    // Convert an AcornValue to an Expression.
    fn value_to_expr(
        &self,
        value: &AcornValue,
        var_names: &mut Vec<String>,
        next_x: &mut u32,
        next_k: &mut u32,
    ) -> Result<Expression, CodeGenError> {
        match value {
            AcornValue::Variable(i, _) => {
                Ok(Expression::generate_identifier(&var_names[*i as usize]))
            }
            AcornValue::Application(fa) => {
                let mut args = vec![];
                for arg in &fa.args {
                    args.push(self.value_to_expr(arg, var_names, next_x, next_k)?);
                }

                if let Some(name) = fa.function.is_member(&fa.args[0].get_type()) {
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
                        let applied = Expression::Apply(
                            Box::new(bound),
                            Box::new(Expression::generate_paren_grouping(args)),
                        );
                        return Ok(applied);
                    }
                }

                let f = self.value_to_expr(&fa.function, var_names, next_x, next_k)?;
                let grouped_args = Expression::generate_paren_grouping(args);
                Ok(Expression::Apply(Box::new(f), Box::new(grouped_args)))
            }
            AcornValue::Binary(op, left, right) => {
                let left = self.value_to_expr(left, var_names, next_x, next_k)?;
                let right = self.value_to_expr(right, var_names, next_x, next_k)?;
                let token = op.token_type().generate();
                Ok(Expression::Binary(Box::new(left), token, Box::new(right)))
            }
            AcornValue::Not(x) => {
                let x = self.value_to_expr(x, var_names, next_x, next_k)?;
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
                // Here we are assuming that the context will be enough to disambiguate
                // the type of the templated name.
                // I'm not sure if this is a good assumption.
                self.name_to_expr(c.module_id, &c.name)
            }
            AcornValue::IfThenElse(condition, if_value, else_value) => {
                let condition = self.value_to_expr(condition, var_names, next_x, next_k)?;
                let if_value = self.value_to_expr(if_value, var_names, next_x, next_k)?;
                let else_value = self.value_to_expr(else_value, var_names, next_x, next_k)?;
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

    // Check that the given name actually does have this type in the environment.
    pub fn expect_type(&self, name: &str, type_string: &str) {
        let env_type = match self.constant_name_to_type.get(name) {
            Some(t) => t,
            None => panic!("{} not found", name),
        };
        assert_eq!(env_type.to_string(), type_string);
    }

    // Check that this code, when converted to a value and back to code, is the same.
    pub fn expect_good_code(&self, input_code: &str) {
        let project = Project::new_mock();
        let expression = Expression::expect_value(input_code);
        let value = self
            .evaluate_value(&project, &expression, None)
            .expect("evaluate_value failed");
        let output_code = self.value_to_code(&value).expect("value_to_code failed");
        assert_eq!(input_code, output_code);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_env_types() {
        let mut b = BindingMap::new(FIRST_NORMAL);
        b.assert_type_ok("Bool");
        b.assert_type_ok("Bool -> Bool");
        b.assert_type_ok("Bool -> (Bool -> Bool)");
        b.assert_type_ok("(Bool -> Bool) -> (Bool -> Bool)");
        b.assert_type_ok("(Bool, Bool) -> Bool");
        b.assert_type_bad("Bool, Bool -> Bool");
        b.assert_type_bad("(Bool, Bool)");
    }
}

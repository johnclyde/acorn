use std::collections::{BTreeMap, HashMap, HashSet};

use tower_lsp::lsp_types::{CompletionItem, CompletionItemKind};

use crate::acorn_type::{AcornType, TypeClass};
use crate::acorn_value::{AcornValue, BinaryOp};
use crate::atom::AtomId;
use crate::code_gen_error::CodeGenError;
use crate::compilation::{self, ErrorSource};
use crate::expression::{Declaration, Expression, Terminator};
use crate::module::{ModuleId, FIRST_NORMAL};
use crate::project::Project;
use crate::termination_checker::TerminationChecker;
use crate::token::{self, Token, TokenIter, TokenType};

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
    type_names: BTreeMap<String, AcornType>,

    // Maps the type object to the name of a type.
    reverse_type_names: HashMap<AcornType, String>,

    // Maps an identifier name to its type.
    // Has entries for both defined constants and aliases.
    identifier_types: HashMap<String, AcornType>,

    // Maps the name of a constant defined in this scope to information about it.
    // Doesn't handle variables defined on the stack, only ones that will be in scope for the
    // entirety of this environment.
    // Doesn't handle aliases.
    // Includes "<datatype>.<constant>" for members.
    constants: BTreeMap<String, ConstantInfo>,

    // The canonical identifier of a constant is the first place it is defined.
    // There may be other names in this environment that refer to the same thing.
    // When we create an AcornValue, we want to use the canonical name.
    // The alias -> canonical name mapping is stored here.
    alias_to_canonical: HashMap<String, (ModuleId, String)>,

    // Whenever a name from some other scope has a local alias in this one,
    // if we're generating code, we prefer to use the local name.
    // Thus, preferred_names maps the canonical identifier to a local alias.
    canonical_to_alias: HashMap<(ModuleId, String), String>,

    // Names that refer to other modules.
    // After "import foo", "foo" refers to a module.
    modules: BTreeMap<String, ModuleId>,

    // The local name for imported modules.
    reverse_modules: HashMap<ModuleId, String>,

    // The default data type to use for numeric literals.
    default: Option<(ModuleId, String)>,

    // Whether this constant is the name of a theorem in this context.
    // Inside the block containing the proof of a theorem, the name is not considered to
    // be a theorem.
    theorems: HashSet<String>,
}

// A generic constant that we don't know the type of yet.
pub struct UnresolvedConstant {
    module_id: ModuleId,

    // The name can have a dot in it, indicating this value is <typename>.<constantname>.
    name: String,

    // The type parameters are all the type variables used in the definition of this constant,
    // in their canonical order. Each of these type parameters should be referenced in the type of
    // the constant itself. Otherwise we would not be able to infer them.
    params: Vec<String>,

    // The generic type uses the params.
    generic_type: AcornType,
}

// A constant that has been described by name, but we might not know the precise type of it yet.
pub enum NamedConstant {
    // (module, constant name, type, type parameters)
    Unresolved(UnresolvedConstant),

    // Something that we do know the type of.
    Resolved(AcornValue),
}

impl NamedConstant {
    pub fn force_value(self) -> AcornValue {
        match self {
            NamedConstant::Unresolved(u) => {
                panic!("tried to force unresolved constant {}", u.name);
            }
            NamedConstant::Resolved(c) => c,
        }
    }
}

#[derive(Clone)]
struct ConstantInfo {
    // The names of the type parameters this constant was defined with, if any.
    // These type parameters can be used in the definition.
    params: Vec<String>,

    // The definition of this constant, if it has one.
    definition: Option<AcornValue>,

    // If this constant is a constructor, store:
    //   the type it constructs
    //   an index of which constructor it is
    //   how many total constructors there are
    constructor: Option<(AcornType, usize, usize)>,
}

// Return an error if the types don't match.
// This doesn't do full polymorphic typechecking, but it will fail if there's no
// way that the types can match, for example if a function expects T -> Nat and
// the value provided is Nat.
// actual_type should be non-generic here.
// expected_type can be generic.
pub fn check_type<'a>(
    source: &dyn ErrorSource,
    expected_type: Option<&AcornType>,
    actual_type: &AcornType,
) -> compilation::Result<()> {
    if let Some(e) = expected_type {
        if e != actual_type {
            return Err(source.error(&format!("expected type {}, but this is {}", e, actual_type)));
        }
    }
    Ok(())
}

fn keys_with_prefix<'a, T>(
    map: &'a BTreeMap<String, T>,
    prefix: &'a str,
) -> impl Iterator<Item = &'a String> {
    map.range(prefix.to_string()..)
        .take_while(move |(key, _)| key.starts_with(prefix))
        .map(|(key, _)| key)
}

// A name can refer to any of these things.
enum NamedEntity {
    Value(AcornValue),
    Type(AcornType),
    Module(ModuleId),

    // A constant that we don't know the type of yet.
    Unresolved(UnresolvedConstant),
}

impl NamedEntity {
    fn expect_value(
        self,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorSource,
    ) -> compilation::Result<AcornValue> {
        match self {
            NamedEntity::Value(value) => {
                check_type(source, expected_type, &value.get_type())?;
                Ok(value)
            }
            NamedEntity::Type(_) => {
                Err(source.error("name refers to a type but we expected a value"))
            }
            NamedEntity::Module(_) => {
                Err(source.error("name refers to a module but we expected a value"))
            }
            NamedEntity::Unresolved(u) => {
                Err(source.error(&format!("name {} has unresolved type", u.name)))
            }
        }
    }

    fn expect_type(self, source: &dyn ErrorSource) -> compilation::Result<AcornType> {
        match self {
            NamedEntity::Value(_) => {
                Err(source.error("name refers to a value but we expected a type"))
            }
            NamedEntity::Type(t) => Ok(t),
            NamedEntity::Module(_) => {
                Err(source.error("name refers to a module but we expected a type"))
            }
            NamedEntity::Unresolved(u) => {
                Err(source.error(&format!("name {} has unresolved type", u.name)))
            }
        }
    }
}

impl BindingMap {
    pub fn new(module: ModuleId) -> Self {
        assert!(module >= FIRST_NORMAL);
        let mut answer = BindingMap {
            module,
            type_names: BTreeMap::new(),
            reverse_type_names: HashMap::new(),
            identifier_types: HashMap::new(),
            constants: BTreeMap::new(),
            alias_to_canonical: HashMap::new(),
            canonical_to_alias: HashMap::new(),
            modules: BTreeMap::new(),
            reverse_modules: HashMap::new(),
            default: None,
            theorems: HashSet::new(),
        };
        answer.add_type_alias("Bool", AcornType::Bool);
        answer
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Simple helper functions.
    ////////////////////////////////////////////////////////////////////////////////

    pub fn name_in_use(&self, name: &str) -> bool {
        self.type_names.contains_key(name)
            || self.identifier_types.contains_key(name)
            || self.modules.contains_key(name)
    }

    fn insert_type_name(&mut self, name: String, acorn_type: AcornType) {
        if self.name_in_use(&name) {
            panic!("type name {} already bound", name);
        }
        // There can be multiple names for a type.
        // If we already have a name for the reverse lookup, we don't overwrite it.
        if !self.reverse_type_names.contains_key(&acorn_type) {
            self.reverse_type_names
                .insert(acorn_type.clone(), name.clone());
        }
        self.type_names.insert(name, acorn_type);
    }

    // Adds a new data type to the binding map.
    // Panics if the name is already bound.
    pub fn add_data_type(&mut self, name: &str) -> AcornType {
        if self.name_in_use(name) {
            panic!("type name {} already bound", name);
        }
        let data_type = AcornType::Data(self.module, name.to_string());
        self.insert_type_name(name.to_string(), data_type.clone());
        data_type
    }

    // Adds a new type name that's an alias for an existing type
    pub fn add_type_alias(&mut self, name: &str, acorn_type: AcornType) {
        if self.name_in_use(name) {
            panic!("type alias {} already bound", name);
        }
        if let AcornType::Data(module, type_name) = &acorn_type {
            self.canonical_to_alias
                .entry((*module, type_name.clone()))
                .or_insert(name.to_string());
        }
        self.insert_type_name(name.to_string(), acorn_type);
    }

    fn add_type_variable(&mut self, name: &str, typeclass: Option<TypeClass>) {
        if self.name_in_use(name) {
            panic!("type variable {} already bound", name);
        }
        let acorn_type = AcornType::Variable(name.to_string(), typeclass);
        self.insert_type_name(name.to_string(), acorn_type);
    }

    // Returns an AcornValue representing this name, if there is one.
    // This can return an unresolved value.
    // Returns None if this name does not refer to a constant.
    pub fn old_get_constant_value(&self, name: &str) -> Option<AcornValue> {
        let constant_type = self.identifier_types.get(name)?.clone();

        // Aliases
        if let Some((canonical_module, canonical_name)) = self.alias_to_canonical.get(name) {
            return Some(AcornValue::new_constant(
                *canonical_module,
                canonical_name.clone(),
                vec![],
                constant_type,
            ));
        }

        // Constants defined here
        let params = self.constants.get(name)?.params.clone();
        if params.is_empty() {
            Some(AcornValue::new_constant(
                self.module,
                name.to_string(),
                vec![],
                constant_type,
            ))
        } else {
            Some(AcornValue::Unresolved(
                self.module,
                name.to_string(),
                constant_type,
                params,
            ))
        }
    }

    // Returns an AcornValue representing this name, if there is one.
    // This can return an unresolved value.
    // Returns None if this name does not refer to a constant.
    pub fn get_constant_value(&self, name: &str) -> Option<NamedConstant> {
        let constant_type = self.identifier_types.get(name)?.clone();

        // Aliases
        if let Some((canonical_module, canonical_name)) = self.alias_to_canonical.get(name) {
            return Some(NamedConstant::Resolved(AcornValue::new_constant(
                *canonical_module,
                canonical_name.clone(),
                vec![],
                constant_type,
            )));
        }

        // Constants defined here
        let params = self.constants.get(name)?.params.clone();
        if params.is_empty() {
            Some(NamedConstant::Resolved(AcornValue::new_constant(
                self.module,
                name.to_string(),
                vec![],
                constant_type,
            )))
        } else {
            Some(NamedConstant::Unresolved(UnresolvedConstant {
                module_id: self.module,
                name: name.to_string(),
                params,
                generic_type: constant_type,
            }))
        }
    }

    // Gets the type for an identifier, not for a type name.
    // E.g. if let x: Nat = 0, then get_type("x") will give you Nat.
    pub fn get_type_for_identifier(&self, identifier: &str) -> Option<&AcornType> {
        self.identifier_types.get(identifier)
    }

    pub fn get_params(&self, identifier: &str) -> Vec<String> {
        match self.constants.get(identifier) {
            Some(info) => info.params.clone(),
            None => vec![],
        }
    }

    // Gets the type for a type name, not for an identifier.
    pub fn get_type_for_name(&self, type_name: &str) -> Option<&AcornType> {
        self.type_names.get(type_name)
    }

    pub fn has_type_name(&self, type_name: &str) -> bool {
        self.type_names.contains_key(type_name)
    }

    pub fn has_identifier(&self, identifier: &str) -> bool {
        self.identifier_types.contains_key(identifier)
    }

    // Returns the defined value, if there is a defined value.
    // If there isn't, returns None.
    pub fn get_definition(&self, name: &str) -> Option<&AcornValue> {
        self.constants.get(name)?.definition.as_ref()
    }

    // Returns the defined value and its parameters in their canonical order.
    // Returns None if there is no definition.
    pub fn get_definition_and_params(&self, name: &str) -> Option<(&AcornValue, &[String])> {
        let info = self.constants.get(name)?;
        Some((info.definition.as_ref()?, &info.params))
    }

    // All other modules that we directly depend on, besides this one.
    // Sorted by the name of the import, so that the order will be consistent.
    pub fn direct_dependencies(&self) -> Vec<ModuleId> {
        self.modules.values().copied().collect()
    }

    pub fn set_default(&mut self, module: ModuleId, type_name: String) {
        self.default = Some((module, type_name));
    }

    // Adds a constant.
    // This can also add members, by providing a name like "Foo.bar".
    pub fn add_constant(
        &mut self,
        name: &str,
        params: Vec<String>,
        constant_type: AcornType,
        definition: Option<AcornValue>,
        constructor: Option<(AcornType, usize, usize)>,
    ) {
        if self.name_in_use(name) {
            panic!("constant name {} already bound", name);
        }
        self.identifier_types
            .insert(name.to_string(), constant_type);

        let info = ConstantInfo {
            params,
            definition,
            constructor,
        };
        self.constants.insert(name.to_string(), info);
    }

    // Be really careful about this, it seems likely to break things.
    fn remove_constant(&mut self, name: &str) {
        if !self.name_in_use(name) {
            panic!("removing constant {} which is already not present", name);
        }
        self.identifier_types.remove(name);
        self.constants.remove(name);
    }

    // Adds a local alias for an already-existing constant.
    pub fn add_alias(
        &mut self,
        name: &str,
        canonical_module: ModuleId,
        canonical_name: String,
        acorn_type: AcornType,
    ) {
        if self.name_in_use(name) {
            panic!("cannot alias name {} because it is already bound", name);
        }
        self.identifier_types.insert(name.to_string(), acorn_type);
        let canonical = (canonical_module, canonical_name);
        if canonical_module != self.module {
            // Prefer this alias locally to using the qualified, canonical name
            self.canonical_to_alias
                .entry(canonical.clone())
                .or_insert(name.to_string());
        }
        self.alias_to_canonical.insert(name.to_string(), canonical);
    }

    pub fn is_constant(&self, name: &str) -> bool {
        self.constants.contains_key(name)
    }

    pub fn mark_as_theorem(&mut self, name: &str) {
        self.theorems.insert(name.to_string());
    }

    pub fn is_theorem(&self, name: &str) -> bool {
        self.theorems.contains(name)
    }

    // Type variables should get removed when they go out of scope.
    fn remove_type_variable(&mut self, name: &str) {
        match self.type_names.remove(name) {
            Some(t) => {
                self.reverse_type_names.remove(&t);
            }
            None => panic!("removing data type {} which is already not present", name),
        }
    }

    // Adds this name to the environment as a module.
    pub fn import_module(&mut self, name: &str, module: ModuleId) {
        if self.name_in_use(name) {
            panic!("module name {} already bound", name);
        }
        self.modules.insert(name.to_string(), module);
        self.reverse_modules.insert(module, name.to_string());
    }

    pub fn is_module(&self, name: &str) -> bool {
        self.modules.contains_key(name)
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

    // Gets completions when we are typing a member name.
    fn get_member_completions(
        &self,
        project: &Project,
        t: &AcornType,
        prefix: &str,
    ) -> Option<Vec<CompletionItem>> {
        let mut answer = vec![];
        if let AcornType::Data(module, type_name) = t {
            let bindings = if *module == self.module {
                &self
            } else {
                project.get_bindings(*module).unwrap()
            };
            let full_prefix = format!("{}.{}", type_name, prefix);
            for key in keys_with_prefix(&bindings.constants, &full_prefix) {
                let completion = CompletionItem {
                    label: key.split('.').last()?.to_string(),
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
                    return self.get_member_completions(project, &t, partial);
                }
                NamedEntity::Value(v) => {
                    let t = v.get_type();
                    return self.get_member_completions(project, &t, partial);
                }
                NamedEntity::Unresolved(u) => {
                    return self.get_member_completions(project, &u.generic_type, partial);
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
            for key in keys_with_prefix(&self.constants, prefix) {
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
            for key in keys_with_prefix(&self.type_names, prefix) {
                if importing {
                    let data_type = self.type_names.get(key)?;
                    match data_type {
                        AcornType::Data(module, name) => {
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
        match expression {
            Expression::Singleton(token) => {
                if token.token_type == TokenType::Axiom {
                    return Err(token.error("axiomatic types can only be created at the top level"));
                }
                if let Some(acorn_type) = self.type_names.get(token.text()) {
                    Ok(acorn_type.clone())
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
                    Ok(AcornType::new_functional(arg_types, return_type))
                }
                TokenType::Dot => {
                    let entity = self.evaluate_entity(&mut Stack::new(), project, expression)?;
                    entity.expect_type(token)
                }
                _ => Err(token.error("unexpected binary operator in type expression")),
            },
            Expression::Apply(left, _) => {
                Err(left.error("unexpected function application in type expression"))
            }
            Expression::Grouping(_, e, _) => self.evaluate_type(project, e),
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
    // expect_self is whether we expect this to be a "self" declaration.
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
    // class_name should be provided if these are the arguments of a new member function.
    pub fn bind_args<'a, I>(
        &self,
        stack: &mut Stack,
        project: &Project,
        declarations: I,
        class_name: Option<&str>,
    ) -> compilation::Result<(Vec<String>, Vec<AcornType>)>
    where
        I: IntoIterator<Item = &'a Declaration>,
    {
        let mut names = Vec::new();
        let mut types = Vec::new();
        for (i, declaration) in declarations.into_iter().enumerate() {
            if class_name.is_some() && i == 0 {
                match declaration {
                    Declaration::SelfToken(_) => {
                        names.push("self".to_string());
                        types.push(AcornType::Data(
                            self.module,
                            class_name.unwrap().to_string(),
                        ));
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
            if self.name_in_use(&name) {
                return Err(declaration
                    .token()
                    .error("cannot redeclare a name in an argument list"));
            }
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
                bindings.constants.get(name).unwrap()
            }
            None => return Err(source.error("invalid pattern")),
        };
        match &info.constructor {
            Some((constructor_type, i, total)) => {
                check_type(source, Some(expected_type), &constructor_type)?;
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
            if self.name_in_use(&name) {
                return Err(name_exp.error(&format!("name '{}' is already bound", name)));
            }
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
        if let Some(value) = self.evaluate_class_variable(project, module, type_name, s) {
            return Ok(value);
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
        let read_fn = match self.evaluate_class_variable(project, module, type_name, "read") {
            Some(f) => f,
            None => {
                return Err(token.error(&format!(
                    "{}.read must be defined to read numeric literals",
                    type_name
                )))
            }
        };
        let value = AcornValue::new_apply(read_fn, vec![initial_num, last_num]);
        Ok(value)
    }

    // Evaluates a name scoped by a type name, like MyClass.foo
    fn evaluate_class_variable(
        &self,
        project: &Project,
        module: ModuleId,
        type_name: &str,
        var_name: &str,
    ) -> Option<AcornValue> {
        let bindings = if module == self.module {
            &self
        } else {
            project.get_bindings(module).unwrap()
        };
        let constant_name = format!("{}.{}", type_name, var_name);
        bindings.old_get_constant_value(&constant_name)
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

    // Evaluates a variable attached to an instance like foo.bar.
    // token is used for reporting errors but may not correspond to anything in particular.
    fn evaluate_instance_variable(
        &self,
        source: &dyn ErrorSource,
        project: &Project,
        instance: AcornValue,
        name: &str,
    ) -> compilation::Result<AcornValue> {
        let base_type = instance.get_type();
        if let AcornType::Data(module, type_name) = base_type {
            let bindings = if module == self.module {
                &self
            } else {
                project.get_bindings(module).unwrap()
            };
            let constant_name = format!("{}.{}", type_name, name);
            let function = match bindings.old_get_constant_value(&constant_name) {
                Some(value) => value,
                None => {
                    return Err(
                        source.error(&format!("unknown instance variable '{}'", constant_name))
                    )
                }
            };
            // We need to typecheck that the apply is okay
            match function.get_type() {
                AcornType::Function(function_type) => {
                    check_type(
                        source,
                        Some(&function_type.arg_types[0]),
                        &instance.get_type(),
                    )?;
                }
                _ => {
                    return Err(source.error("expected member to be a function"));
                }
            };
            Ok(AcornValue::new_apply(function, vec![instance]))
        } else {
            Err(source.error(&format!("objects of type {:?} have no members", base_type)))
        }
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
                let value = self.evaluate_instance_variable(name_token, project, instance, name)?;
                Ok(NamedEntity::Value(value))
            }
            Some(NamedEntity::Type(t)) => {
                if let AcornType::Data(module, type_name) = t {
                    if name_token.token_type == TokenType::Numeral {
                        let value = self.evaluate_number_with_type(
                            name_token,
                            project,
                            module,
                            &type_name,
                            name_token.text(),
                        )?;
                        return Ok(NamedEntity::Value(value));
                    }
                    match self.evaluate_class_variable(project, module, &type_name, name) {
                        Some(value) => Ok(NamedEntity::Value(value)),
                        None => Err(name_token
                            .error(&format!("{} has no member named '{}'", type_name, name))),
                    }
                } else {
                    Err(name_token.error("expected a data type"))
                }
            }
            Some(NamedEntity::Module(module)) => {
                if let Some(bindings) = project.get_bindings(module) {
                    bindings.evaluate_name(name_token, project, stack, None)
                } else {
                    Err(name_token.error("could not load bindings for module"))
                }
            }
            Some(NamedEntity::Unresolved(_)) => {
                Err(name_token.error("cannot access members of unresolved types"))
            }
            None => {
                match name_token.token_type {
                    TokenType::Identifier => {
                        if self.is_module(name) {
                            match self.modules.get(name) {
                                Some(module) => Ok(NamedEntity::Module(*module)),
                                None => Err(name_token.error("unknown module")),
                            }
                        } else if self.has_type_name(name) {
                            match self.get_type_for_name(name) {
                                Some(t) => Ok(NamedEntity::Type(t.clone())),
                                None => Err(name_token.error("unknown type")),
                            }
                        } else if let Some((i, t)) = stack.get(name) {
                            // This is a stack variable
                            Ok(NamedEntity::Value(AcornValue::Variable(*i, t.clone())))
                        } else if let Some(value) = self.old_get_constant_value(name) {
                            Ok(NamedEntity::Value(value))
                        } else {
                            Err(name_token.error(&format!("unknown identifier '{}'", name)))
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

        if let Expression::Binary(left, token, right) = expression {
            if token.token_type == TokenType::Dot {
                return self.evaluate_dot_expression(stack, project, left, right);
            }
        }

        // If it isn't a name or a dot, it must be a value.
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
        let partial = self.evaluate_instance_variable(expression, project, left_value, name)?;
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
                check_type(expression, Some(&f.arg_types[1]), &right_value.get_type())?;
            }
            _ => return Err(expression.error(&format!("unexpected type for '{}' method", name))),
        };

        fa.args.push(right_value);
        let value = AcornValue::new_apply(*fa.function, fa.args);
        check_type(expression, expected_type, &value.get_type())?;
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
        if self.name_in_use(&name_token.text()) {
            return Err(name_token.error(&format!(
                "name {} already bound in this module",
                name_token.text()
            )));
        }
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
                        value.get_type(),
                    );
                    Ok(())
                } else {
                    // I don't see how this branch can be reached.
                    return Err(name_token.error("cannot import non-constant values"));
                }
            }
            NamedEntity::Type(acorn_type) => {
                self.add_type_alias(&name_token.text(), acorn_type);
                Ok(())
            }
            NamedEntity::Module(_) => Err(name_token.error("cannot import modules indirectly")),

            // TODO: we *should* be able to import unresolved types.
            NamedEntity::Unresolved(_) => Err(name_token.error("cannot import unresolved types")),
        }
    }

    // Evaluates an expression that describes a value, with a stack given as context.
    // A value expression could be either a value or an argument list.
    // Returns the value along with its type.
    pub fn evaluate_value_with_stack(
        &self,
        stack: &mut Stack,
        project: &Project,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<AcornValue> {
        match expression {
            Expression::Singleton(token) => match token.token_type {
                TokenType::Axiom => panic!("axiomatic values should be handled elsewhere"),
                TokenType::ForAll | TokenType::Exists | TokenType::Function => {
                    return Err(token.error("binder keywords cannot be used as values"));
                }
                TokenType::True | TokenType::False => {
                    check_type(token, expected_type, &AcornType::Bool)?;
                    Ok(AcornValue::Bool(token.token_type == TokenType::True))
                }
                TokenType::Identifier | TokenType::Numeral | TokenType::SelfToken => {
                    let entity = self.evaluate_name(token, project, stack, None)?;
                    Ok(entity.expect_value(expected_type, token)?)
                }
                token_type => Err(token.error(&format!(
                    "identifier expression has token type {:?}",
                    token_type
                ))),
            },
            Expression::Unary(token, expr) => match token.token_type {
                TokenType::Not => {
                    check_type(token, expected_type, &AcornType::Bool)?;
                    let value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        expr,
                        Some(&AcornType::Bool),
                    )?;
                    Ok(AcornValue::Not(Box::new(value)))
                }
                token_type => match token_type.to_prefix_magic_method_name() {
                    Some(name) => {
                        let subvalue =
                            self.evaluate_value_with_stack(stack, project, expr, None)?;
                        let value =
                            self.evaluate_instance_variable(token, project, subvalue, name)?;
                        check_type(token, expected_type, &value.get_type())?;
                        Ok(value)
                    }
                    None => Err(token.error("unexpected unary operator in value expression")),
                },
            },
            Expression::Binary(left, token, right) => match token.token_type {
                TokenType::RightArrow | TokenType::Implies => {
                    check_type(token, expected_type, &AcornType::Bool)?;
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

                    Ok(AcornValue::Binary(
                        BinaryOp::Implies,
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::Equals => {
                    check_type(token, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value_with_stack(stack, project, left, None)?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&left_value.get_type()),
                    )?;
                    Ok(AcornValue::Binary(
                        BinaryOp::Equals,
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::NotEquals => {
                    check_type(token, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value_with_stack(stack, project, left, None)?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&left_value.get_type()),
                    )?;
                    Ok(AcornValue::Binary(
                        BinaryOp::NotEquals,
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::And => {
                    check_type(token, expected_type, &AcornType::Bool)?;
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
                    Ok(AcornValue::Binary(
                        BinaryOp::And,
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::Or => {
                    check_type(token, expected_type, &AcornType::Bool)?;
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
                    Ok(AcornValue::Binary(
                        BinaryOp::Or,
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::Dot => {
                    let entity = self.evaluate_dot_expression(stack, project, left, right)?;
                    Ok(entity.expect_value(expected_type, token)?)
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
                    ),
                    None => Err(expression.error("unhandled binary operator in value expression")),
                },
            },
            Expression::Apply(function_expr, args_expr) => {
                let function =
                    self.evaluate_value_with_stack(stack, project, function_expr, None)?;
                let function_type = function.get_type();

                let function_type = match function_type {
                    AcornType::Function(f) => f,
                    _ => {
                        return Err(function_expr.error("expected a function"));
                    }
                };

                let arg_exprs = args_expr.flatten_list(false)?;

                if function_type.arg_types.len() < arg_exprs.len() {
                    return Err(args_expr.error(&format!(
                        "expected <= {} arguments, but got {}",
                        function_type.arg_types.len(),
                        arg_exprs.len()
                    )));
                }

                // Check if we have to do type inference.
                if let AcornValue::Unresolved(c_module, c_name, c_type, c_params) = function {
                    // Do the actual inference
                    let mut args = vec![];
                    let mut mapping = HashMap::new();
                    for (i, arg_expr) in arg_exprs.iter().enumerate() {
                        let arg_type: &AcornType = &function_type.arg_types[i];
                        let arg_value =
                            self.evaluate_value_with_stack(stack, project, arg_expr, None)?;
                        if !arg_type.match_instance(&arg_value.get_type(), &mut mapping) {
                            return Err(arg_expr.error(&format!(
                                "expected type {}, but got {}",
                                arg_type,
                                arg_value.get_type()
                            )));
                        }
                        args.push(arg_value);
                    }

                    // Determine the parameters for the instance function
                    let mut named_params = vec![];
                    let mut instance_params = vec![];
                    for param_name in &c_params {
                        match mapping.get(param_name) {
                            Some(t) => {
                                named_params.push((param_name.clone(), t.clone()));
                                instance_params.push(t.clone());
                            }
                            None => {
                                return Err(function_expr.error(&format!(
                                    "parameter {} could not be inferred",
                                    param_name
                                )))
                            }
                        }
                    }
                    let resolved_type = c_type.instantiate(&named_params);

                    let instance_fn =
                        AcornValue::new_constant(c_module, c_name, instance_params, resolved_type);
                    let value = AcornValue::new_apply(instance_fn, args);
                    if expected_type.is_some() {
                        check_type(&**function_expr, expected_type, &value.get_type())?;
                    }
                    return Ok(value);
                }

                // Simple, no-type-inference-necessary construction
                let mut args = vec![];
                for (i, arg_expr) in arg_exprs.iter().enumerate() {
                    let arg_type: &AcornType = &function_type.arg_types[i];
                    let arg =
                        self.evaluate_value_with_stack(stack, project, arg_expr, Some(arg_type))?;
                    args.push(arg);
                }
                Ok(AcornValue::new_apply(function, args))
            }
            Expression::Grouping(_, e, _) => {
                self.evaluate_value_with_stack(stack, project, e, expected_type)
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
                if ret_val.is_ok()
                    && token.token_type == TokenType::Function
                    && expected_type.is_some()
                {
                    // We could check this before creating the value rather than afterwards.
                    // It seems theoretically faster but I'm not sure if there's any reason to.
                    check_type(token, expected_type, &ret_val.as_ref().unwrap().get_type())?;
                }
                ret_val
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
                Ok(AcornValue::IfThenElse(
                    Box::new(cond),
                    Box::new(if_value),
                    Box::new(else_value),
                ))
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
                Ok(AcornValue::Match(Box::new(scrutinee), cases))
            }
        }
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
    //   a list of type parameter names
    //   a list of argument names
    //   a list of argument types
    //   an optional unbound value. (None means axiom.)
    //   the value type
    //
    // Wherever the argument types and the value type include the type parameters, they will
    // be type variables.
    //
    // class_name should be provided if this is the definition of a member function.
    //
    // The return value is "unbound" in the sense that it has variable atoms that are not
    // bound within any lambda, exists, or forall value. It also may have references to a
    // recursive function that is not yet defined.
    pub fn evaluate_scoped_value(
        &mut self,
        project: &Project,
        type_param_tokens: &[Token],
        args: &[Declaration],
        value_type_expr: Option<&Expression>,
        value_expr: &Expression,
        class_name: Option<&str>,
        function_name: Option<&str>,
    ) -> compilation::Result<(
        Vec<String>,
        Vec<String>,
        Vec<AcornType>,
        Option<AcornValue>,
        AcornType,
    )> {
        // Bind all the type parameters and arguments
        let mut type_param_names: Vec<String> = vec![];
        for token in type_param_tokens {
            if self.type_names.contains_key(token.text()) {
                return Err(token.error("cannot redeclare a type in a generic type list"));
            }
            self.add_type_variable(token.text(), None);
            type_param_names.push(token.text().to_string());
        }
        let mut stack = Stack::new();
        let (arg_names, arg_types) = self.bind_args(&mut stack, project, args, class_name)?;

        // Check for possible errors in the specification.
        // Each type has to be used by some argument (although you can imagine lifting this rule).
        for (i, type_param_name) in type_param_names.iter().enumerate() {
            if !arg_types
                .iter()
                .any(|a| a.has_type_variable(&type_param_name))
            {
                return Err(type_param_tokens[i].error(&format!(
                    "type parameter {} is not used in the function arguments",
                    type_param_names[i]
                )));
            }
        }

        // Figure out types.
        let value_type = match value_type_expr {
            Some(e) => self.evaluate_type(project, e)?,
            None => AcornType::Bool,
        };

        if let Some(function_name) = function_name {
            let fn_type = AcornType::new_functional(arg_types.clone(), value_type.clone());
            self.add_constant(function_name, type_param_names.clone(), fn_type, None, None);
        }

        // Evaluate the inner value using our modified bindings
        let value = if value_expr.is_axiom() {
            None
        } else {
            let value =
                self.evaluate_value_with_stack(&mut stack, project, value_expr, Some(&value_type))?;

            if let Some(function_name) = function_name {
                let mut checker = TerminationChecker::new(
                    self.module,
                    function_name.to_string(),
                    arg_types.len(),
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
        for name in type_param_names.iter().rev() {
            self.remove_type_variable(&name);
        }
        if let Some(function_name) = function_name {
            self.remove_constant(&function_name);
        }

        Ok((type_param_names, arg_names, arg_types, value, value_type))
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
            AcornValue::Unresolved(module, name, t, _) => {
                if *module == self.module && !self.constants.contains_key(name) {
                    answer.insert(name.to_string(), t.clone());
                }
            }
            AcornValue::Constant(c) => {
                if c.module_id == self.module && !self.constants.contains_key(&c.name) {
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
                Expression::generate_grouping(args)
            };
            let rhs = self.type_to_expr(&ft.return_type)?;
            return Ok(Expression::Binary(
                Box::new(lhs),
                TokenType::RightArrow.generate(),
                Box::new(rhs),
            ));
        }

        // Check if there's a local alias for this type
        if let Some(name) = self.reverse_type_names.get(acorn_type) {
            return Ok(Expression::generate_identifier(name));
        }

        // Check if it's a type from a module that we have imported
        if let AcornType::Data(module, type_name) = acorn_type {
            if let Some(module_name) = self.reverse_modules.get(module) {
                return Ok(Expression::generate_identifier_chain(&[
                    &module_name,
                    &type_name,
                ]));
            }
        }

        Err(CodeGenError::unnamed_type(acorn_type))
    }

    // We use variables named x0, x1, x2, etc when new temporary variables are needed.
    // Find the next one that's available.
    fn next_x_var(&self, next_x: &mut u32) -> String {
        loop {
            let name = format!("x{}", next_x);
            *next_x += 1;
            if !self.name_in_use(&name) {
                return name;
            }
        }
    }

    // We use variables named k0, k1, k2, etc when new constant names are needed.
    // Find the next one that's available.
    fn next_k_var(&self, next_k: &mut u32) -> String {
        loop {
            let name = format!("k{}", next_k);
            *next_k += 1;
            if !self.name_in_use(&name) {
                return name;
            }
        }
    }

    // If this value cannot be expressed in a single chunk of code, returns an error.
    // For example, it might refer to a constant that is not in scope.
    // Takes a next_k parameter so that it can be used sequentially in the middle of
    // a bunch of code generation.
    pub fn value_to_code(&self, value: &AcornValue) -> Result<String, CodeGenError> {
        let mut var_names = vec![];
        let mut next_x = 0;
        let mut next_k = 0;
        let expr = self.value_to_expr(value, &mut var_names, &mut next_x, &mut next_k)?;
        Ok(expr.to_string())
    }

    // Given a module and a name, find an expression that refers to the name.
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
            let data_type = AcornType::Data(module, parts[0].to_string());
            if let Some(type_alias) = self.reverse_type_names.get(&data_type) {
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
        match self.reverse_modules.get(&module) {
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
                self.next_x_var(next_x)
            } else {
                self.next_k_var(next_k)
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
            AcornValue::Unresolved(module, name, _, _) => self.name_to_expr(*module, name),
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
                            Box::new(Expression::generate_grouping(args)),
                        );
                        return Ok(applied);
                    }
                }

                let f = self.value_to_expr(&fa.function, var_names, next_x, next_k)?;
                let grouped_args = Expression::generate_grouping(args);
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
            .evaluate_type(&Project::new_mock(), &expression)
            .is_err());
    }

    // Check that the given name actually does have this type in the environment.
    pub fn expect_type(&self, name: &str, type_string: &str) {
        let env_type = match self.identifier_types.get(name) {
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

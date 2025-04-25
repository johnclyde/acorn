use std::collections::{HashMap, HashSet};
use std::vec;

use tower_lsp::lsp_types::Range;

use crate::acorn_type::{AcornType, Class, PotentialType, TypeParam, Typeclass};
use crate::acorn_value::{AcornValue, BinaryOp};
use crate::atom::AtomId;
use crate::binding_map::{BindingMap, Stack};
use crate::block::{Block, BlockParams, Node, NodeCursor};
use crate::compilation::{self, Error, ErrorSource, PanicOnError};
use crate::fact::Fact;
use crate::module::ModuleId;
use crate::names::{DefinedName, GlobalName, LocalName};
use crate::potential_value::PotentialValue;
use crate::project::{LoadError, Project};
use crate::proposition::Proposition;
use crate::source::{Source, SourceType};
use crate::statement::{
    Body, ClassStatement, DefineStatement, FunctionSatisfyStatement, InductiveStatement,
    InstanceStatement, LetStatement, Statement, StatementInfo, StructureStatement,
    TheoremStatement, TypeclassStatement, VariableSatisfyStatement,
};
use crate::token::{Token, TokenIter, TokenType};

/// Each line has a LineType, to handle line-based user interface.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LineType {
    /// Only used within subenvironments.
    /// The line relates to the block, but is outside the opening brace for this block.
    Opening,

    /// This line corresponds to a node inside the environment.
    /// The usize is an index into the nodes array.
    /// If the node represents a block, this line should also have a line type in the
    /// subenvironment within the block.
    Node(usize),

    /// Either only whitespace is here, or a comment.
    Empty,

    /// Lines with other sorts of statements besides prop statements.
    Other,

    /// Only used within subenvironments.
    /// The line has the closing brace for this block.
    Closing,
}

/// The Environment takes Statements as input and processes them.
/// It does not prove anything directly, but it is responsible for determining which
/// things need to be proved, and which statements are usable in which proofs.
/// It creates subenvironments for nested blocks.
/// It does not have to be efficient enough to run in the inner loop of the prover.
pub struct Environment {
    pub module_id: ModuleId,

    /// What all the names mean in this environment
    pub bindings: BindingMap,

    /// The nodes structure is fundamentally linear.
    /// Each node depends only on the nodes before it.
    pub nodes: Vec<Node>,

    /// The region in the source document where a name was defined
    definition_ranges: HashMap<DefinedName, Range>,

    /// Whether a plain "false" is anywhere in this environment.
    /// This indicates that the environment is supposed to have contradictory facts.
    pub includes_explicit_false: bool,

    /// For the base environment, first_line is zero.
    /// first_line is usually nonzero when the environment is a subenvironment.
    /// line_types[0] corresponds to first_line in the source document.
    pub first_line: u32,
    pub line_types: Vec<LineType>,

    /// Implicit blocks aren't written in the code; they are created for theorems that
    /// the user has asserted without proof.
    pub implicit: bool,

    /// The depth if you think of the environments in a module like a tree structure.
    /// The root environment for a module has depth zero.
    /// Each child node has a depth of one plus its parent.
    pub depth: u32,
}

impl Environment {
    pub fn new(module_id: ModuleId) -> Self {
        Environment {
            module_id,
            bindings: BindingMap::new(module_id),
            nodes: Vec::new(),
            definition_ranges: HashMap::new(),
            includes_explicit_false: false,
            first_line: 0,
            line_types: Vec::new(),
            implicit: false,
            depth: 0,
        }
    }

    /// Create a child environment.
    /// theorem_name is provided if this is the newly-created environment for proving a theorem.
    pub fn create_child(&self, first_line: u32, implicit: bool) -> Self {
        Environment {
            module_id: self.module_id,
            bindings: self.bindings.clone(),
            nodes: Vec::new(),
            definition_ranges: self.definition_ranges.clone(),
            includes_explicit_false: false,
            first_line,
            line_types: Vec::new(),
            implicit,
            depth: self.depth + 1,
        }
    }

    fn next_line(&self) -> u32 {
        self.line_types.len() as u32 + self.first_line
    }

    pub fn last_line(&self) -> u32 {
        self.next_line() - 1
    }

    /// Add line types for the given range, inserting empties as needed.
    /// If the line already has a type, do nothing.
    pub fn add_line_types(&mut self, line_type: LineType, first: u32, last: u32) {
        while self.next_line() < first {
            self.line_types.push(LineType::Empty);
        }
        while self.next_line() <= last {
            self.line_types.push(line_type);
        }
    }

    fn add_other_lines(&mut self, statement: &Statement) {
        self.add_line_types(
            LineType::Other,
            statement.first_line(),
            statement.last_line(),
        );
    }

    /// Associate the provided node and range.
    fn add_node_lines(&mut self, index: usize, range: &Range) {
        self.add_line_types(LineType::Node(index), range.start.line, range.end.line);
    }

    pub fn get_line_type(&self, line: u32) -> Option<LineType> {
        if line < self.first_line {
            return None;
        }
        let index = (line - self.first_line) as usize;
        if index < self.line_types.len() {
            Some(self.line_types[index])
        } else {
            None
        }
    }

    /// Adds a node to the environment tree.
    /// Returns the index of the newly added node.
    pub fn add_node(&mut self, node: Node) -> usize {
        self.nodes.push(node);
        self.nodes.len() - 1
    }

    /// Adds a node to represent the definition of the provided
    /// constant.
    pub fn add_definition(&mut self, constant_name: &DefinedName) {
        let definition = if let Some(d) = self.bindings.get_definition(&constant_name) {
            d.clone()
        } else {
            return;
        };

        // This constant can be generic, with type variables in it.
        let potential = self
            .bindings
            .get_constant_value(&PanicOnError, constant_name)
            .expect("bad add_definition call");
        let range = self.definition_ranges.get(&constant_name).unwrap().clone();
        let name = constant_name.to_string();
        let source = Source::constant_definition(
            self.module_id,
            range,
            self.depth,
            potential.clone().to_generic_value(),
            &name,
        );

        self.add_node(Node::definition(potential, definition, source));
    }

    /// Defines a new constant, adding a node for its definition and also tracking its definition range.
    fn define_constant(
        &mut self,
        name: DefinedName,
        params: Vec<TypeParam>,
        constant_type: AcornType,
        definition: Option<AcornValue>,
        range: Range,
    ) {
        self.bindings
            .add_constant(name.clone(), params, constant_type, definition, None);
        self.definition_ranges.insert(name.clone(), range);
        self.add_definition(&name);
    }

    pub fn get_definition(&self, name: &DefinedName) -> Option<&AcornValue> {
        self.bindings.get_definition(name)
    }

    /// Returns an error if this isn't the canonical name (and module) for the class.
    fn check_canonical_classname(
        &self,
        name_token: &Token,
        class_type: &AcornType,
    ) -> compilation::Result<()> {
        match &class_type {
            AcornType::Data(class, _) => {
                if class.module_id != self.module_id {
                    return Err(
                        name_token.error("we can only bind members to types in the current module")
                    );
                }
                if &class.name != &name_token.text() {
                    return Err(name_token.error("we cannot bind members to type aliases"));
                }
            }
            _ => {
                return Err(name_token.error(&format!("we can only bind members to data types")));
            }
        }
        Ok(())
    }

    /// Adds a conditional block to the environment.
    /// Takes the condition, the range to associate with the condition, the first line of
    /// the conditional block, and finally the body itself.
    /// If this is an "else" block, we pass in the claim from the "if" part of the block.
    /// This way, if the claim is the same, we can simplify by combining them when externalized.
    /// Returns the last claim in the block, if we didn't have an if-claim to match against.
    fn add_conditional(
        &mut self,
        project: &mut Project,
        condition: AcornValue,
        range: Range,
        first_line: u32,
        last_line: u32,
        body: &Body,
        if_claim: Option<AcornValue>,
    ) -> compilation::Result<Option<AcornValue>> {
        if body.statements.is_empty() {
            // Conditional blocks with an empty body can just be ignored
            return Ok(None);
        }
        let block = Block::new(
            project,
            &self,
            vec![],
            vec![],
            BlockParams::Conditional(&condition, range),
            first_line,
            last_line,
            Some(body),
        )?;
        let (outer_claim, claim_range) = block.externalize_last_claim(self, &body.right_brace)?;

        let matching_branches = if let Some(if_claim) = if_claim {
            if outer_claim == if_claim {
                true
            } else {
                false
            }
        } else {
            false
        };
        let (external_claim, last_claim) = if matching_branches {
            (outer_claim, None)
        } else {
            (
                AcornValue::Binary(
                    BinaryOp::Implies,
                    Box::new(condition),
                    Box::new(outer_claim.clone()),
                ),
                Some(outer_claim),
            )
        };
        let source = Source::anonymous(self.module_id, claim_range, self.depth);
        let prop = Proposition::monomorphic(external_claim, source);
        let index = self.add_node(Node::block(project, self, block, Some(prop)));
        self.add_line_types(
            LineType::Node(index),
            first_line,
            body.right_brace.line_number,
        );
        Ok(last_claim)
    }

    /// Adds a "let" statement to the environment.
    /// This can also be in a class, typeclass, or instance block.
    /// If this is in a class block, the class parameters are provided.
    fn add_let_statement(
        &mut self,
        project: &Project,
        constant_name: DefinedName,
        ls: &LetStatement,
        range: Range,
        class_params: Option<&Vec<TypeParam>>,
    ) -> compilation::Result<()> {
        if ls.name == "self" || ls.name == "new" {
            return Err(ls.name_token.error(&format!(
                "'{}' is a reserved word. use a different name",
                ls.name
            )));
        }

        if self.bindings.constant_name_in_use(&constant_name) {
            return Err(ls.name_token.error(&format!(
                "constant name '{}' already defined in this scope",
                &constant_name
            )));
        }

        if self.depth > 0 && !ls.type_params.is_empty() {
            return Err(ls
                .name_token
                .error("parametrized constants may only be defined at the top level"));
        }

        let local_type_params = self
            .bindings
            .evaluate_type_params(project, &ls.type_params)?;
        for param in &local_type_params {
            self.bindings.add_arbitrary_type(param.clone());
        }

        let acorn_type = self.bindings.evaluate_type(project, &ls.type_expr)?;
        if ls.name_token.token_type == TokenType::Numeral {
            let class_name = match constant_name.as_attribute() {
                Some((class_name, _)) => class_name.to_string(),
                _ => {
                    return Err(ls
                        .name_token
                        .error("numeric literals must be class members"))
                }
            };
            let class = Class {
                module_id: self.module_id,
                name: class_name,
            };
            if acorn_type != AcornType::Data(class, vec![]) {
                return Err(ls
                    .type_expr
                    .error("numeric class variables must be the class type"));
            }
        }
        let value = if ls.value.is_axiom() {
            None
        } else {
            let v = self
                .bindings
                .evaluate_value(project, &ls.value, Some(&acorn_type))?;
            Some(v)
        };

        // Reset the bindings
        for param in local_type_params.iter().rev() {
            self.bindings.remove_type(&param.name);
        }

        // Genericize the value being defined
        let type_params = match class_params {
            Some(p) => {
                if !local_type_params.is_empty() {
                    return Err(ls
                        .name_token
                        .error("class parameters and let parameters cannot be used together"));
                }
                p.clone()
            }
            None => local_type_params,
        };
        let acorn_type = acorn_type.genericize(&type_params);
        let value = value.map(|v| v.genericize(&type_params));

        // Check for aliasing
        if let Some(value) = &value {
            if let Some(global_name) = value.as_simple_constant() {
                match &constant_name {
                    // For local names, 'let x = y' should create an alias for y, not a new constant.
                    // Aliases for local names are handled in the binding map.
                    DefinedName::Local(local_name) => {
                        self.bindings.add_alias(
                            local_name.clone(),
                            global_name.clone(),
                            PotentialValue::Resolved(value.clone()),
                        );
                        return Ok(());
                    }
                    // Aliases for instance names are handled in normalization.
                    // Just do nothing here.
                    DefinedName::Instance(_) => {}
                }
            }
        }

        self.define_constant(constant_name, type_params, acorn_type, value, range);
        Ok(())
    }

    /// Adds a "define" statement to the environment, that may be within a class block.
    ///
    /// The self type is the type of the "self" variable. If it's None, there can't be a self.
    ///
    /// The class params are the parameters for the overall class statement, if we are within one.
    /// They will become the parameters of the newly defined function.
    fn add_define_statement(
        &mut self,
        project: &Project,
        constant_name: DefinedName,
        self_type: Option<&AcornType>,
        class_params: Option<&Vec<TypeParam>>,
        ds: &DefineStatement,
        range: Range,
    ) -> compilation::Result<()> {
        if ds.name == "new" || ds.name == "self" {
            return Err(ds.name_token.error(&format!(
                "'{}' is a reserved word. use a different name",
                ds.name
            )));
        }
        if self.depth > 0 && !ds.type_params.is_empty() {
            return Err(ds
                .name_token
                .error("parametrized functions may only be defined at the top level"));
        }
        if self_type.is_some() && !ds.type_params.is_empty() {
            return Err(ds
                .name_token
                .error("member functions may not have type parameters"));
        }
        if self.bindings.constant_name_in_use(&constant_name) {
            return Err(ds.name_token.error(&format!(
                "function name '{}' already defined in this scope",
                constant_name
            )));
        }

        // Calculate the function value
        let (fn_param_names, _, arg_types, unbound_value, value_type) =
            self.bindings.evaluate_scoped_value(
                project,
                &ds.type_params,
                &ds.args,
                Some(&ds.return_type),
                &ds.return_value,
                self_type,
                constant_name.as_local(),
            )?;

        if let Some(class_type) = self_type {
            if &arg_types[0] != class_type {
                return Err(ds.args[0].token().error("self must be the class type"));
            }

            if ds.name == "read" {
                if arg_types.len() != 2 || &arg_types[1] != class_type || &value_type != class_type
                {
                    return Err(ds.name_token.error(&format!(
                        "{}.read should be type ({}, {}) -> {}",
                        class_type, class_type, class_type, class_type
                    )));
                }
            }
        }

        // The typical definition case
        if let Some(v) = unbound_value {
            let mut fn_value = AcornValue::lambda(arg_types, v);

            let params = if let Some(class_params) = class_params {
                // When a class is parametrized, the member gets parameters from the class.
                fn_value = fn_value.genericize(&class_params);
                class_params.clone()
            } else {
                // When there's no class, we just have the function's own type parameters.
                fn_param_names
            };

            // Add the function value to the environment
            self.define_constant(
                constant_name,
                params,
                fn_value.get_type(),
                Some(fn_value),
                range,
            );
            return Ok(());
        }

        // Defining an axiom
        let new_axiom_type = AcornType::functional(arg_types, value_type);
        self.define_constant(constant_name, fn_param_names, new_axiom_type, None, range);
        Ok(())
    }

    fn add_theorem_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ts: &TheoremStatement,
    ) -> compilation::Result<()> {
        // Figure out the range for this theorem definition.
        // It's smaller than the whole theorem statement because it doesn't
        // include the proof block.
        let range = Range {
            start: statement.first_token.start_pos(),
            end: ts.claim_right_brace.end_pos(),
        };

        if let Some(name) = &ts.name {
            self.bindings
                .check_unqualified_name_available(&statement.first_token, &name)?;
            let name = DefinedName::unqualified(name);
            self.definition_ranges.insert(name, range.clone());
        }

        let (type_params, arg_names, arg_types, value, _) = self.bindings.evaluate_scoped_value(
            project,
            &ts.type_params,
            &ts.args,
            None,
            &ts.claim,
            None,
            None,
        )?;

        let unbound_claim = value.ok_or_else(|| ts.claim.error("theorems must have values"))?;
        unbound_claim.check_type(&ts.claim, Some(&AcornType::Bool))?;

        let is_citation = self.bindings.is_citation(project, &unbound_claim);
        if is_citation && ts.body.is_some() {
            return Err(statement.error("citations do not need proof blocks"));
        }

        let mut block_args = vec![];
        for (arg_name, arg_type) in arg_names.iter().zip(&arg_types) {
            block_args.push((arg_name.clone(), arg_type.clone()));
        }

        // Externally we use the theorem in unnamed, "forall" form
        let external_claim = AcornValue::forall(arg_types.clone(), unbound_claim.clone());
        if let Err(message) = external_claim.validate() {
            return Err(ts.claim.error(&message));
        }

        let (premise, goal) = match &unbound_claim {
            AcornValue::Binary(BinaryOp::Implies, left, right) => {
                let premise_range = match ts.claim.premise() {
                    Some(p) => p.range(),
                    None => {
                        // I don't think this should happen, but it's awkward for the
                        // compiler to enforce, so pick a not-too-wrong default.
                        ts.claim.range()
                    }
                };
                (
                    Some((left.to_arbitrary(), premise_range)),
                    right.to_arbitrary(),
                )
            }
            c => (None, c.to_arbitrary()),
        };

        // We define the theorem using "lambda" form.
        // The definition happens here, in the outside environment, because the
        // theorem is usable by name in this environment.
        let lambda_claim = AcornValue::lambda(arg_types, unbound_claim);
        let theorem_type = lambda_claim.get_type();
        if let Some(name) = &ts.name {
            self.bindings.add_local_constant(
                LocalName::unqualified(name),
                type_params.clone(),
                theorem_type.clone(),
                Some(lambda_claim.clone()),
                None,
            );
        }

        let already_proven = ts.axiomatic || is_citation;
        let source = Source::theorem(
            already_proven,
            self.module_id,
            range,
            true,
            self.depth,
            ts.name.clone(),
        );
        let prop = Proposition::new(external_claim, type_params.clone(), source);

        let node = if already_proven {
            Node::structural(project, self, prop)
        } else {
            let block = Block::new(
                project,
                &self,
                type_params,
                block_args,
                BlockParams::Theorem(ts.name.as_deref(), range, premise, goal),
                statement.first_line(),
                statement.last_line(),
                ts.body.as_ref(),
            )?;
            Node::block(project, self, block, Some(prop))
        };

        let index = self.add_node(node);
        self.add_node_lines(index, &statement.range());
        if let Some(name) = &ts.name {
            let name = LocalName::unqualified(name);
            self.bindings.mark_as_theorem(&name);
        }

        Ok(())
    }

    fn add_variable_satisfy_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        vss: &VariableSatisfyStatement,
    ) -> compilation::Result<()> {
        // We need to prove the general existence claim
        let mut stack = Stack::new();
        let (quant_names, quant_types) =
            self.bindings
                .bind_args(&mut stack, project, &vss.declarations, None)?;
        let general_claim_value = self.bindings.evaluate_value_with_stack(
            &mut stack,
            project,
            &vss.condition,
            Some(&AcornType::Bool),
        )?;
        let general_claim = AcornValue::Exists(quant_types.clone(), Box::new(general_claim_value));
        let source = Source::anonymous(self.module_id, statement.range(), self.depth);
        let general_prop = Proposition::monomorphic(general_claim, source);
        let index = self.add_node(Node::claim(project, self, general_prop));
        self.add_node_lines(index, &statement.range());

        // Define the quantifiers as constants
        for (quant_name, quant_type) in quant_names.iter().zip(quant_types.iter()) {
            let name = LocalName::unqualified(quant_name);
            self.bindings
                .add_local_constant(name, vec![], quant_type.clone(), None, None);
        }

        // We can then assume the specific existence claim with the named constants
        let specific_claim =
            self.bindings
                .evaluate_value(project, &vss.condition, Some(&AcornType::Bool))?;
        let source = Source::anonymous(self.module_id, statement.range(), self.depth);
        let specific_prop = Proposition::monomorphic(specific_claim, source);
        self.add_node(Node::structural(project, self, specific_prop));

        Ok(())
    }

    fn add_function_satisfy_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        fss: &FunctionSatisfyStatement,
    ) -> compilation::Result<()> {
        if fss.name == "new" || fss.name == "self" {
            return Err(fss.name_token.error(&format!(
                "'{}' is a reserved word. use a different name",
                fss.name
            )));
        }
        self.bindings
            .check_unqualified_name_available(statement, &fss.name)?;

        // Figure out the range for this function definition.
        // It's smaller than the whole function statement because it doesn't
        // include the proof block.
        let definition_range = Range {
            start: statement.first_token.start_pos(),
            end: fss.satisfy_token.end_pos(),
        };
        let name = DefinedName::unqualified(&fss.name);
        self.definition_ranges.insert(name, definition_range);

        let (_, mut arg_names, mut arg_types, condition, _) = self.bindings.evaluate_scoped_value(
            project,
            &[],
            &fss.declarations,
            None,
            &fss.condition,
            None,
            None,
        )?;

        let unbound_condition = condition.ok_or_else(|| statement.error("missing condition"))?;
        if unbound_condition.get_type() != AcornType::Bool {
            return Err(fss.condition.error("condition must be a boolean"));
        }

        // The return variable shouldn't become a block arg, because we're trying to
        // prove its existence.
        let _return_name = arg_names.pop().unwrap();
        let return_type = arg_types.pop().unwrap();
        let block_args: Vec<_> = arg_names
            .iter()
            .cloned()
            .zip(arg_types.iter().cloned())
            .collect();
        let num_args = block_args.len() as AtomId;

        let block = Block::new(
            project,
            &self,
            vec![],
            block_args,
            BlockParams::FunctionSatisfy(
                unbound_condition.clone(),
                return_type.clone(),
                fss.condition.range(),
            ),
            statement.first_line(),
            statement.last_line(),
            fss.body.as_ref(),
        )?;

        // We define this function not with an equality, but via the condition.
        let local_name = LocalName::unqualified(&fss.name);
        let function_type = AcornType::functional(arg_types.clone(), return_type);
        self.bindings.add_local_constant(
            local_name.clone(),
            vec![],
            function_type.clone(),
            None,
            None,
        );
        let global_name = GlobalName::new(self.module_id, local_name);
        let function_constant = AcornValue::constant(global_name, vec![], function_type);
        let function_term = AcornValue::apply(
            function_constant.clone(),
            arg_types
                .iter()
                .enumerate()
                .map(|(i, t)| AcornValue::Variable(i as AtomId, t.clone()))
                .collect(),
        );
        let return_bound = unbound_condition.bind_values(num_args, num_args, &[function_term]);
        let external_condition = AcornValue::ForAll(arg_types, Box::new(return_bound));

        let source = Source::constant_definition(
            self.module_id,
            definition_range,
            self.depth,
            function_constant,
            &fss.name,
        );
        let prop = Proposition::monomorphic(external_condition, source);

        let index = self.add_node(Node::block(project, self, block, Some(prop)));
        self.add_node_lines(index, &statement.range());
        Ok(())
    }

    fn add_structure_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ss: &StructureStatement,
    ) -> compilation::Result<()> {
        self.add_line_types(
            LineType::Other,
            statement.first_line(),
            ss.first_right_brace.line_number,
        );
        self.bindings
            .check_typename_available(statement, &ss.name)?;

        let mut arbitrary_params = vec![];
        let type_params = self
            .bindings
            .evaluate_type_params(project, &ss.type_params)?;
        for type_param in &type_params {
            // Internally to the structure definition, the type parameters are
            // treated as arbitrary types.
            arbitrary_params.push(self.bindings.add_arbitrary_type(type_param.clone()));
        }

        // Parse the fields before adding the struct type so that we can't have
        // self-referential structs.
        let mut member_fn_names = vec![];
        let mut field_types = vec![];
        for (field_name_token, field_type_expr) in &ss.fields {
            let field_type = self.bindings.evaluate_type(project, &field_type_expr)?;
            field_types.push(field_type.clone());
            if TokenType::is_magic_method_name(&field_name_token.text()) {
                return Err(field_name_token.error(&format!(
                    "'{}' is a reserved word. use a different name",
                    field_name_token.text()
                )));
            }
            let member_fn_name = LocalName::attribute(&ss.name, field_name_token.text());
            member_fn_names.push(member_fn_name);
        }

        // If there's a constraint, add a block to prove it can be satisfied.
        // The stack for the unbound constraint is the fields of the structure.
        // This happens before adding any names of methods, so that the block
        // can't use them.
        let unbound_constraint = if let Some(constraint) = &ss.constraint {
            let mut stack = Stack::new();
            for ((name_token, _), t) in ss.fields.iter().zip(&field_types) {
                stack.insert(name_token.to_string(), t.clone());
            }
            let unbound = self.bindings.evaluate_value_with_stack(
                &mut stack,
                project,
                &constraint,
                Some(&AcornType::Bool),
            )?;
            let inhabited = AcornValue::Exists(field_types.clone(), Box::new(unbound.clone()));
            let block_params = BlockParams::TypeRequirement(inhabited, constraint.range());
            let block = Block::new(
                project,
                &self,
                vec![], // no type params
                vec![], // no args, because we already handled them
                block_params,
                statement.first_line(),
                statement.last_line(),
                ss.body.as_ref(),
            )?;
            let index = self.add_node(Node::block(project, self, block, None));
            self.add_node_lines(index, &statement.range());
            Some(unbound)
        } else {
            None
        };

        // The member functions take the type itself to a particular member.
        // These may be unresolved values.
        let typeclasses = type_params.iter().map(|tp| tp.typeclass.clone()).collect();
        let potential_type = self.bindings.add_potential_type(&ss.name, typeclasses);
        let struct_type = potential_type.resolve(arbitrary_params, &ss.name_token)?;
        let mut member_fns = vec![];
        for (member_fn_name, field_type) in member_fn_names.into_iter().zip(&field_types) {
            let member_fn_type =
                AcornType::functional(vec![struct_type.clone()], field_type.clone());
            let potential = self.bindings.add_local_constant(
                member_fn_name,
                type_params.clone(),
                member_fn_type.genericize(&type_params),
                None,
                None,
            );
            member_fns.push(potential);
        }

        // A "new" function to create one of these struct types.
        let class = Class {
            module_id: self.module_id,
            name: ss.name.clone(),
        };
        let new_fn_name = LocalName::attribute(&ss.name, "new");
        let new_fn_type = AcornType::functional(field_types.clone(), struct_type.clone());
        let new_fn = self.bindings.add_local_constant(
            new_fn_name,
            type_params.clone(),
            new_fn_type.genericize(&type_params),
            None,
            Some((class, 0, 1)),
        );

        // Each object of this new type has certain properties.
        // member_args are expressions for each of these properties, with x0
        // assigned to a variable of our new type.
        let object_var = AcornValue::Variable(0, struct_type.clone());
        let mut member_args = vec![];
        for (i, member_fn) in member_fns.iter().enumerate() {
            let member_arg = self.bindings.apply_potential(
                &ss.fields[i].0,
                project,
                member_fn.clone(),
                vec![object_var.clone()],
                None,
            )?;
            member_args.push(member_arg);
        }
        let range = Range {
            start: statement.first_token.start_pos(),
            end: ss.name_token.end_pos(),
        };

        // If there is a constraint, it applies to all instances of the type.
        // constraint(Pair.first(p), Pair.second(p))
        // This is the "constraint equation".
        if let Some(unbound_constraint) = &unbound_constraint {
            // As we start, the stack is all the members of p.
            // First, add a stack spot for p.
            let c = unbound_constraint.clone().insert_stack(0, 1);
            // Then, bind the members of p.
            let partially_bound = c.bind_values(1, 1, &member_args);
            // Then, bind a variable for p.
            let constraint_claim =
                AcornValue::ForAll(vec![struct_type.clone()], Box::new(partially_bound))
                    .genericize(&type_params);
            let source = Source::type_definition(
                self.module_id,
                range,
                self.depth,
                ss.name.clone(),
                "constraint".to_string(),
            );
            let prop = Proposition::new(constraint_claim, type_params.clone(), source);
            self.add_node(Node::structural(project, self, prop));
        }

        // An object can be recreated by new'ing from its members. Ie:
        // Pair.new(Pair.first(p), Pair.second(p)) = p.
        // This is the "new equation" for a struct type.
        let recreated = self.bindings.apply_potential(
            &ss.name_token,
            project,
            new_fn.clone(),
            member_args,
            None,
        )?;
        let new_eq =
            AcornValue::Binary(BinaryOp::Equals, Box::new(recreated), Box::new(object_var));
        let new_claim =
            AcornValue::ForAll(vec![struct_type], Box::new(new_eq)).genericize(&type_params);
        let source = Source::type_definition(
            self.module_id,
            range,
            self.depth,
            ss.name.clone(),
            "new".to_string(),
        );
        let prop = Proposition::new(new_claim, type_params.clone(), source);
        self.add_node(Node::structural(project, self, prop));

        // There are also formulas for new followed by member functions. Ie:
        //   Pair.first(Pair.new(a, b)) = a.
        // These are the "member equations".
        //
        // When there's a constraint, we need to add it as a condition here, like:
        //   constraint(a, b) -> Pair.first(Pair.new(a, b)) = a.
        let var_args = (0..ss.fields.len())
            .map(|i| AcornValue::Variable(i as AtomId, field_types[i].clone()))
            .collect::<Vec<_>>();
        let new_application =
            self.bindings
                .apply_potential(&ss.name_token, project, new_fn, var_args, None)?;
        for i in 0..ss.fields.len() {
            let (field_name_token, field_type_expr) = &ss.fields[i];
            let member_fn = &member_fns[i];
            let applied = self.bindings.apply_potential(
                field_name_token,
                project,
                member_fn.clone(),
                vec![new_application.clone()],
                None,
            )?;
            let member_eq = AcornValue::Binary(
                BinaryOp::Equals,
                Box::new(applied),
                Box::new(AcornValue::Variable(i as AtomId, field_types[i].clone())),
            );
            let unbound_member_claim = if let Some(constraint) = &unbound_constraint {
                AcornValue::implies(constraint.clone(), member_eq)
            } else {
                member_eq
            };
            let member_claim =
                AcornValue::ForAll(field_types.clone(), Box::new(unbound_member_claim))
                    .genericize(&type_params);
            let range = Range {
                start: field_name_token.start_pos(),
                end: field_type_expr.last_token().end_pos(),
            };
            let source = Source::type_definition(
                self.module_id,
                range,
                self.depth,
                ss.name.clone(),
                field_name_token.text().to_string(),
            );
            let prop = Proposition::new(member_claim, type_params.clone(), source);
            self.add_node(Node::structural(project, self, prop));
        }

        // Clean up the type parameters
        for type_param in &ss.type_params {
            self.bindings.remove_type(type_param.name.text());
        }
        Ok(())
    }

    fn add_inductive_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        is: &InductiveStatement,
    ) -> compilation::Result<()> {
        self.add_other_lines(statement);
        self.bindings
            .check_typename_available(statement, &is.name)?;
        let range = Range {
            start: statement.first_token.start_pos(),
            end: is.name_token.end_pos(),
        };

        // Add the new type first, because we can have self-reference in the inductive type.
        let mut arbitrary_params = vec![];
        let type_params = self
            .bindings
            .evaluate_type_params(project, &is.type_params)?;
        for type_param in &type_params {
            // Internally to the structure definition, the type parameters are
            // treated as arbitrary types.
            arbitrary_params.push(self.bindings.add_arbitrary_type(type_param.clone()));
        }
        let typeclasses = type_params.iter().map(|tp| tp.typeclass.clone()).collect();
        let potential_type = self.bindings.add_potential_type(&is.name, typeclasses);
        let arb_inductive_type =
            potential_type.resolve(arbitrary_params.clone(), &is.name_token)?;

        // Parse (member name, list of arg types) for each constructor.
        // This uses the arbitrary types.
        let mut constructors = vec![];
        let mut has_base = false;
        for (name_token, type_list_expr) in &is.constructors {
            let type_list = match type_list_expr {
                Some(expr) => {
                    let mut type_list = vec![];
                    self.bindings
                        .evaluate_type_list(project, expr, &mut type_list)?;
                    type_list
                }
                None => vec![],
            };
            if !type_list.contains(&arb_inductive_type) {
                // This provides a base case
                has_base = true;
            }
            let member_name = LocalName::attribute(&is.name, name_token.text());
            constructors.push((member_name, type_list));
        }
        if !has_base {
            return Err(statement.error("inductive type must have a base case"));
        }

        // Define the constructors.
        // constructor_fns contains the functions in their arbitrary forms, as AcornValue.
        let class = Class {
            module_id: self.module_id,
            name: is.name.clone(),
        };
        let mut constructor_fns = vec![];
        let total = constructors.len();
        for (i, (constructor_name, type_list)) in constructors.iter().enumerate() {
            let arb_constructor_type =
                AcornType::functional(type_list.clone(), arb_inductive_type.clone());
            let gen_constructor_type = arb_constructor_type.genericize(&type_params);
            let gen_constructor_fn = self.bindings.add_local_constant(
                constructor_name.clone(),
                type_params.clone(),
                gen_constructor_type,
                None,
                Some((class.clone(), i, total)),
            );
            let arb_constructor_fn =
                gen_constructor_fn.resolve_constant(&arbitrary_params, &is.name_token)?;

            constructor_fns.push(arb_constructor_fn);
        }

        // The "no confusion" property. Different constructors give different results.
        for i in 0..constructors.len() {
            let (member_name, i_arg_types) = &constructors[i];
            let i_fn = constructor_fns[i].clone();
            let i_vars: Vec<_> = i_arg_types
                .iter()
                .enumerate()
                .map(|(k, t)| AcornValue::Variable(k as AtomId, t.clone()))
                .collect();
            let i_app = AcornValue::apply(i_fn, i_vars);
            for j in 0..i {
                let (_, j_arg_types) = &constructors[j];
                let j_fn = constructor_fns[j].clone();
                let j_vars: Vec<_> = j_arg_types
                    .iter()
                    .enumerate()
                    .map(|(k, t)| {
                        AcornValue::Variable((k + i_arg_types.len()) as AtomId, t.clone())
                    })
                    .collect();
                let j_app = AcornValue::apply(j_fn, j_vars);
                let inequality = AcornValue::not_equals(i_app.clone(), j_app);
                let mut quantifiers = i_arg_types.clone();
                quantifiers.extend(j_arg_types.clone());
                let arb_claim = AcornValue::forall(quantifiers, inequality);
                let source = Source::type_definition(
                    self.module_id,
                    range,
                    self.depth,
                    is.name.clone(),
                    member_name.to_string(),
                );
                let gen_claim = arb_claim.genericize(&type_params);
                let prop = Proposition::new(gen_claim, type_params.clone(), source);
                self.add_node(Node::structural(project, self, prop));
            }
        }

        // The "canonical form" principle. Any item of this type must be created by one
        // of the constructors.
        // It seems like this is implied by induction but let's just stick it in.
        // x0 is going to be the "generic item of this type".
        let mut disjuncts = vec![];
        for (i, constructor_fn) in constructor_fns.iter().enumerate() {
            let (_, arg_types) = &constructors[i];
            let args = arg_types
                .iter()
                .enumerate()
                .map(|(k, t)| AcornValue::Variable((k + 1) as AtomId, t.clone()))
                .collect();
            let app = AcornValue::apply(constructor_fn.clone(), args);
            let var = AcornValue::Variable(0, arb_inductive_type.clone());
            let equality = AcornValue::equals(var, app);
            let exists = AcornValue::exists(arg_types.clone(), equality);
            disjuncts.push(exists);
        }
        let disjunction = AcornValue::reduce(BinaryOp::Or, disjuncts);
        let arb_claim = AcornValue::forall(vec![arb_inductive_type.clone()], disjunction);
        // There is no "new" for this type, but it's kind of thematically appropriate.
        let source = Source::type_definition(
            self.module_id,
            range,
            self.depth,
            is.name.clone(),
            "new".to_string(),
        );
        let gen_claim = arb_claim.genericize(&type_params);
        let prop = Proposition::new(gen_claim, type_params.clone(), source);
        self.add_node(Node::structural(project, self, prop));

        // The next principle is that each constructor is injective.
        // Ie if Type.construct(x0, x1) = Type.construct(x2, x3) then x0 = x2 and x1 = x3.
        for (i, constructor_fn) in constructor_fns.iter().enumerate() {
            let (member_name, arg_types) = &constructors[i];
            if arg_types.is_empty() {
                continue;
            }

            // First construct the equality.
            // "Type.construct(x0, x1) = Type.construct(x2, x3)"
            let left_args = arg_types
                .iter()
                .enumerate()
                .map(|(k, t)| AcornValue::Variable(k as AtomId, t.clone()))
                .collect();
            let lhs = AcornValue::apply(constructor_fn.clone(), left_args);
            let right_args = arg_types
                .iter()
                .enumerate()
                .map(|(k, t)| AcornValue::Variable((k + arg_types.len()) as AtomId, t.clone()))
                .collect();
            let rhs = AcornValue::apply(constructor_fn.clone(), right_args);
            let equality = AcornValue::equals(lhs, rhs);

            // Then construct the implication, that the corresponding args are equal.
            let mut conjuncts = vec![];
            for (i, arg_type) in arg_types.iter().enumerate() {
                let left = AcornValue::Variable(i as AtomId, arg_type.clone());
                let right = AcornValue::Variable((i + arg_types.len()) as AtomId, arg_type.clone());
                let arg_equality = AcornValue::equals(left, right);
                conjuncts.push(arg_equality);
            }
            let conjunction = AcornValue::reduce(BinaryOp::And, conjuncts);
            let mut forall_types = arg_types.clone();
            forall_types.extend_from_slice(&arg_types);
            let arb_claim =
                AcornValue::forall(forall_types, AcornValue::implies(equality, conjunction));
            let source = Source::type_definition(
                self.module_id,
                range,
                self.depth,
                is.name.clone(),
                member_name.to_string(),
            );
            let gen_claim = arb_claim.genericize(&type_params);
            let prop = Proposition::new(gen_claim, type_params.clone(), source);
            self.add_node(Node::structural(project, self, prop));
        }

        // Structural induction.
        // The type for the inductive hypothesis.
        let hyp_type = AcornType::functional(vec![arb_inductive_type.clone()], AcornType::Bool);
        // x0 represents the inductive hypothesis.
        // Think of the inductive principle as (conjunction) -> (conclusion).
        // The conjunction is a case for each constructor.
        // The conclusion is that x0 holds for all items of the type.
        let mut conjuncts = vec![];
        for (i, constructor_fn) in constructor_fns.iter().enumerate() {
            let (_, arg_types) = &constructors[i];
            let mut args = vec![];
            let mut conditions = vec![];
            for (j, arg_type) in arg_types.iter().enumerate() {
                // x0 is the inductive hypothesis so we start at 1 for the
                // constructor arguments.
                let id = (j + 1) as AtomId;
                args.push(AcornValue::Variable(id, arg_type.clone()));
                if arg_type == &arb_inductive_type {
                    // The inductive case for this constructor includes a condition
                    // that the inductive hypothesis holds for this argument.
                    conditions.push(AcornValue::apply(
                        AcornValue::Variable(0, hyp_type.clone()),
                        vec![AcornValue::Variable(id, arg_type.clone())],
                    ));
                }
            }

            let new_instance = AcornValue::apply(constructor_fn.clone(), args);
            let instance_claim = AcornValue::apply(
                AcornValue::Variable(0, hyp_type.clone()),
                vec![new_instance],
            );
            let unbound = if conditions.is_empty() {
                // This is a base case. We just need to show that the inductive hypothesis
                // holds for this constructor.
                instance_claim
            } else {
                // This is an inductive case. Given the conditions, we show that
                // the inductive hypothesis holds for this constructor.
                AcornValue::implies(
                    AcornValue::reduce(BinaryOp::And, conditions),
                    instance_claim,
                )
            };
            let conjunction_part = AcornValue::forall(arg_types.clone(), unbound);
            conjuncts.push(conjunction_part);
        }
        let conjunction = AcornValue::reduce(BinaryOp::And, conjuncts);
        let conclusion = AcornValue::forall(
            vec![arb_inductive_type.clone()],
            AcornValue::apply(
                AcornValue::Variable(0, hyp_type.clone()),
                vec![AcornValue::Variable(1, arb_inductive_type.clone())],
            ),
        );
        let unbound_claim = AcornValue::implies(conjunction, conclusion);

        // The lambda form is the functional form, which we bind in the environment.
        let name = LocalName::attribute(&is.name, "induction");
        let arb_lambda_claim = AcornValue::lambda(vec![hyp_type.clone()], unbound_claim.clone());
        let gen_lambda_claim = arb_lambda_claim.genericize(&type_params);
        self.bindings.add_local_constant(
            name.clone(),
            type_params.clone(),
            gen_lambda_claim.get_type(),
            Some(gen_lambda_claim),
            None,
        );
        self.bindings.mark_as_theorem(&name);

        // The forall form is the anonymous truth of induction.
        // We add that as a proposition.
        let arb_forall_claim = AcornValue::forall(vec![hyp_type], unbound_claim);
        let source = Source::theorem(
            true,
            self.module_id,
            range,
            true,
            self.depth,
            Some(name.to_string()),
        );
        let gen_forall_claim = arb_forall_claim.genericize(&type_params);
        let prop = Proposition::new(gen_forall_claim, type_params, source);
        self.add_node(Node::structural(project, self, prop));

        // Clean up the type parameters
        for type_param in &is.type_params {
            self.bindings.remove_type(type_param.name.text());
        }
        Ok(())
    }

    fn add_class_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        cs: &ClassStatement,
    ) -> compilation::Result<()> {
        self.add_other_lines(statement);
        let potential = match self.bindings.get_type_for_typename(&cs.name) {
            Some(potential) => potential.clone(),
            None => {
                return Err(cs
                    .name_token
                    .error(&format!("undefined type name '{}'", cs.name)));
            }
        };
        let type_params = self
            .bindings
            .evaluate_type_params(project, &cs.type_params)?;
        let mut params = vec![];
        for param in &type_params {
            params.push(self.bindings.add_arbitrary_type(param.clone()));
        }
        let instance_type = potential.invertible_resolve(params, &cs.name_token)?;
        self.check_canonical_classname(&cs.name_token, &instance_type)?;

        for substatement in &cs.body.statements {
            match &substatement.statement {
                StatementInfo::Let(ls) => {
                    self.add_let_statement(
                        project,
                        DefinedName::attribute(&cs.name, &ls.name),
                        ls,
                        substatement.range(),
                        Some(&type_params),
                    )?;
                }
                StatementInfo::Define(ds) => {
                    self.add_define_statement(
                        project,
                        DefinedName::attribute(&cs.name, &ds.name),
                        Some(&instance_type),
                        Some(&type_params),
                        ds,
                        substatement.range(),
                    )?;
                }
                _ => {
                    return Err(substatement
                        .error("only let and define statements are allowed in class bodies"));
                }
            }
        }
        for type_param in &cs.type_params {
            self.bindings.remove_type(type_param.name.text());
        }
        Ok(())
    }

    fn add_typeclass_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ts: &TypeclassStatement,
    ) -> compilation::Result<()> {
        self.add_other_lines(statement);
        let instance_name = ts.instance_name.text();
        self.bindings
            .check_typename_available(statement, instance_name)?;
        let typeclass_name = ts.typeclass_name.text();
        self.bindings
            .check_typename_available(statement, typeclass_name)?;
        let typeclass = Typeclass {
            module_id: self.module_id,
            name: typeclass_name.to_string(),
        };
        self.bindings
            .add_typeclass(typeclass_name, typeclass.clone());
        let type_param = TypeParam {
            name: instance_name.to_string(),
            typeclass: Some(typeclass.clone()),
        };
        self.bindings.add_arbitrary_type(type_param.clone());
        let type_params = vec![type_param.clone()];

        for (attr_name, type_expr) in &ts.constants {
            let arb_type = self.bindings.evaluate_type(project, type_expr)?;
            let var_type = arb_type.genericize(&type_params);
            let local_name = LocalName::attribute(typeclass_name, attr_name.text());
            self.bindings
                .check_local_name_available(attr_name, &local_name)?;
            self.bindings.add_local_constant(
                local_name,
                vec![type_param.clone()],
                var_type,
                None,
                None,
            );
        }

        for condition in &ts.conditions {
            // Conditions are similar to theorems, but they don't get proven at the typeclass level.
            // So they don't have blocks.
            // They do get proven, but in the instance statement, not in the typeclass statement.
            let range = Range {
                start: condition.name.start_pos(),
                end: condition.claim.last_token().end_pos(),
            };
            let local_name = LocalName::attribute(&typeclass_name, &condition.name.text());
            self.bindings
                .check_local_name_available(&condition.name, &local_name)?;
            let condition_name = local_name.clone().to_defined();
            self.definition_ranges.insert(condition_name.clone(), range);

            let (bad_params, _, arg_types, unbound_claim, _) =
                self.bindings.evaluate_scoped_value(
                    project,
                    &[],
                    &condition.args,
                    None,
                    &condition.claim,
                    None,
                    None,
                )?;
            if !bad_params.is_empty() {
                return Err(condition.name.error("type parameters are not allowed here"));
            }
            let unbound_claim = unbound_claim
                .ok_or_else(|| condition.claim.error("conditions must have values"))?;
            let external_claim = AcornValue::forall(arg_types.clone(), unbound_claim.clone())
                .genericize(&type_params);
            if let Err(message) = external_claim.validate() {
                return Err(condition.claim.error(&message));
            }
            let lambda_claim = AcornValue::lambda(arg_types.clone(), unbound_claim.clone())
                .genericize(&type_params);
            let theorem_type = lambda_claim.get_type();
            self.bindings.add_local_constant(
                local_name.clone(),
                type_params.clone(),
                theorem_type.clone(),
                Some(lambda_claim),
                None,
            );

            let source = Source::theorem(
                true,
                self.module_id,
                range,
                true,
                self.depth,
                Some(condition_name.to_string()),
            );
            let prop = Proposition::new(external_claim, vec![type_param.clone()], source);
            self.add_node(Node::structural(project, self, prop));
            self.bindings.mark_as_theorem(&local_name);
        }

        self.bindings.remove_type(ts.instance_name.text());
        Ok(())
    }

    fn add_instance_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        is: &InstanceStatement,
    ) -> compilation::Result<()> {
        self.add_line_types(
            LineType::Other,
            statement.first_line(),
            is.definitions.right_brace.line_number,
        );
        let instance_name = is.type_name.text();
        let instance_class = Class {
            module_id: self.module_id,
            name: instance_name.to_string(),
        };
        let instance_type = match self.bindings.get_type_for_typename(&instance_name) {
            Some(PotentialType::Resolved(t)) => t.clone(),
            Some(_) => {
                return Err(is.type_name.error("parametrized types cannot be used here"));
            }
            None => {
                return Err(is
                    .type_name
                    .error(&format!("undefined type name '{}'", instance_name)));
            }
        };
        self.check_canonical_classname(&is.type_name, &instance_type)?;
        let typeclass = self.bindings.evaluate_typeclass(project, &is.typeclass)?;
        // Pairs contains (resolved constant, defined constant) for each attribute.
        let mut pairs = vec![];
        for substatement in &is.definitions.statements {
            match &substatement.statement {
                StatementInfo::Let(ls) => {
                    self.add_let_statement(
                        project,
                        DefinedName::instance(typeclass.clone(), &ls.name, instance_class.clone()),
                        ls,
                        substatement.range(),
                        None,
                    )?;

                    pairs.push(self.bindings.check_instance_attribute(
                        substatement,
                        &project,
                        instance_name,
                        &instance_type,
                        &typeclass,
                        &ls.name,
                    )?);
                }
                StatementInfo::Define(ds) => {
                    if !ds.type_params.is_empty() {
                        return Err(substatement.error("type parameters are not allowed here"));
                    }
                    self.add_define_statement(
                        project,
                        DefinedName::instance(typeclass.clone(), &ds.name, instance_class.clone()),
                        Some(&instance_type),
                        None,
                        ds,
                        substatement.range(),
                    )?;

                    pairs.push(self.bindings.check_instance_attribute(
                        substatement,
                        &project,
                        instance_name,
                        &instance_type,
                        &typeclass,
                        &ds.name,
                    )?);
                }
                _ => {
                    return Err(substatement
                        .error("only let and define statements are allowed in instance bodies"));
                }
            }
        }

        // Check that we have all implementations.
        let attributes =
            self.bindings
                .get_attributes(&project, typeclass.module_id, &typeclass.name);
        let mut conditions = vec![];
        for attr_name in attributes.keys() {
            let tc_attr_name = LocalName::attribute(&typeclass.name, attr_name);
            if self.bindings.is_theorem(&tc_attr_name) {
                // Conditions don't have an implementation.
                // We do gather them for verification.
                let condition = self.bindings.unsafe_instantiate_condition(
                    statement,
                    &typeclass,
                    &attr_name,
                    &instance_type,
                )?;
                conditions.push(condition);
                continue;
            }

            let name = DefinedName::instance(typeclass.clone(), attr_name, instance_class.clone());
            if !self.bindings.constant_name_in_use(&name) {
                return Err(
                    statement.error(&format!("missing implementation for attribute '{}'", name))
                );
            }
        }

        // Create a node for the instance relationship.
        let source = Source {
            module: self.module_id,
            range: statement.range(),
            source_type: SourceType::Instance(
                instance_name.to_string(),
                typeclass.name.to_string(),
            ),
            importable: true,
            depth: self.depth,
        };
        let instance_fact = Fact::Instance(instance_class.clone(), typeclass.clone(), source);

        let node = if conditions.is_empty() {
            Node::Structural(instance_fact)
        } else {
            // We must prove in a block that all the conditions hold for this instance.
            let conditions_claim = AcornValue::reduce(BinaryOp::And, conditions);
            let range = Range {
                start: statement.first_token.start_pos(),
                end: is.definitions.right_brace.end_pos(),
            };
            let block_params = BlockParams::TypeRequirement(conditions_claim, range);
            let block = Block::new(
                project,
                &self,
                vec![], // no type params
                vec![], // no args
                block_params,
                statement.first_line(),
                statement.last_line(),
                is.body.as_ref(),
            )?;
            Node::Block(block, Some(instance_fact))
        };

        let index = self.add_node(node);
        self.add_node_lines(index, &statement.range());
        self.bindings.add_instance_of(instance_class, typeclass);
        Ok(())
    }

    /// Adds a statement to the environment.
    /// If the statement has a body, this call creates a sub-environment and adds the body
    /// to that sub-environment.
    pub fn add_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
    ) -> compilation::Result<()> {
        if self.includes_explicit_false {
            return Err(
                statement.error("an explicit 'false' may not be followed by other statements")
            );
        }
        match &statement.statement {
            StatementInfo::Type(ts) => {
                self.add_other_lines(statement);
                self.bindings
                    .check_typename_available(statement, &ts.name)?;
                if ts.type_expr.is_axiom() {
                    self.bindings.add_potential_type(&ts.name, vec![]);
                } else {
                    let potential = self
                        .bindings
                        .evaluate_potential_type(project, &ts.type_expr)?;
                    self.bindings.add_type_alias(&ts.name, potential);
                };
                Ok(())
            }

            StatementInfo::Let(ls) => {
                self.add_other_lines(statement);
                self.add_let_statement(
                    project,
                    DefinedName::unqualified(&ls.name),
                    ls,
                    statement.range(),
                    None,
                )
            }

            StatementInfo::Define(ds) => {
                self.add_other_lines(statement);
                self.add_define_statement(
                    project,
                    DefinedName::unqualified(&ds.name),
                    None,
                    None,
                    ds,
                    statement.range(),
                )
            }

            StatementInfo::Theorem(ts) => self.add_theorem_statement(project, statement, ts),

            StatementInfo::Claim(cs) => {
                let claim =
                    self.bindings
                        .evaluate_value(project, &cs.claim, Some(&AcornType::Bool))?;
                if claim == AcornValue::Bool(false) {
                    self.includes_explicit_false = true;
                }

                if self.bindings.is_citation(project, &claim) {
                    // We already know this is true, so we don't need to prove it
                    let source = Source::anonymous(self.module_id, statement.range(), self.depth);
                    let prop = Proposition::monomorphic(claim, source);
                    self.add_node(Node::structural(project, self, prop));
                    self.add_other_lines(statement);
                } else {
                    let source = Source::anonymous(self.module_id, statement.range(), self.depth);
                    let prop = Proposition::monomorphic(claim, source);
                    let index = self.add_node(Node::claim(project, self, prop));
                    self.add_node_lines(index, &statement.range());
                }
                Ok(())
            }

            StatementInfo::ForAll(fas) => {
                if fas.body.statements.is_empty() {
                    // ForAll statements with an empty body can just be ignored
                    return Ok(());
                }
                let mut args = vec![];
                for quantifier in &fas.quantifiers {
                    let (arg_name, arg_type) =
                        self.bindings.evaluate_declaration(project, quantifier)?;
                    args.push((arg_name, arg_type));
                }

                let block = Block::new(
                    project,
                    &self,
                    vec![],
                    args,
                    BlockParams::ForAll,
                    statement.first_line(),
                    statement.last_line(),
                    Some(&fas.body),
                )?;

                let (outer_claim, range) =
                    block.externalize_last_claim(self, &fas.body.right_brace)?;
                let source = Source::anonymous(self.module_id, range, self.depth);
                let prop = Proposition::monomorphic(outer_claim, source);
                let index = self.add_node(Node::block(project, self, block, Some(prop)));
                self.add_node_lines(index, &statement.range());
                Ok(())
            }

            StatementInfo::If(is) => {
                let condition =
                    self.bindings
                        .evaluate_value(project, &is.condition, Some(&AcornType::Bool))?;
                let range = is.condition.range();
                let if_claim = self.add_conditional(
                    project,
                    condition.clone(),
                    range,
                    statement.first_line(),
                    statement.last_line(),
                    &is.body,
                    None,
                )?;
                if let Some(else_body) = &is.else_body {
                    self.add_conditional(
                        project,
                        condition.negate(),
                        range,
                        else_body.left_brace.line_number as u32,
                        else_body.right_brace.line_number as u32,
                        else_body,
                        if_claim,
                    )?;
                }
                Ok(())
            }

            StatementInfo::VariableSatisfy(vss) => {
                self.add_variable_satisfy_statement(project, statement, vss)
            }

            StatementInfo::FunctionSatisfy(fss) => {
                self.add_function_satisfy_statement(project, statement, fss)
            }

            StatementInfo::Structure(ss) => self.add_structure_statement(project, statement, ss),

            StatementInfo::Inductive(is) => self.add_inductive_statement(project, statement, is),

            StatementInfo::Import(is) => {
                self.add_other_lines(statement);

                // Give a local name to the imported module
                let local_name = is.components.last().unwrap();
                self.bindings
                    .check_unqualified_name_available(statement, local_name)?;
                let full_name = is.components.join(".");
                let module_id = match project.load_module_by_name(&full_name) {
                    Ok(module_id) => module_id,
                    Err(LoadError(s)) => {
                        // The error is with the import statement itself, like a circular import.
                        return Err(statement.error(&format!("import error: {}", s)));
                    }
                };
                if project.get_bindings(module_id).is_none() {
                    // The fundamental error is in the other module, not this one.
                    return Err(Error::secondary(
                        &statement.first_token,
                        &statement.last_token,
                        &format!("error in '{}' module", full_name),
                    ));
                }
                self.bindings.import_module(local_name, module_id);

                // Bring the imported names into this environment
                for name in &is.names {
                    self.bindings.import_name(project, module_id, name)?;
                }

                Ok(())
            }

            StatementInfo::Class(cs) => self.add_class_statement(project, statement, cs),

            StatementInfo::Numerals(ds) => {
                self.add_other_lines(statement);
                let acorn_type = self.bindings.evaluate_type(project, &ds.type_expr)?;
                if let AcornType::Data(class, params) = acorn_type {
                    if !params.is_empty() {
                        return Err(ds
                            .type_expr
                            .error("numerals type cannot have type parameters"));
                    }
                    self.bindings.set_numerals(class);
                    Ok(())
                } else {
                    Err(ds.type_expr.error("numerals type must be a data type"))
                }
            }

            StatementInfo::Solve(ss) => {
                let target = self.bindings.evaluate_value(project, &ss.target, None)?;
                let solve_range = Range {
                    start: statement.first_token.start_pos(),
                    end: ss.target.last_token().end_pos(),
                };

                let mut block = Block::new(
                    project,
                    &self,
                    vec![],
                    vec![],
                    BlockParams::Solve(target.clone(), solve_range),
                    statement.first_line(),
                    statement.last_line(),
                    Some(&ss.body),
                )?;

                let prop = match block.solves(self, &target) {
                    Some((outer_claim, claim_range)) => {
                        block.goal = None;
                        let source = Source::anonymous(self.module_id, claim_range, self.depth);
                        Some(Proposition::monomorphic(outer_claim, source))
                    }
                    None => None,
                };

                let index = self.add_node(Node::block(project, self, block, prop));
                self.add_node_lines(index, &statement.range());
                Ok(())
            }

            StatementInfo::Problem(body) => {
                let block = Block::new(
                    project,
                    &self,
                    vec![],
                    vec![],
                    BlockParams::Problem,
                    statement.first_line(),
                    statement.last_line(),
                    Some(body),
                )?;

                let index = self.add_node(Node::block(project, self, block, None));
                self.add_node_lines(index, &statement.range());
                Ok(())
            }

            StatementInfo::Match(ms) => {
                let scrutinee = self.bindings.evaluate_value(project, &ms.scrutinee, None)?;
                let scrutinee_type = scrutinee.get_type();
                let mut indices = vec![];
                let mut disjuncts = vec![];
                for (pattern, body) in &ms.cases {
                    let (constructor, args, i, total) =
                        self.bindings
                            .evaluate_pattern(project, &scrutinee_type, pattern)?;
                    if indices.contains(&i) {
                        return Err(pattern.error("duplicate pattern in match statement"));
                    }
                    indices.push(i);

                    let params = BlockParams::MatchCase(
                        scrutinee.clone(),
                        constructor,
                        args,
                        pattern.range(),
                    );

                    let block = Block::new(
                        project,
                        &self,
                        vec![],
                        vec![],
                        params,
                        body.left_brace.line_number,
                        body.right_brace.line_number,
                        Some(body),
                    )?;

                    let (disjunct, _) = block.externalize_last_claim(self, &body.right_brace)?;
                    disjuncts.push(disjunct);

                    if total == indices.len() {
                        if ms.cases.len() > total {
                            // The next iteration will report an error
                            continue;
                        }

                        let disjunction = AcornValue::reduce(BinaryOp::Or, disjuncts);
                        let source =
                            Source::anonymous(self.module_id, statement.range(), self.depth);
                        let prop = Proposition::monomorphic(disjunction, source);
                        let index = self.add_node(Node::block(project, self, block, Some(prop)));
                        self.add_node_lines(index, &body.range());
                        return Ok(());
                    }

                    // No proposition here. We only put an externalized proposition on the last block.
                    let index = self.add_node(Node::block(project, self, block, None));
                    self.add_node_lines(index, &body.range());
                }
                Err(ms
                    .scrutinee
                    .error("not all cases are covered in match statement"))
            }

            StatementInfo::Typeclass(ts) => self.add_typeclass_statement(project, statement, ts),

            StatementInfo::Instance(is) => self.add_instance_statement(project, statement, is),
        }
    }

    /// Parse these tokens and add them to the environment.
    /// If project is not provided, we won't be able to handle import statements.
    pub fn add_tokens(
        &mut self,
        project: &mut Project,
        tokens: Vec<Token>,
    ) -> compilation::Result<()> {
        let mut tokens = TokenIter::new(tokens);
        loop {
            match Statement::parse(&mut tokens, false) {
                Ok((Some(statement), _)) => {
                    if let Err(e) = self.add_statement(project, &statement) {
                        return Err(e);
                    }
                }
                Ok((None, _)) => return Ok(()),
                Err(e) => return Err(e),
            }
        }
    }

    /// Get all facts that can be imported into other modules from this one.
    /// If the filter is provided, we only return facts whose qualified name is in the filter.
    pub fn importable_facts(&self, filter: Option<&HashSet<String>>) -> Vec<Fact> {
        assert_eq!(self.depth, 0);
        let mut facts = vec![];
        for node in &self.nodes {
            if !node.importable() {
                continue;
            }
            if let Some(filter) = filter {
                let name = node.source_name().expect("importable fact has no name");
                if !filter.contains(&name) {
                    continue;
                }
            }
            if let Some(fact) = node.get_fact() {
                facts.push(fact);
            }
        }
        facts
    }

    /// Returns a NodeCursor for all nodes that correspond to a goal within this environment,
    /// or subenvironments, recursively.
    /// The order is "proving order", ie the goals inside the block are listed before the
    /// root goal of a block.
    pub fn iter_goals(&self) -> impl Iterator<Item = NodeCursor> {
        let mut answer = vec![];
        for i in 0..self.nodes.len() {
            let mut cursor = NodeCursor::new(self, i);
            cursor.find_goals(&mut answer);
        }
        answer.into_iter()
    }

    /// Used for integration testing.
    /// Not good for general use because it's based on the human-readable description.
    pub fn get_node_by_description(&self, description: &str) -> NodeCursor {
        let mut descriptions = Vec::new();
        for node in self.iter_goals() {
            let context = node.goal_context().unwrap();
            if context.description == description {
                return node;
            }
            descriptions.push(context.description);
        }

        panic!(
            "no context found for {} in:\n{}\n",
            description,
            descriptions.join("\n")
        );
    }

    /// Returns the path to a given zero-based line.
    /// This is a UI heuristic.
    /// Either returns a path to a proposition, or an error message explaining why this
    /// line is unusable.
    /// Error messages use one-based line numbers.
    pub fn path_for_line(&self, line: u32) -> Result<Vec<usize>, String> {
        let mut path = vec![];
        let mut block: Option<&Block> = None;
        let mut env = self;
        loop {
            match env.get_line_type(line) {
                Some(LineType::Node(i)) => {
                    path.push(i);
                    let node = &env.nodes[i];
                    if node.is_axiom() {
                        return Err(format!("line {} is an axiom", line + 1));
                    }
                    match node.get_block() {
                        Some(b) => {
                            block = Some(b);
                            env = &b.env;
                            continue;
                        }
                        None => {
                            return Ok(path);
                        }
                    }
                }
                Some(LineType::Opening) | Some(LineType::Closing) => match block {
                    Some(block) => {
                        if block.goal.is_none() {
                            return Err(format!("no claim for block at line {}", line + 1));
                        }
                        return Ok(path);
                    }
                    None => return Err(format!("brace but no block, line {}", line + 1)),
                },
                Some(LineType::Other) => return Err(format!("line {} is not a prop", line + 1)),
                None => return Err(format!("line {} is out of range", line + 1)),
                Some(LineType::Empty) => {
                    // We let the user insert a proof in an area by clicking on an empty
                    // line where the proof would go.
                    // To find the statement we're proving, we "slide" into the next prop.
                    let mut slide = line;
                    loop {
                        slide += 1;
                        match env.get_line_type(slide) {
                            Some(LineType::Node(i)) => {
                                let node = &env.nodes[i];
                                if node.is_axiom() {
                                    return Err(format!("slide to axiom, line {}", slide + 1));
                                }
                                if node.get_block().is_none() {
                                    path.push(i);
                                    return Ok(path);
                                }
                                // We can't slide into a block, because the proof would be
                                // inserted into the block, rather than here.
                                return Err(format!("blocked slide {} -> {}", line + 1, slide + 1));
                            }
                            Some(LineType::Empty) => {
                                // Keep sliding
                                continue;
                            }
                            Some(LineType::Closing) => {
                                // Sliding into the end of our block is okay
                                match block {
                                    Some(block) => {
                                        if block.goal.is_none() {
                                            return Err("slide to end but no claim".to_string());
                                        }
                                        return Ok(path);
                                    }
                                    None => {
                                        return Err(format!(
                                            "close brace but no block, line {}",
                                            slide + 1
                                        ))
                                    }
                                }
                            }
                            Some(LineType::Opening) => {
                                return Err(format!("slide to open brace, line {}", slide + 1));
                            }
                            Some(LineType::Other) => {
                                return Err(format!("slide to non-prop {}", slide + 1));
                            }
                            None => return Err(format!("slide to end, line {}", slide + 1)),
                        }
                    }
                }
            }
        }
    }

    pub fn covers_line(&self, line: u32) -> bool {
        if line < self.first_line {
            return false;
        }
        if line >= self.next_line() {
            return false;
        }
        true
    }

    /// Finds the narrowest environment that covers the given line.
    pub fn env_for_line(&self, line: u32) -> &Environment {
        loop {
            match self.get_line_type(line) {
                Some(LineType::Node(i)) => {
                    if let Some(block) = self.nodes[i].get_block() {
                        return block.env.env_for_line(line);
                    }
                    return self;
                }
                Some(LineType::Opening)
                | Some(LineType::Closing)
                | Some(LineType::Other)
                | Some(LineType::Empty)
                | None => return self,
            }
        }
    }
}

/// Methods used for integration testing.
impl Environment {
    /// Create a test version of the environment.
    pub fn test() -> Self {
        use crate::module::FIRST_NORMAL;
        Environment::new(FIRST_NORMAL)
    }

    /// Adds a possibly multi-line statement to the environment.
    /// Panics on failure.
    pub fn add(&mut self, input: &str) {
        let tokens = Token::scan(input);
        if let Err(e) = self.add_tokens(&mut Project::new_mock(), tokens) {
            panic!("error in add_tokens: {}", e);
        }
    }

    /// Makes sure the lines are self-consistent
    pub fn check_lines(&self) {
        // Check that each proposition's block covers the lines it claims to cover
        for (line, line_type) in self.line_types.iter().enumerate() {
            if let LineType::Node(prop_index) = line_type {
                let node = &self.nodes[*prop_index];
                if let Some(block) = node.get_block() {
                    assert!(block.env.covers_line(line as u32));
                }
            }
        }

        // Recurse
        for node in &self.nodes {
            if let Some(block) = node.get_block() {
                block.env.check_lines();
            }
        }
    }

    /// Expects the given line to be bad
    pub fn bad(&mut self, input: &str) {
        if let Ok(statement) = Statement::parse_str(input) {
            assert!(
                self.add_statement(&mut Project::new_mock(), &statement)
                    .is_err(),
                "expected error in: {}",
                input
            );
        }
    }

    /// Check that the given name actually does have this type in the environment.
    pub fn expect_type(&mut self, name: &str, type_string: &str) {
        self.bindings.expect_type(name, type_string)
    }

    /// Check that the given name is defined to be this value
    pub fn expect_def(&mut self, name: &str, value_string: &str) {
        let name = DefinedName::guess(name);
        let env_value = match self.bindings.get_definition(&name) {
            Some(t) => t,
            None => panic!("{} not found in environment", name),
        };
        assert_eq!(env_value.to_string(), value_string);
    }

    /// Assert that these two names are defined to equal the same thing
    pub fn assert_def_eq(&self, name1: &str, name2: &str) {
        let name1 = DefinedName::guess(name1);
        let def1 = self.bindings.get_definition(&name1).unwrap();
        let name2 = DefinedName::guess(name2);
        let def2 = self.bindings.get_definition(&name2).unwrap();
        assert_eq!(def1, def2);
    }

    /// Assert that these two names are defined to be different things
    pub fn assert_def_ne(&self, name1: &str, name2: &str) {
        let name1 = DefinedName::guess(name1);
        let def1 = self.bindings.get_definition(&name1).unwrap();
        let name2 = DefinedName::guess(name2);
        let def2 = self.bindings.get_definition(&name2).unwrap();
        assert_ne!(def1, def2);
    }

    /// Get the bindings for the theorem block with the given name.
    pub fn get_bindings(&self, theorem_name: &str) -> &BindingMap {
        let mut cursor = self.get_node_by_description(theorem_name);
        cursor.descend(0);
        &cursor.env().bindings
    }
}

use crate::acorn_type::{AcornType, Class, PotentialType, TypeParam, Typeclass};
use crate::acorn_value::{AcornValue, BinaryOp};
use crate::binding_map::BindingMap;
use crate::code_gen_error::CodeGenError;
use crate::compilation::{self, ErrorSource, PanicOnError};
use crate::expression::{Declaration, Expression, Terminator, TypeParamExpr};
use crate::module::{Module, ModuleId};
use crate::named_entity::NamedEntity;
use crate::names::{DefinedName, GlobalName, LocalName};
use crate::potential_value::PotentialValue;
use crate::project::Project;
use crate::stack::Stack;
use crate::token::{Token, TokenIter, TokenType};

/// The Evaluator turns expressions into types and values, and other things of that nature.
pub struct Evaluator<'a> {
    bindings: &'a BindingMap,
    project: &'a Project,
}

impl<'a> Evaluator<'a> {
    /// Creates a new evaluator.
    pub fn new(bindings: &'a BindingMap, project: &'a Project) -> Self {
        Self { project, bindings }
    }

    // Gets the bindings from the project, except uses the one we already have if it's correct.
    // This is useful while we're still analyzing the module, because in that case, the project
    // won't have access to it yet.
    fn get_bindings(&self, module_id: ModuleId) -> &'a BindingMap {
        if module_id == self.bindings.module_id {
            self.bindings
        } else {
            self.project.get_bindings(module_id).unwrap()
        }
    }

    /// Evaluates an expression that represents a type.
    pub fn evaluate_type(&self, expression: &Expression) -> compilation::Result<AcornType> {
        let potential = self.evaluate_potential_type(expression)?;
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
        expression: &Expression,
    ) -> compilation::Result<PotentialType> {
        match expression {
            Expression::Singleton(token) => {
                if token.token_type == TokenType::Axiom {
                    return Err(token.error("axiomatic types can only be created at the top level"));
                }
                if let Some(t) = self.bindings.typename_to_type.get(token.text()) {
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
                        arg_types.push(self.evaluate_type(arg_expr)?);
                    }
                    let return_type = self.evaluate_type(right)?;
                    Ok(PotentialType::Resolved(AcornType::functional(
                        arg_types,
                        return_type,
                    )))
                }
                TokenType::Dot => {
                    let entity = self.evaluate_entity(&mut Stack::new(), expression)?;
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
                    instance_params.push(self.evaluate_type(param_expr)?);
                }
                let p = self.evaluate_potential_type(left)?;
                let t = p.resolve(instance_params, expression)?;
                Ok(PotentialType::Resolved(t))
            }
            Expression::Grouping(_, e, _) => self.evaluate_potential_type(e),
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
        expression: &Expression,
        output: &mut Vec<AcornType>,
    ) -> compilation::Result<()> {
        match expression {
            Expression::Grouping(_, e, _) => self.evaluate_type_list(e, output),
            Expression::Binary(left, token, right) if token.token_type == TokenType::Comma => {
                self.evaluate_type_list(left, output)?;
                self.evaluate_type_list(right, output)
            }
            e => {
                output.push(self.evaluate_type(e)?);
                Ok(())
            }
        }
    }

    /// Evaluates a variable declaration in this context.
    /// "self" declarations should be handled externally.
    pub fn evaluate_declaration(
        &self,
        declaration: &Declaration,
    ) -> compilation::Result<(String, AcornType)> {
        match declaration {
            Declaration::Typed(name_token, type_expr) => {
                let acorn_type = self.evaluate_type(&type_expr)?;
                return Ok((name_token.to_string(), acorn_type));
            }
            Declaration::SelfToken(name_token) => {
                return Err(name_token.error("cannot use 'self' as an argument here"));
            }
        };
    }

    /// Parses a list of named argument declarations and adds them to the stack.
    /// class_type should be provided if these are the arguments of a new member function.
    pub fn bind_args<'b, I>(
        &self,
        stack: &mut Stack,
        declarations: I,
        class_type: Option<&AcornType>,
    ) -> compilation::Result<(Vec<String>, Vec<AcornType>)>
    where
        I: IntoIterator<Item = &'b Declaration>,
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
            let (name, acorn_type) = self.evaluate_declaration(declaration)?;
            self.bindings
                .check_unqualified_name_available(&name, declaration.token())?;
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
        expected_type: &AcornType,
        value: &AcornValue,
        source: &dyn ErrorSource,
    ) -> compilation::Result<(usize, usize)> {
        let info = match value {
            AcornValue::Constant(ci) => {
                let bindings = self.get_bindings(ci.name.module_id);
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
        expected_type: &AcornType,
        pattern: &Expression,
    ) -> compilation::Result<(AcornValue, Vec<(String, AcornType)>, usize, usize)> {
        let (fn_exp, args) = match pattern {
            Expression::Concatenation(function, args) if !args.is_type() => (function, args),
            _ => {
                // This can only be a no-argument constructor.
                let constructor = self.evaluate_value(pattern, Some(expected_type))?;
                let (i, total) = self.expect_constructor(expected_type, &constructor, pattern)?;
                return Ok((constructor, vec![], i, total));
            }
        };
        let potential_constructor =
            self.evaluate_potential_value(&mut Stack::new(), fn_exp, None)?;
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
        let (i, total) = self.expect_constructor(expected_type, &constructor, pattern)?;
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
            self.bindings
                .check_unqualified_name_available(&name, name_exp)?;
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
        class: &Class,
        s: &str,
    ) -> compilation::Result<AcornValue> {
        if self.bindings.has_type_attribute(&class, s) {
            return self
                .evaluate_type_attribute(&class, s, token)?
                .as_value(token);
        }

        if s.len() == 1 {
            return Err(token.error(&format!("digit {}.{} is not defined", &class.name, s)));
        }

        let last_str = &s[s.len() - 1..];
        let last_num = self.evaluate_number_with_class(token, class, last_str)?;
        let initial_str = &s[..s.len() - 1];
        let initial_num = self.evaluate_number_with_class(token, class, initial_str)?;
        let read_fn = match self.evaluate_type_attribute(&class, "read", token)? {
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

    /// Evaluates a name scoped by a type name, like Nat.range
    fn evaluate_type_attribute(
        &self,
        class: &Class,
        attr_name: &str,
        source: &dyn ErrorSource,
    ) -> compilation::Result<PotentialValue> {
        let module_id = self
            .bindings
            .class_info
            .get(class)
            .and_then(|info| info.attributes.get(attr_name))
            .ok_or_else(|| source.error("attribute not found"))?;
        let bindings = self.get_bindings(*module_id);
        let constant_name = DefinedName::attribute(&class.name, attr_name);
        bindings.get_constant_value(&constant_name, source)
    }

    /// Evalutes a name scoped by a typeclass name, like Group.foo
    fn evaluate_typeclass_attribute(
        &self,
        typeclass: &Typeclass,
        attr_name: &str,
        source: &dyn ErrorSource,
    ) -> compilation::Result<PotentialValue> {
        let bindings = self.get_bindings(typeclass.module_id);

        // Check if this attribute is an inherited one.
        // Note that if we are in the definition of typeclass conditions, there is no info yet.
        if let Some(info) = self.bindings.typeclass_info.get(&typeclass) {
            if let Some(base_tc) = info.attributes.get(attr_name) {
                if base_tc != typeclass {
                    return self.evaluate_typeclass_attribute(&base_tc, attr_name, source);
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
    ) -> compilation::Result<AcornValue> {
        self.evaluate_value_with_stack(&mut Stack::new(), expression, expected_type)
    }

    /// Evaluates an attribute of a value, like foo.bar.
    /// token is used for reporting errors but may not correspond to anything in particular.
    fn evaluate_value_attribute(
        &self,
        receiver: AcornValue,
        attr_name: &str,
        source: &dyn ErrorSource,
    ) -> compilation::Result<AcornValue> {
        let base_type = receiver.get_type();

        let function = match &base_type {
            AcornType::Data(class, _) => self.evaluate_type_attribute(class, attr_name, source)?,
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
                self.evaluate_typeclass_attribute(typeclass, attr_name, source)?
            }
            _ => {
                return Err(source.error(&format!(
                    "objects of type {:?} have no attributes",
                    base_type
                )));
            }
        };
        self.bindings
            .apply_potential(function, vec![receiver], None, source)
    }

    /// Evaluates a single name, which may be namespaced to another named entity.
    /// In this situation, we don't know what sort of thing we expect the name to represent.
    /// We have the entity described by a chain of names, and we're adding one more name to the chain.
    fn evaluate_name(
        &self,
        name_token: &Token,
        stack: &Stack,
        namespace: Option<NamedEntity>,
    ) -> compilation::Result<NamedEntity> {
        let name = name_token.text();
        match namespace {
            Some(NamedEntity::Value(instance)) => {
                let value = self.evaluate_value_attribute(instance, name, name_token)?;
                Ok(NamedEntity::Value(value))
            }
            Some(NamedEntity::Type(t)) => {
                match &t {
                    AcornType::Data(class, params) => {
                        if name_token.token_type == TokenType::Numeral {
                            let value = self.evaluate_number_with_class(
                                name_token,
                                &class,
                                name_token.text(),
                            )?;
                            return Ok(NamedEntity::Value(value));
                        }
                        match self.evaluate_type_attribute(class, name, name_token)? {
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
                        match self.evaluate_typeclass_attribute(&typeclass, name, name_token)? {
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
                if let Some(bindings) = self.project.get_bindings(module) {
                    Evaluator::new(bindings, self.project).evaluate_name(name_token, stack, None)
                } else {
                    Err(name_token.error("could not load bindings for module"))
                }
            }
            Some(NamedEntity::Typeclass(tc)) => {
                match self.evaluate_typeclass_attribute(&tc, name, name_token)? {
                    PotentialValue::Resolved(value) => Ok(NamedEntity::Value(value)),
                    PotentialValue::Unresolved(u) => Ok(NamedEntity::UnresolvedValue(u)),
                }
            }
            Some(NamedEntity::UnresolvedValue(_)) => {
                Err(name_token.error("cannot access members of unresolved types"))
            }
            Some(NamedEntity::UnresolvedType(ut)) => {
                match self.evaluate_type_attribute(&ut.class, name, name_token)? {
                    PotentialValue::Resolved(value) => Ok(NamedEntity::Value(value)),
                    PotentialValue::Unresolved(u) => Ok(NamedEntity::UnresolvedValue(u)),
                }
            }
            None => {
                match name_token.token_type {
                    TokenType::Identifier => {
                        if self.bindings.is_module(name) {
                            match self.bindings.name_to_module.get(name) {
                                Some(module) => Ok(NamedEntity::Module(*module)),
                                None => Err(name_token.error("unknown module")),
                            }
                        } else if self.bindings.has_typename(name) {
                            match self.bindings.get_type_for_typename(name) {
                                Some(PotentialType::Resolved(t)) => {
                                    Ok(NamedEntity::Type(t.clone()))
                                }
                                Some(PotentialType::Unresolved(ut)) => {
                                    Ok(NamedEntity::UnresolvedType(ut.clone()))
                                }
                                _ => Err(name_token.error("unknown type")),
                            }
                        } else if self.bindings.has_typeclass_name(name) {
                            let tc = self.bindings.get_typeclass_for_name(name).unwrap();
                            Ok(NamedEntity::Typeclass(tc.clone()))
                        } else if let Some((i, t)) = stack.get(name) {
                            // This is a stack variable
                            Ok(NamedEntity::Value(AcornValue::Variable(*i, t.clone())))
                        } else {
                            let constant_name = DefinedName::unqualified(name);
                            Ok(NamedEntity::new(
                                self.bindings
                                    .get_constant_value(&constant_name, name_token)?,
                            ))
                        }
                    }
                    TokenType::Numeral => {
                        let class = match &self.bindings.numerals {
                            Some(c) => c,
                            None => {
                                return Err(name_token
                                    .error("you must set a default type for numeric literals"));
                            }
                        };
                        let value =
                            self.evaluate_number_with_class(name_token, class, name_token.text())?;
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
        left: &Expression,
        right: &Expression,
    ) -> compilation::Result<NamedEntity> {
        let right_token = match right {
            Expression::Singleton(token) => token,
            _ => return Err(right.error("expected an identifier after a dot")),
        };
        let left_entity = self.evaluate_entity(stack, left)?;
        self.evaluate_name(right_token, stack, Some(left_entity))
    }

    /// Evaluate a string of names separated by dots.
    /// Creates fake tokens to be used for error reporting.
    /// Chain must not be empty.
    pub fn evaluate_name_chain(&self, chain: &[&str]) -> Option<NamedEntity> {
        let mut answer: Option<NamedEntity> = None;
        for name in chain {
            let token = TokenType::Identifier.new_token(name);
            answer = Some(self.evaluate_name(&token, &Stack::new(), answer).ok()?);
        }
        answer
    }

    /// Evaluates an expression that could represent any sort of named entity.
    /// It could be a type, a value, or a module.
    fn evaluate_entity(
        &self,
        stack: &mut Stack,
        expression: &Expression,
    ) -> compilation::Result<NamedEntity> {
        // Handle a plain old name
        if let Expression::Singleton(token) = expression {
            return self.evaluate_name(token, stack, None);
        }

        // Dot expressions could be any sort of named entity
        if let Expression::Binary(left, token, right) = expression {
            if token.token_type == TokenType::Dot {
                return self.evaluate_dot_expression(stack, left, right);
            }
        }

        if expression.is_type() {
            let acorn_type = self.evaluate_type(expression)?;
            return Ok(NamedEntity::Type(acorn_type));
        }

        // If it isn't a name or a type, it must be a value.
        let value = self.evaluate_value_with_stack(stack, expression, None)?;
        Ok(NamedEntity::Value(value))
    }

    /// Evaluates an infix operator.
    /// name is the special alphanumeric name that corresponds to the operator, like "+" expands to "add".
    fn evaluate_infix(
        &self,
        stack: &mut Stack,
        expression: &Expression,
        left: &Expression,
        token: &Token,
        right: &Expression,
        name: &str,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<AcornValue> {
        let left_value = self.evaluate_value_with_stack(stack, left, None)?;
        let right_value = self.evaluate_value_with_stack(stack, right, None)?;

        // Get the partial application to the left
        let partial = self.evaluate_value_attribute(left_value, name, expression)?;
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

    /// Evaluates an expression that describes a value, with a stack given as context.
    /// This must resolve to a completed value, with all types inferred.
    pub fn evaluate_value_with_stack(
        &self,
        stack: &mut Stack,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<AcornValue> {
        let potential = self.evaluate_potential_value(stack, expression, expected_type)?;
        potential.as_value(expression)
    }

    /// Evaluates an expression that could describe a value, but could also describe
    /// a constant with an unresolved type.
    fn evaluate_potential_value(
        &self,
        stack: &mut Stack,
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
                    AcornType::Bool.check_eq(expected_type, token)?;
                    AcornValue::Bool(token.token_type == TokenType::True)
                }
                TokenType::Identifier | TokenType::Numeral | TokenType::SelfToken => {
                    let entity = self.evaluate_name(token, stack, None)?;
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
                            return self.bindings.maybe_resolve_value(
                                potential,
                                expected_type,
                                token,
                            );
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
                    let value =
                        self.evaluate_value_with_stack(stack, expr, Some(&AcornType::Bool))?;
                    AcornValue::Not(Box::new(value))
                }
                token_type => match token_type.to_prefix_magic_method_name() {
                    Some(name) => {
                        let subvalue = self.evaluate_value_with_stack(stack, expr, None)?;
                        let value = self.evaluate_value_attribute(subvalue, name, token)?;
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
                    let left_value =
                        self.evaluate_value_with_stack(stack, left, Some(&AcornType::Bool))?;
                    let right_value =
                        self.evaluate_value_with_stack(stack, right, Some(&AcornType::Bool))?;

                    AcornValue::Binary(
                        BinaryOp::Implies,
                        Box::new(left_value),
                        Box::new(right_value),
                    )
                }
                TokenType::Equals => {
                    AcornType::Bool.check_eq(expected_type, token)?;
                    let left_value = self.evaluate_value_with_stack(stack, left, None)?;
                    let right_value =
                        self.evaluate_value_with_stack(stack, right, Some(&left_value.get_type()))?;
                    AcornValue::Binary(
                        BinaryOp::Equals,
                        Box::new(left_value),
                        Box::new(right_value),
                    )
                }
                TokenType::NotEquals => {
                    AcornType::Bool.check_eq(expected_type, token)?;
                    let left_value = self.evaluate_value_with_stack(stack, left, None)?;
                    let right_value =
                        self.evaluate_value_with_stack(stack, right, Some(&left_value.get_type()))?;
                    AcornValue::Binary(
                        BinaryOp::NotEquals,
                        Box::new(left_value),
                        Box::new(right_value),
                    )
                }
                TokenType::And => {
                    AcornType::Bool.check_eq(expected_type, token)?;
                    let left_value =
                        self.evaluate_value_with_stack(stack, left, Some(&AcornType::Bool))?;
                    let right_value =
                        self.evaluate_value_with_stack(stack, right, Some(&AcornType::Bool))?;
                    AcornValue::Binary(BinaryOp::And, Box::new(left_value), Box::new(right_value))
                }
                TokenType::Or => {
                    AcornType::Bool.check_eq(expected_type, token)?;
                    let left_value =
                        self.evaluate_value_with_stack(stack, left, Some(&AcornType::Bool))?;
                    let right_value =
                        self.evaluate_value_with_stack(stack, right, Some(&AcornType::Bool))?;
                    AcornValue::Binary(BinaryOp::Or, Box::new(left_value), Box::new(right_value))
                }
                TokenType::Dot => {
                    let entity = self.evaluate_dot_expression(stack, left, right)?;
                    let potential = entity.expect_potential_value(expected_type, expression)?;
                    return self
                        .bindings
                        .maybe_resolve_value(potential, expected_type, token);
                }
                token_type => match token_type.to_infix_magic_method_name() {
                    Some(name) => self.evaluate_infix(
                        stack,
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
                let function = self.evaluate_potential_value(stack, function_expr, None)?;

                // Handle the case where the "args" are actually type parameters.
                let arg_exprs = match args_expr.as_ref() {
                    Expression::Grouping(left_delimiter, e, _) => {
                        let exprs = e.flatten_comma_separated_list();
                        if left_delimiter.token_type == TokenType::LessThan {
                            // This is a type parameter list
                            if let PotentialValue::Unresolved(unresolved) = function {
                                let mut type_params = vec![];
                                for expr in exprs {
                                    type_params.push(self.evaluate_type(expr)?);
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
                    PotentialValue::Unresolved(unresolved) => self.bindings.infer_and_apply(
                        stack,
                        unresolved,
                        arg_exprs,
                        expected_type,
                        &self.project,
                        expression,
                    )?,
                    PotentialValue::Resolved(function) => {
                        // Simple, no-type-inference-necessary construction
                        let mut args = vec![];
                        for (i, arg_expr) in arg_exprs.iter().enumerate() {
                            let arg_type: &AcornType = &function_type.arg_types[i];
                            let arg =
                                self.evaluate_value_with_stack(stack, arg_expr, Some(arg_type))?;
                            args.push(arg);
                        }
                        let value = AcornValue::apply(function, args);
                        value.check_type(expected_type, expression)?;
                        value
                    }
                }
            }
            Expression::Grouping(_, e, _) => {
                self.evaluate_value_with_stack(stack, e, expected_type)?
            }
            Expression::Binder(token, args, body, _) => {
                if args.len() < 1 {
                    return Err(token.error("binders must have at least one argument"));
                }
                let (arg_names, arg_types) = self.bind_args(stack, args, None)?;
                let body_type = match token.token_type {
                    TokenType::ForAll => Some(&AcornType::Bool),
                    TokenType::Exists => Some(&AcornType::Bool),
                    _ => None,
                };
                let ret_val = match self.evaluate_value_with_stack(stack, body, body_type) {
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
                let cond =
                    self.evaluate_value_with_stack(stack, cond_exp, Some(&AcornType::Bool))?;
                let if_value = self.evaluate_value_with_stack(stack, if_exp, expected_type)?;
                let else_value =
                    self.evaluate_value_with_stack(stack, else_exp, Some(&if_value.get_type()))?;
                AcornValue::IfThenElse(Box::new(cond), Box::new(if_value), Box::new(else_value))
            }
            Expression::Match(_, scrutinee_exp, case_exps, _) => {
                let mut expected_type: Option<AcornType> = expected_type.cloned();
                let scrutinee = self.evaluate_value_with_stack(stack, scrutinee_exp, None)?;
                let scrutinee_type = scrutinee.get_type();
                let mut cases = vec![];
                let mut indices = vec![];
                let mut all_cases = false;
                for (pattern_exp, result_exp) in case_exps {
                    let (_, args, i, total) =
                        self.evaluate_pattern(&scrutinee_type, pattern_exp)?;
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
                        self.evaluate_value_with_stack(stack, pattern_exp, Some(&scrutinee_type))?;
                    let result =
                        self.evaluate_value_with_stack(stack, result_exp, expected_type.as_ref())?;
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

    pub fn evaluate_typeclass(&self, expression: &Expression) -> compilation::Result<Typeclass> {
        let entity = self.evaluate_entity(&mut Stack::new(), expression)?;
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
    ) -> compilation::Result<Vec<TypeParam>> {
        let mut answer: Vec<TypeParam> = vec![];
        for expr in exprs {
            let name = expr.name.text().to_string();
            self.bindings.check_typename_available(&name, &expr.name)?;
            if answer.iter().any(|tp| tp.name == name) {
                return Err(expr.name.error("duplicate type parameter"));
            }
            let typeclass = match expr.typeclass.as_ref() {
                Some(e) => Some(self.evaluate_typeclass(e)?),
                None => None,
            };
            answer.push(TypeParam {
                name: expr.name.text().to_string(),
                typeclass,
            });
        }
        Ok(answer)
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
            .bindings
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
                if let Some(name) = self.bindings.canonical_to_alias.get(&global_name) {
                    let base_expr = Expression::generate_identifier(name);
                    return self.parametrize_expr(base_expr, params);
                }

                // Reference this type via referencing the imported module
                if let Some(module_name) = self.bindings.module_to_name.get(&class.module_id) {
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
            if !self.bindings.constant_name_in_use(&name) {
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
                if let Some(numerals) = &self.bindings.numerals {
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
        if name.module_id == self.bindings.module_id {
            return Ok(match &name.local_name {
                LocalName::Unqualified(word) => Expression::generate_identifier(word),
                LocalName::Attribute(left, right) => Expression::generate_dot(
                    Expression::generate_identifier(left),
                    Expression::generate_identifier(right),
                ),
            });
        }

        // Check if there's a local alias for this constant.
        if let Some(alias) = self.bindings.canonical_to_alias.get(&name) {
            return Ok(Expression::generate_identifier(alias));
        }

        // If it's a member function, check if there's a local alias for its receiver.
        // Note that the receiver could be either a class or a typeclass.
        if let LocalName::Attribute(rname, attr) = &name.local_name {
            let receiver = GlobalName::new(name.module_id, LocalName::unqualified(rname));
            if let Some(alias) = self.bindings.canonical_to_alias.get(&receiver) {
                let lhs = Expression::generate_identifier(alias);
                let rhs = Expression::generate_identifier(attr);
                return Ok(Expression::generate_dot(lhs, rhs));
            }
        }

        // Refer to this constant using its module
        match self.bindings.module_to_name.get(&name.module_id) {
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
        match self.evaluate_type(&expression) {
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
        assert!(self.evaluate_potential_type(&expression).is_err());
    }

    /// Check that the given name actually does have this type in the environment.
    pub fn expect_type(&self, name: &str, type_string: &str) {
        let name = DefinedName::guess(name);
        let value = self
            .bindings
            .get_constant_value(&name, &PanicOnError)
            .expect("no such constant");
        let env_type = value.get_type();
        assert_eq!(env_type.to_string(), type_string);
    }

    /// Check that this code, when converted to a value and back to code, is the same.
    pub fn expect_good_code(&self, input_code: &str) {
        let expression = Expression::expect_value(input_code);
        let value = self
            .evaluate_value(&expression, None)
            .expect("evaluate_value failed");
        let output_code = self.value_to_code(&value).expect("value_to_code failed");
        assert_eq!(input_code, output_code);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_evaluator_types() {
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

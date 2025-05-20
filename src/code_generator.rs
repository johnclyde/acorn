use std::fmt;

use crate::acorn_type::{AcornType, PotentialType};
use crate::acorn_value::AcornValue;
use crate::binding_map::BindingMap;
use crate::expression::{Declaration, Expression};
use crate::module::{Module, ModuleId};
use crate::names::{GlobalName, LocalName};
use crate::token::TokenType;

pub type Result<T> = std::result::Result<T, Error>;

pub struct CodeGenerator<'a> {
    /// Bindings for the module we are generating code in.
    bindings: &'a BindingMap,

    /// We use variables named x0, x1, x2, etc for universal variables.
    next_x: u32,

    /// We use variables named k0, k1, k2, etc for existential variables.
    next_k: u32,

    /// The names we have assigned to indexed variables so far.
    var_names: Vec<String>,
}

impl CodeGenerator<'_> {
    /// Creates a new code generator.
    pub fn new(bindings: &BindingMap) -> CodeGenerator {
        CodeGenerator {
            bindings,
            next_x: 0,
            next_k: 0,
            var_names: vec![],
        }
    }

    /// Returns an error if this type can't be encoded as an expression.
    /// This will happen when it's defined in a module that isn't directly imported.
    /// In theory we could fix this, but we would have to have a way to suggest imports.
    /// There are probably other error cases.
    pub fn type_to_expr(&self, acorn_type: &AcornType) -> Result<Expression> {
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
            .get_typename_for_type(&PotentialType::Resolved(acorn_type.clone()))
        {
            return Ok(Expression::generate_identifier(name));
        }

        match acorn_type {
            AcornType::Data(class, params) => {
                // Check if it's a type from a module that we have imported
                // See if we have an alias
                let global_name =
                    GlobalName::new(class.module_id, LocalName::unqualified(&class.name));
                if let Some(name) = self.bindings.get_alias(&global_name) {
                    let base_expr = Expression::generate_identifier(name);
                    return self.parametrize_expr(base_expr, params);
                }

                // Reference this type via referencing the imported module
                if let Some(module_name) = self.bindings.get_name_for_module_id(class.module_id) {
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

        Err(Error::unnamed_type(acorn_type))
    }

    /// Adds parameters, if there are any, to an expression representing a type.
    fn parametrize_expr(&self, base_expr: Expression, params: &[AcornType]) -> Result<Expression> {
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

    /// If this value cannot be expressed in a single chunk of code, returns an error.
    /// For example, it might refer to a constant that is not in scope.
    pub fn value_to_code(&mut self, value: &AcornValue) -> Result<String> {
        let expr = self.value_to_expr(value, false)?;
        Ok(expr.to_string())
    }

    /// Given a module and a name, find an expression that refers to the name.
    /// The name can be dotted, if it's a class member.
    /// Note that:
    ///   module, the canonical module of the entity we are trying to express
    /// is different from
    ///   self.module, the module we are trying to express the name in
    fn name_to_expr(&self, name: &GlobalName) -> Result<Expression> {
        // We can't do skolems
        if name.module_id == Module::SKOLEM {
            return Err(Error::skolem(&name.local_name.to_string()));
        }

        // Handle numeric literals
        if let LocalName::Attribute(class, attr) = &name.local_name {
            if attr.chars().all(|ch| ch.is_ascii_digit()) {
                let numeral = TokenType::Numeral.new_token(attr);

                // If it's the default type, we don't need to scope it
                if let Some(numerals) = self.bindings.numerals() {
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
        if name.module_id == self.bindings.module_id() {
            return Ok(match &name.local_name {
                LocalName::Unqualified(word) => Expression::generate_identifier(word),
                LocalName::Attribute(left, right) => Expression::generate_dot(
                    Expression::generate_identifier(left),
                    Expression::generate_identifier(right),
                ),
            });
        }

        // Check if there's a local alias for this constant.
        if let Some(alias) = self.bindings.get_alias(&name) {
            return Ok(Expression::generate_identifier(alias));
        }

        // If it's a member function, check if there's a local alias for its receiver.
        // Note that the receiver could be either a class or a typeclass.
        if let LocalName::Attribute(rname, attr) = &name.local_name {
            let receiver = GlobalName::new(name.module_id, LocalName::unqualified(rname));
            if let Some(alias) = self.bindings.get_alias(&receiver) {
                let lhs = Expression::generate_identifier(alias);
                let rhs = Expression::generate_identifier(attr);
                return Ok(Expression::generate_dot(lhs, rhs));
            }
        }

        // Refer to this constant using its module
        match self.bindings.get_name_for_module_id(name.module_id) {
            Some(module_name) => {
                let mut parts: Vec<&str> = vec![module_name];
                parts.extend(name.local_name.name_chain().unwrap().into_iter());
                Ok(Expression::generate_identifier_chain(&parts))
            }
            None => Err(Error::UnimportedModule(
                name.module_id,
                name.local_name.to_string(),
            )),
        }
    }

    /// If use_x is true we use x-variables; otherwise we use k-variables.
    fn generate_quantifier_expr(
        &mut self,
        token_type: TokenType,
        quants: &Vec<AcornType>,
        value: &AcornValue,
        use_x: bool,
    ) -> Result<Expression> {
        let initial_var_names_len = self.var_names.len();
        let mut decls = vec![];
        for arg_type in quants {
            let var_name = if use_x {
                self.bindings.next_indexed_var('x', &mut self.next_x)
            } else {
                self.bindings.next_indexed_var('k', &mut self.next_k)
            };
            let name_token = TokenType::Identifier.new_token(&var_name);
            self.var_names.push(var_name);
            let type_expr = self.type_to_expr(arg_type)?;
            let var_name = Declaration::Typed(name_token, type_expr);
            let decl = var_name;
            decls.push(decl);
        }
        let subresult = self.value_to_expr(value, false)?;
        self.var_names.truncate(initial_var_names_len);
        Ok(Expression::Binder(
            token_type.generate(),
            decls,
            Box::new(subresult),
            TokenType::RightBrace.generate(),
        ))
    }

    /// Convert an AcornValue to an Expression.
    /// var_names is the names we have assigned to indexed variables so far.
    /// We automatically generate variable names sometimes, using next_x and next_k.
    /// "inferrable" is true if the type of this value can be inferred, which means
    /// we don't need top level parameters.
    fn value_to_expr(&mut self, value: &AcornValue, inferrable: bool) -> Result<Expression> {
        match value {
            AcornValue::Variable(i, _) => Ok(Expression::generate_identifier(
                &self.var_names[*i as usize],
            )),
            AcornValue::Application(fa) => {
                let mut args = vec![];
                for arg in &fa.args {
                    // We currently never infer the type of arguments from the type of the function.
                    // Inference only goes the other way.
                    // We could improve this at some point.
                    args.push(self.value_to_expr(arg, false)?);
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

                let f = self.value_to_expr(&fa.function, true)?;
                let grouped_args = Expression::generate_paren_grouping(args);
                Ok(Expression::Concatenation(
                    Box::new(f),
                    Box::new(grouped_args),
                ))
            }
            AcornValue::Binary(op, left, right) => {
                let left = self.value_to_expr(left, false)?;
                let right = self.value_to_expr(right, false)?;
                let token = op.token_type().generate();
                Ok(Expression::Binary(Box::new(left), token, Box::new(right)))
            }
            AcornValue::Not(x) => {
                let x = self.value_to_expr(x, false)?;
                Ok(Expression::generate_unary(TokenType::Not, x))
            }
            AcornValue::ForAll(quants, value) => {
                self.generate_quantifier_expr(TokenType::ForAll, quants, value, true)
            }
            AcornValue::Exists(quants, value) => {
                self.generate_quantifier_expr(TokenType::Exists, quants, value, false)
            }
            AcornValue::Lambda(quants, value) => {
                self.generate_quantifier_expr(TokenType::Function, quants, value, true)
            }
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
                let condition = self.value_to_expr(condition, false)?;
                let if_value = self.value_to_expr(if_value, false)?;
                let else_value = self.value_to_expr(else_value, false)?;
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
}

#[derive(Debug)]
pub enum Error {
    // Trouble expressing a skolem function created during normalization.
    Skolem(String),

    // Trouble referencing a module that has not been directly imported.
    UnimportedModule(ModuleId, String),

    // Trouble using a type that we can't find the name for.
    UnnamedType(String),

    // Some sort of value we could handle, but we don't yet, because it's rare.
    UnhandledValue(String),

    // The code contains the explicit goal, which we can't generate code for.
    ExplicitGoal,

    // When you try to generate code but there is no proof
    NoProof,

    // Something went wrong, it's our fault, and we can't figure out what it is
    InternalError(String),
}

impl Error {
    pub fn skolem(s: &str) -> Error {
        Error::Skolem(s.to_string())
    }

    pub fn unnamed_type(acorn_type: &AcornType) -> Error {
        Error::UnnamedType(format!("{:?}", acorn_type))
    }

    pub fn unhandled_value(s: &str) -> Error {
        Error::UnhandledValue(s.to_string())
    }

    pub fn error_type(&self) -> &'static str {
        match self {
            Error::Skolem(_) => "Skolem",
            Error::UnimportedModule(..) => "UnimportedModule",
            Error::UnnamedType(_) => "UnnamedType",
            Error::UnhandledValue(_) => "UnhandledValue",
            Error::ExplicitGoal => "ExplicitGoal",
            Error::NoProof => "NoProof",
            Error::InternalError(_) => "InternalError",
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Skolem(s) => {
                write!(f, "could not find a name for the skolem constant: {}", s)
            }
            Error::UnimportedModule(_, name) => {
                write!(
                    f,
                    "could not generate code using '{}' because it is not imported",
                    name
                )
            }
            Error::UnnamedType(s) => {
                write!(f, "could not figure out a name for the type: {}", s)
            }
            Error::UnhandledValue(s) => {
                write!(f, "codegen for '{}' values is not yet implemented", s)
            }
            Error::ExplicitGoal => {
                write!(f, "could not isolate the goal at the end of the proof")
            }
            Error::NoProof => write!(f, "no proof"),
            Error::InternalError(s) => {
                write!(f, "internal error: {}", s)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::project::Project;

    #[test]
    fn test_code_generation() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            type MyType: axiom
            let t: MyType = axiom
        "#,
        );
        p.check_code("main", "t");
        p.check_code("main", "forall(x0: MyType) { x0 = t }");
    }
}

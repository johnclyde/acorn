use std::fmt;

use crate::acorn_type::{AcornType, Class, PotentialType, Typeclass};
use crate::acorn_value::{AcornValue, ConstantInstance};
use crate::binding_map::BindingMap;
use crate::expression::{Declaration, Expression};
use crate::module::{Module, ModuleId};
use crate::names::ConstantName;
use crate::token::TokenType;
use crate::type_unifier::TypeclassRegistry;

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

    fn class_to_expr(&self, class: &Class) -> Result<Expression> {
        if class.module_id == self.bindings.module_id() {
            return Ok(Expression::generate_identifier(&class.name));
        }

        // Check if we have an alias
        if let Some(alias) = self.bindings.class_alias(&class) {
            return Ok(Expression::generate_identifier(alias));
        }

        // Reference this type via referencing the imported module
        if let Some(module_name) = self.bindings.get_name_for_module_id(class.module_id) {
            return Ok(Expression::generate_identifier_chain(&[
                module_name,
                &class.name,
            ]));
        }
        Err(Error::unnamed_type(&class))
    }

    /// Returns an error if this type can't be encoded as an expression.
    /// This will happen when it's defined in a module that isn't directly imported.
    /// In theory we could fix this, but we would have to have a way to suggest imports.
    /// There are probably other error cases.
    pub fn type_to_expr(&self, acorn_type: &AcornType) -> Result<Expression> {
        // Check if there's a local name for this exact type
        if let Some(name) = self
            .bindings
            .get_typename_for_type(&PotentialType::Resolved(acorn_type.clone()))
        {
            return Ok(Expression::generate_identifier(name));
        }

        match acorn_type {
            AcornType::Data(class, params) => {
                let base_expr = self.class_to_expr(class)?;

                self.parametrize_expr(base_expr, params)
            }
            AcornType::Variable(param) | AcornType::Arbitrary(param) => {
                Ok(Expression::generate_identifier(&param.name))
            }
            AcornType::Function(ft) => {
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
                Ok(Expression::Binary(
                    Box::new(lhs),
                    TokenType::RightArrow.generate(),
                    Box::new(rhs),
                ))
            }
            AcornType::Empty => Err(Error::InternalError("empty type generated".to_string())),
            AcornType::Bool => Err(Error::InternalError("Bool unbound".to_string())),
        }
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

    /// Given a constant instance, find an expression that refers to it.
    /// This does *not* include the parameters.
    fn const_to_expr(&self, ci: &ConstantInstance) -> Result<Expression> {
        // We can't do skolems
        if ci.name.module_id() == Module::SKOLEM {
            return Err(Error::skolem(&ci.name.to_string()));
        }

        // Handle numeric literals
        if let Some((_, class_name, attr)) = ci.name.as_attribute() {
            if attr.chars().all(|ch| ch.is_ascii_digit()) {
                let class = Class {
                    module_id: ci.name.module_id(),
                    name: class_name.to_string(),
                };

                let numeral = TokenType::Numeral.new_token(&attr);

                // If it's the default type, we don't need to scope it
                if self.bindings.numerals() == Some(&class) {
                    return Ok(Expression::Singleton(numeral));
                }

                // Otherwise, we need to scope it by the type
                let numeric_type = self.class_to_expr(&class)?;
                return Ok(Expression::generate_dot(
                    numeric_type,
                    Expression::Singleton(numeral),
                ));
            }
        }

        // Handle local constants
        if ci.name.module_id() == self.bindings.module_id() {
            return Ok(match &ci.name {
                ConstantName::Unqualified(_, word) => Expression::generate_identifier(word),
                ConstantName::ClassAttribute(class, attr) => Expression::generate_dot(
                    Expression::generate_identifier(&class.name),
                    Expression::generate_identifier(attr),
                ),
                ConstantName::TypeclassAttribute(tc, attr) => Expression::generate_dot(
                    Expression::generate_identifier(&tc.name),
                    Expression::generate_identifier(attr),
                ),
            });
        }

        // Check if there's a local alias for this constant.
        if let Some(alias) = self.bindings.constant_alias(&ci.name) {
            return Ok(Expression::generate_identifier(alias));
        }

        // If it's a member function, check if there's a local alias for its receiver.
        // Note that the receiver could be either a class or a typeclass.
        if let Some((_, rname, attr)) = ci.name.as_attribute() {
            // Check if this is a class attribute
            let class = Class {
                module_id: ci.name.module_id(),
                name: rname.to_string(),
            };
            if let Some(alias) = self.bindings.class_alias(&class) {
                let lhs = Expression::generate_identifier(alias);
                let rhs = Expression::generate_identifier(attr);
                return Ok(Expression::generate_dot(lhs, rhs));
            }

            // Check if this is a typeclass attribute
            let typeclass = Typeclass {
                module_id: ci.name.module_id(),
                name: rname.to_string(),
            };
            if let Some(alias) = self.bindings.typeclass_alias(&typeclass) {
                let lhs = Expression::generate_identifier(alias);
                let rhs = Expression::generate_identifier(attr);
                return Ok(Expression::generate_dot(lhs, rhs));
            }
        }

        // Refer to this constant using its module
        match self.bindings.get_name_for_module_id(ci.name.module_id()) {
            Some(module_name) => {
                let mut parts: Vec<&str> = vec![module_name];
                match &ci.name {
                    ConstantName::Unqualified(_, name) => parts.push(name),
                    ConstantName::ClassAttribute(class, attr) => {
                        parts.push(&class.name);
                        parts.push(attr);
                    }
                    ConstantName::TypeclassAttribute(tc, attr) => {
                        parts.push(&tc.name);
                        parts.push(attr);
                    }
                }
                Ok(Expression::generate_identifier_chain(&parts))
            }
            None => Err(Error::UnimportedModule(
                ci.name.module_id(),
                ci.name.to_string(),
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
                let receiver_type = fa.args[0].get_type();
                if let Some((module_id, entity, attr)) = fa.function.as_attribute() {
                    if self
                        .bindings
                        .inherits_attributes(&receiver_type, module_id, entity)
                    {
                        // We can use receiver+attribute syntax
                        if args.len() == 1 {
                            // Prefix operators
                            if let Some(op) = TokenType::from_prefix_magic_method_name(&attr) {
                                return Ok(Expression::generate_unary(op, args.pop().unwrap()));
                            }
                        }

                        if args.len() == 2 {
                            // Infix operators
                            if let Some(op) = TokenType::from_infix_magic_method_name(&attr) {
                                let right = args.pop().unwrap();
                                let left = args.pop().unwrap();
                                return Ok(Expression::generate_binary(left, op, right));
                            }

                            // Long numeric literals
                            if attr == "read" && args[0].is_number() {
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
                            Expression::generate_identifier(&attr),
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
                    if let Some((module_id, entity, attr)) = c.name.as_attribute() {
                        if self
                            .bindings
                            .inherits_attributes(&c.params[0], module_id, entity)
                        {
                            // We can use receiver+attribute syntax
                            let lhs = self.type_to_expr(&c.params[0])?;
                            let rhs = Expression::generate_identifier(&attr);
                            return Ok(Expression::generate_dot(lhs, rhs));
                        }
                    }
                }

                let const_expr = self.const_to_expr(&c)?;

                if !inferrable && !c.params.is_empty() {
                    self.parametrize_expr(const_expr, &c.params)
                } else {
                    // We don't need to parametrize because it can be inferred
                    Ok(const_expr)
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

    /// For testing. Panics if generating code for this value does not give expected.
    pub fn expect(bindings: &BindingMap, input: &str, value: &AcornValue, expected: &str) {
        let output = match CodeGenerator::new(bindings).value_to_code(&value) {
            Ok(output) => output,
            Err(e) => panic!("code generation error: {}", e),
        };

        if output != expected {
            panic!(
                "\nconverted:\n  {}\nto value:\n  {}\nand back to:\n  {}\nbut expected:\n  {}\n",
                input, value, output, expected
            );
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

    pub fn unnamed_type(class: &Class) -> Error {
        Error::UnnamedType(class.name.to_string())
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

    #[test]
    fn test_code_for_imported_things() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/stuff.ac",
            r#"
            let thing1: Bool = axiom
            let thing2: Bool = axiom
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import stuff
            let st1: Bool = stuff.thing1
        "#,
        );
        p.check_code_into("main", "stuff.thing1", "st1");
        p.check_code("main", "st1");
        p.check_code("main", "stuff.thing2");
    }

    #[test]
    fn test_imported_member_functions() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/boolpair.ac",
            r#"
            structure BoolPair {
                first: Bool
                second: Bool
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import boolpair
            type BoolPair: boolpair.BoolPair
            let first: BoolPair -> Bool = BoolPair.first
        "#,
        );
        p.expect_ok("main");
        p.check_code("main", "first");
        p.check_code_into("main", "BoolPair.first", "first");
        p.check_code_into("main", "boolpair.BoolPair.first", "first");

        p.check_code("main", "BoolPair.second");
        p.check_code_into("main", "boolpair.BoolPair.second", "BoolPair.second");
    }

    #[test]
    fn test_structure_aliasing() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/stuff.ac",
            r#"
            structure Foo {
                member: Bool
            }
            type Bar: Foo
        "#,
        );
        p.expect_ok("stuff");
        p.check_code_into("stuff", "Bar.member", "Foo.member");
    }

    #[test]
    fn test_names_imported_via_from() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/stuff.ac",
            r#"
            type Foo: axiom
            class Foo {
                let foo: Bool = true
                let foo2: Bool = false
            }
            type Bar: Foo
            let bar: Bar = axiom
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from stuff import Foo, Bar, bar
            let x: Bool = Bar.foo
            let y: Bar = bar
        "#,
        );
        p.expect_ok("stuff");
        p.expect_ok("main");
        p.check_code("main", "x");
        p.check_code_into("main", "y", "bar");
        p.check_code_into("main", "stuff.Foo.foo2", "Foo.foo2");
    }

    #[test]
    fn test_imported_numbers_codegen_basic() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/nat.ac",
            r#"
            inductive Nat {
                0
                suc(Nat)
            }

            numerals Nat

            class Nat {
                define add(self, other: Nat) -> Nat {
                    0
                }
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from nat import Nat
            "#,
        );
        p.check_code_into("main", "nat.Nat.0", "Nat.0");
        p.check_code_into("main", "Nat.suc(Nat.0)", "Nat.0.suc");
        p.check_code_into("main", "Nat.add(Nat.0, Nat.0)", "Nat.0 + Nat.0");
    }

    #[test]
    fn test_imported_numbers_codegen_with_numerals() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/nat.ac",
            r#"
            inductive Nat {
                0
                suc(Nat)
            }

            numerals Nat

            class Nat {
                define add(self, other: Nat) -> Nat {
                    0
                }
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from nat import Nat
            numerals Nat
            "#,
        );
        p.check_code_into("main", "nat.Nat.0", "0");
        p.check_code_into("main", "Nat.suc(Nat.0)", "0.suc");
        p.check_code_into("main", "Nat.add(Nat.0, Nat.0)", "0 + 0");
    }

    #[test]
    fn test_import_without_from_codegen() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/boolbox.ac",
            r#"
            structure BoolBox {
                item: Bool
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import boolbox
        "#,
        );
        p.check_code("main", "forall(x0: boolbox.BoolBox) { true }");
    }

    #[test]
    fn test_importing_a_generic_type() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/pair.ac",
            r#"
            structure Pair<T, U> {
                first: T
                second: U
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from pair import Pair
            "#,
        );
        p.check_code("main", "forall(x0: Pair<Bool, Bool>) { true }");
        p.check_code(
            "main",
            "forall(x0: Bool, x1: Bool) { Pair.new(x0, x1).second = x1 }",
        );
    }

    #[test]
    fn test_generic_type_in_imported_module() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/pair.ac",
            r#"
            structure Pair<T, U> {
                first: T
                second: U
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import pair
            "#,
        );
        p.check_code("main", "forall(x0: pair.Pair<Bool, Bool>) { true }");
    }

    #[test]
    fn test_aliasing_local_generic_constant() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/pair.ac",
            r#"
            structure Pair<T, U> {
                first: T
                second: U
            }

            let pbbn: (Bool, Bool) -> Pair<Bool, Bool> = Pair<Bool, Bool>.new
            "#,
        );
        p.expect_ok("pair");
        p.check_code("pair", "pbbn(false, true)");
    }

    #[test]
    fn test_importing_generic_function() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/pair.ac",
            r#"
            structure Pair<T, U> {
                first: T
                second: U
            }

            define double<T>(x: T) -> Pair<T, T> {
                Pair.new(x, x)
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from pair import double
            "#,
        );
        p.check_code("main", "double(true)");
    }

    #[test]
    fn test_generic_function_in_imported_module() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/pair.ac",
            r#"
            structure Pair<T, U> {
                first: T
                second: U
            }

            define double<T>(x: T) -> Pair<T, T> {
                Pair.new(x, x)
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import pair
            "#,
        );
        p.check_code("main", "pair.double(true)");
    }

    #[test]
    fn test_importing_typeclasses_with_import() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/magma.ac",
            r#"
            typeclass M: Magma {
                op: (M, M) -> M
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import magma

            inductive Z1 {
                zero
            }

            instance Z1: magma.Magma {
                define op(self, other: Z1) -> Z1 {
                    Z1.zero
                }
            }
            "#,
        );
        p.check_code("main", "magma.Magma.op(Z1.zero, Z1.zero) = Z1.zero");
    }

    #[test]
    fn test_importing_typeclasses_with_from() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/magma.ac",
            r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from magma import Magma

            inductive Z1 {
                zero
            }

            instance Z1: Magma {
                define mul(self, other: Z1) -> Z1 {
                    Z1.zero
                }
            }
            "#,
        );
        p.check_code("main", "Magma.mul(Z1.zero, Z1.zero) = Z1.zero");
    }

    #[test]
    fn test_codegen_typeclass_infix() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            theorem goal<M: Magma>(x: M) {
                x * x = x
            }
            "#,
        );
        p.check_goal_code("main", "goal", "x * x = x");
    }

    #[test]
    fn test_codegen_extended_infix() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            typeclass T: Thing extends Magma {
                thing_property: Bool
            }

            theorem goal<T: Thing>(x: T) {
                x * x = x
            }
            "#,
        );
        p.check_goal_code("main", "goal", "x * x = x");
    }

    #[test]
    fn test_codegen_for_imported_typeclasses() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/foo.ac",
            r#"
            typeclass F: Foo {
                zero: F
                add: (F, F) -> F
                neg: F -> F
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from foo import Foo

            typeclass B: Bar extends Foo {
                bar_property: Bool
            }

            theorem goal<B: Bar>(x: B) {
                x + -x = B.zero + B.zero
            }
            "#,
        );
        p.check_goal_code("main", "goal", "x + -x = B.zero + B.zero");
    }

    #[test]
    fn test_codegen_for_quantified_types() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            typeclass F: Foo {
                item: F
            }

            inductive List<T> {
                nil
                cons(T, List<T>)
            }

            structure Bar {
                item: Bool
            }

            theorem goal1 {
                exists(a: Bar) {
                    true
                }
            }

            theorem goal2 {
                exists(a: List<Bool>) {
                    true
                }
            }

            theorem goal3<F: Foo> {
                exists(a: List<F>) {
                    true
                }
            }

            theorem goal4 {
                exists(a: Bool) {
                    a
                }
            }
            "#,
        );
        p.check_goal_code("main", "goal1", "exists(k0: Bar) { true }");
        p.check_goal_code("main", "goal2", "exists(k0: List<Bool>) { true }");
        p.check_goal_code("main", "goal3", "exists(k0: List<F>) { true }");
        p.check_goal_code("main", "goal4", "exists(k0: Bool) { k0 }");
    }

    #[test]
    fn test_codegen_indirect_attribute() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/foo_base.ac",
            r#"
            inductive Foo {
                foo
            }

            class Foo {
                define add(self, other: Foo) -> Foo {
                    Foo.foo
                }
            }
        "#,
        );
        p.mock(
            "/mock/foo_middle.ac",
            r#"
            from foo_base import Foo
            class Foo {
                define mul(self, other: Foo) -> Foo {
                    Foo.foo
                }
            }
            "#,
        );
        p.mock(
            "/mock/foo.ac",
            r#"
            from foo_middle import Foo
            class Foo {
                define sub(self, other: Foo) -> Foo {
                    Foo.foo
                }
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from foo import Foo
            "#,
        );
        p.check_code("main", "Foo.add");
        p.check_code("main", "Foo.foo.add");
        p.check_code("main", "Foo.foo + Foo.foo");
        // p.check_code("main", "Foo.mul");
        // p.check_code("main", "Foo.foo.mul");
        // p.check_code("main", "Foo.foo * Foo.foo");
        // p.check_code("main", "Foo.sub");
        // p.check_code("main", "Foo.foo.sub");
        // p.check_code("main", "Foo.foo - Foo.foo");
    }
}

use acorn::environment::Environment;

#[test]
fn test_env_with_typeclass() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            "#,
    );
}

#[test]
fn test_env_with_bad_typeclass() {
    let mut env = Environment::test();
    env.bad(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> Magma
            }
            "#,
    );
}

#[test]
fn test_env_typeclass_in_define_template() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            define true_fn<T: Magma>(a: T) -> Bool {
                true
            }
            "#,
    );
}

#[test]
fn test_env_typeclass_attributes() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            define squared<T: Magma>(a: T) -> T {
                Magma.mul(a, a)
            }
            "#,
    );
}

#[test]
fn test_env_typeclass_instance_methods() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            define squared<T: Magma>(a: T) -> T {
                a.mul(a)
            }
            "#,
    );
}

#[test]
fn test_env_typeclass_in_theorem_template() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            theorem wrong_but_syntactic<Q: Magma>(a: Q, b: Q) {
                a.mul(b) = b.mul(a)
            }
            "#,
    );
}

#[test]
fn test_env_typechecking_with_typeclasses() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            "#,
    );
    env.bad(
        r#"
            theorem wrong_by_typecheck<Q: Magma>(a: Q, b: Q) {
                a.mul(b) = b.mul
            }
            "#,
    );
}

#[test]
fn test_env_typeclass_in_structure() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            
            structure MagmaPair<T: Magma> {
                first: T
                second: T
            }

            class MagmaPair<T: Magma> {
                define prod(self) -> T {
                    self.first.mul(self.second)
                }
            }
            "#,
    );
}

#[test]
fn test_env_typeclasses_match_between_structure_and_class() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            
            structure MagmaPair<T> {
                first: T
                second: T
            }
            "#,
    );
    env.bad(
        r#"
            class MagmaPair<T: Magma> {
                define prod(self) -> T {
                    self.first.mul(self.second)
                }
            }
            "#,
    );
}

#[test]
fn test_env_operator_on_typeclass() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            
            // Not true but syntactically valid
            theorem commutative<T: Magma>(a: T, b: T) {
                a * b = b * a
            }
            "#,
    );
}

#[test]
fn test_env_instance_statement_define() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            inductive State {
                clean
                dirty
            }

            instance State: Magma {
                define mul(self, other: State) -> State {
                    if self = State.clean and other = State.clean {
                        State.clean
                    } else {
                        State.dirty
                    }
                }
            }
            "#,
    );
}

#[test]
fn test_env_instance_statement_needs_all_attributes() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass B: Bimagma {
                mul1: (B, B) -> B
                mul2: (B, B) -> B
            }

            inductive State {
                clean
                dirty
            }
            "#,
    );
    // Needs to also define mul2
    env.bad(
        r#"
            instance State: Bimagma {
                define mul1(self, other: State) -> State {
                    State.clean
                }
            }
            "#,
    );
}

#[test]
fn test_env_instance_statement_no_extra_define() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            inductive State {
                clean
                dirty
            }
            "#,
    );
    env.bad(
        r#"
            instance State: Magma {
                define mul(self, other: State) -> State {
                    State.clean
                }
                define add(self, other: State) -> State {
                    State.clean
                }
            }
            "#,
    );
}

#[test]
fn test_env_instance_defines_must_match_type() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            inductive State {
                clean
                dirty
            }
            "#,
    );
    env.bad(
        r#"
            instance State: Magma {
                define mul(self, other: State) -> Bool {
                    true
                }
            }
            "#,
    );
}

#[test]
fn test_env_using_typeclass_methods() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            inductive State {
                clean
                dirty
            }

            instance State: Magma {
                define mul(self, other: State) -> State {
                    if self = State.clean and other = State.clean {
                        State.clean
                    } else {
                        State.dirty
                    }
                }
            }

            theorem commutative(a: State, b: State) {
                Magma.mul(a, b) = Magma.mul(b, a)
            }
            "#,
    );
}

#[test]
fn test_env_instance_statement_let() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass P: PointedSet {
                basepoint: P
            }

            inductive Z2 {
                zero
                one
            }

            instance Z2: PointedSet {
                let basepoint: Z2 = Z2.zero
            }
            "#,
    );
}

#[test]
fn test_env_instance_statement_no_extra_let() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass P: PointedSet {
                basepoint: P
            }

            inductive Z2 {
                zero
                one
            }
            "#,
    );
    env.bad(
        r#"
            instance Z2: PointedSet {
                let basepoint: Z2 = Z2.zero
                let other: Z2 = Z2.one
            }
            "#,
    );
}

#[test]
fn test_env_instance_lets_must_match_type() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass P: PointedSet {
                basepoint: P
            }

            inductive Z2 {
                zero
                one
            }
            "#,
    );
    env.bad(
        r#"
            instance Z2: PointedSet {
                let basepoint: Bool = true
            }
            "#,
    );
}

#[test]
fn test_env_parametrizing_typeclass_constant() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass P: PointedSet {
                basepoint: P
            }

            inductive Z2 {
                zero
                one
            }

            instance Z2: PointedSet {
                let basepoint: Z2 = Z2.zero
            }

            theorem goal {
                Z2.zero = PointedSet.basepoint<Z2>
            }
            "#,
    );
}

#[test]
fn test_env_forbid_instance_on_alias() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Flagged {
                flag: Bool
            }
            type Foo: axiom
            type Bar: Foo
            "#,
    );
    env.bad(
        r#"
            instance Bar: Flagged {
                let flag: Bool = true
            }
            "#,
    );
}

#[test]
fn test_env_arbitrary_type_attributes() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Flagged {
                flag: Bool
            }
            theorem goal<F: Flagged> {
                F.flag or not F.flag
            }
            "#,
    );
}

#[test]
fn test_env_bool_not_instance_of_anything() {
    let mut env = Environment::test();
    env.add(
        r#"
        typeclass F: Flagged {
            flag: Bool
        }
        type Foo: axiom
        instance Foo: Flagged {
            let flag: Bool = true
        }
        define get_flag<F: Flagged>(x: F) -> Bool {
            F.flag
        }
        "#,
    );
    env.bad(
        r#"
        theorem goal {
            get_flag(true)
        }
        "#,
    );
}

#[test]
fn test_env_typechecking_captures_instance_relationships() {
    let mut env = Environment::test();
    env.add(
        r#"
        typeclass F: Flagged {
            flag: Bool
        }
        type Foo: axiom
        type Bar: axiom
        instance Bar: Flagged {
            let flag: Bool = true
        }
        define get_flag<F: Flagged>(x: F) -> Bool {
            F.flag
        }
        theorem goal_bar(b: Bar) {
            get_flag(b)
        }
        "#,
    );
    env.bad(
        r#"
        theorem goal_foo(f: Foo) {
            get_flag(f)
        }
        "#,
    );
}

#[test]
fn test_env_typeclasses_can_have_conditions() {
    let mut env = Environment::test();
    env.add(
        r#"
        typeclass S: Singleton {
            value: S

            unique(x: S) {
                x = S.value
            }
        }

        theorem are_equal<S: Singleton>(a: S, b: S) {
            a = b
        } by {
            Singleton.unique(a)
            Singleton.unique(b)
        }
        "#,
    );
}

#[test]
fn test_env_instance_statement_accepts_by_block() {
    let mut env = Environment::test();
    env.add(
        r#"
        typeclass S: Singleton {
            value: S

            unique(x: S) {
                x = S.value
            }
        }

        inductive Z1 {
            zero
        }

        instance Z1: Singleton {
            let value: Z1 = Z1.zero
        } by {
            forall(x: Z1) {
                x = Z1.zero
            }
        }
        "#,
    );
}

#[test]
fn test_env_must_resolve_typeclass_constants() {
    let mut env = Environment::test();
    env.add(
        r#"
        typeclass P: PointedSet {
            zero: P
        }
        "#,
    );
    env.bad(
        r#"
        theorem goal {
            PointedSet.zero = PointedSet.zero
        }
        "#,
    );
}

#[test]
fn test_env_let_statements_with_params() {
    let mut env = Environment::test();
    env.add(
        r#"
        typeclass P: PointedSet {
            zero: P
        }

        let z<P: PointedSet>: P = P.zero

        define is_zero<P: PointedSet>(x: P) -> Bool {
            z<P> = x
        }
        "#,
    );
}

#[test]
fn test_typeclass_codegen() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                inverse: F -> F
                add: (F, F) -> F
                bar: F
            }

            let qux<F: Foo>: Bool = axiom

            theorem goal<F: Foo>(f: F) {
                true
            }
        "#,
    );

    env.get_bindings("goal").expect_good_code("f.inverse");
    env.get_bindings("goal").expect_good_code("f + f");
    env.get_bindings("goal").expect_good_code("F.bar");
    env.get_bindings("goal").expect_good_code("F.add");
    env.get_bindings("goal").expect_good_code("qux<F>");
}

#[test]
fn test_instance_codegen() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                inverse: F -> F
                bar: F
            }

            inductive Qux {
                qux
                quux
            }

            let other: Qux -> Qux = axiom

            instance Qux: Foo {
                let inverse: Qux -> Qux = other
                let bar: Qux = Qux.qux
            }
        "#,
    );

    env.bindings.expect_good_code("Foo.bar<Qux>");
    env.bindings.expect_good_code("Foo.inverse(Qux.qux)");
}

#[test]
fn test_env_handles_bad_typeclass_name_in_theorem() {
    let mut env = Environment::test();
    env.bad(
        r#"
            theorem goal<F: Foo> {
                true
            }
        "#,
    );
}

#[test]
fn test_env_handles_bad_typeclass_name_in_class_param() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive List<T> {
                nil
                cons(T, List<T>)
            }
            "#,
    );
    env.bad(
        r#"
            class List<F: Foo> {
                let b: Bool = true
            }
        "#,
    );
}

#[test]
fn test_env_basic_typeclass_extension() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                property: F -> Bool
            }

            typeclass B: Bar extends Foo {
                property_true(b: B) {
                    b.property
                }
            }

            inductive Qux {
                qux
            }

            class Qux {
                define q(self) -> Bool {
                    true
                }
            }

            instance Qux: Foo {
                let property: Qux -> Bool = Qux.q
            }

            instance Qux: Bar {
            }
            "#,
    );
}

#[test]
fn test_env_instances_of_extended_must_be_base() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                property: F -> Bool
            }

            typeclass B: Bar extends Foo {
                property_true(b: B) {
                    b.property
                }
            }

            inductive Qux {
                qux
            }
        "#,
    );
    // Should fail because Qux is not a Foo.
    env.bad(
        r#"
            instance Qux: Bar {
            }
        "#,
    );
}

#[test]
fn test_env_no_redefining_property_in_extension() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                property: F -> Bool
            }
        "#,
    );
    // Should fail because property can't be redefined.
    env.bad(
        r#"
            typeclass B: Bar extends Foo {
                property: B -> Bool
            }
        "#,
    );
}

#[test]
fn test_env_empty_zero_extension_not_ok() {
    let mut env = Environment::test();
    env.bad(
        r#"
            typeclass F: Foo {
            }
        "#,
    );
}

#[test]
fn test_env_empty_single_extension_not_ok() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                property: F -> Bool
            }
        "#,
    );
    env.bad(
        r#"
            typeclass B: Bar extends Foo {
            }
        "#,
    );
}

#[test]
fn test_env_empty_double_extension_ok() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                property: F -> Bool
            }
            typeclass B: Bar {
                other_property: B -> Bool
            }
            typeclass Q: Qux extends Foo, Bar {
            }
        "#,
    );
}

#[test]
fn test_env_typeclass_no_block_syntax() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                property: F -> Bool
            }
            typeclass B: Bar {
                other_property: B -> Bool
            }
            typeclass Qux extends Foo, Bar
        "#,
    );
}

#[test]
fn test_env_instance_no_block_syntax() {
    let mut env = Environment::test();
    env.add(
        r#"
            // Define a simple type
            type Nat: axiom
            
            // A typeclass with only conditions, no constants
            typeclass T: Trivial {
                reflexive(x: T) {
                    x = x
                }
            }
            
            // This should work with no-block syntax since no definitions are needed
            instance Nat: Trivial
        "#,
    );
}

#[test]
fn test_env_extending_incompatible_typeclasses() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                property: F -> Bool
            }

            typeclass B: Bar {
                property: B -> Bool
            }
        "#,
    );
    // Should fail because Foo and Bar are incompatible.
    env.bad(
        r#"
            typeclass Q: Qux extends Foo, Bar {
            }
        "#,
    );
}

#[test]
fn test_env_allow_diamonds() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                property: F -> Bool
            }

            typeclass B: Bar extends Foo{
                bar_property: B -> Bool
            }

            typeclass Q: Qux extends Foo {
                qux_property: Q -> Bool
            }

            typeclass Z: Zap extends Bar, Qux {
            }
        "#,
    );
}

#[test]
fn test_env_typeclass_with_numeral_attributes() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                0: F
            }

            typeclass B: Bar extends Foo{
                bar_property: B -> Bool
            }

            theorem goal<B: Bar>(b: B) {
                B.0 = Foo.0<B>
            }
        "#,
    );
}

#[test]
fn test_env_numerals_in_typeclasses() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                0: F
            }

            inductive Bar {
                bar
            }

            instance Bar: Foo {
                let 0: Bar = Bar.bar
            }
        "#,
    );
}

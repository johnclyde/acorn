#[cfg(test)]
mod prover_test {
    use core::panic;
    use std::collections::HashSet;

    use acorn::code_gen_error::CodeGenError;
    use acorn::module::LoadState;
    use acorn::project::Project;
    use acorn::prover::{Outcome, Prover};

    // Tries to prove one thing from the project.
    // If the proof is successful, try to generate the code.
    fn prove(
        project: &mut Project,
        module_name: &str,
        goal_name: &str,
    ) -> (Prover, Outcome, Result<Vec<String>, CodeGenError>) {
        let module_id = project
            .load_module_by_name(module_name)
            .expect("load failed");
        let load_state = project.get_module_by_id(module_id);
        let env = match load_state {
            LoadState::Ok(env) => env,
            LoadState::Error(e) => panic!("module loading error: {}", e),
            _ => panic!("no module"),
        };
        let node = env.get_node_by_description(goal_name);
        let facts = node.usable_facts(project);
        let goal_context = node.goal_context().unwrap();
        let mut prover = Prover::new(&project, false);
        for fact in facts {
            prover.add_fact(fact);
        }
        prover.set_goal(&goal_context);
        prover.verbose = true;
        let outcome = prover.quick_search();
        if let Outcome::Error(s) = outcome {
            panic!("prover error: {}", s);
        }
        let code = match prover.get_and_print_proof() {
            Some(proof) => proof.to_code(&env.bindings),
            None => Err(CodeGenError::NoProof),
        };
        (prover, outcome, code)
    }

    fn prove_as_main(
        text: &str,
        goal_name: &str,
    ) -> (Prover, Outcome, Result<Vec<String>, CodeGenError>) {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", text);
        prove(&mut project, "main", goal_name)
    }

    // Does one proof on the provided text.
    fn prove_text(text: &str, goal_name: &str) -> Outcome {
        prove_as_main(text, goal_name).1
    }

    // Verifies all the goals in the provided text, returning any non-Success outcome.
    fn verify(text: &str) -> Outcome {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", text);
        let module_id = project.load_module_by_name("main").expect("load failed");
        let env = match project.get_module_by_id(module_id) {
            LoadState::Ok(env) => env,
            LoadState::Error(e) => panic!("error: {}", e),
            _ => panic!("no module"),
        };
        for node in env.iter_goals() {
            let facts = node.usable_facts(&project);
            let goal_context = node.goal_context().unwrap();
            println!("proving: {}", goal_context.description);
            let mut prover = Prover::new(&project, false);
            for fact in facts {
                prover.add_fact(fact);
            }
            prover.set_goal(&goal_context);
            prover.verbose = true;
            // This is a key difference between our verification tests, and our real verification.
            // This helps us test that verification fails in cases where we do have an
            // infinite rabbit hole we could go down.
            let outcome = prover.quick_shallow_search();
            if let Outcome::Error(s) = &outcome {
                println!("prover error: {}", s);
            }
            if outcome != Outcome::Success {
                return outcome;
            }
        }
        Outcome::Success
    }

    fn verify_succeeds(text: &str) {
        let outcome = verify(text);
        if outcome != Outcome::Success {
            panic!(
                "We expected verification to return Success, but we got {}.",
                outcome
            );
        }
    }

    fn verify_fails(text: &str) {
        let outcome = verify(text);
        if outcome != Outcome::Exhausted {
            panic!(
                "We expected verification to return Exhausted, but we got {}.",
                outcome
            );
        }
    }

    fn expect_proof(text: &str, goal_name: &str, expected: &[&str]) {
        let (_, outcome, code) = prove_as_main(text, goal_name);
        assert_eq!(outcome, Outcome::Success);
        let actual = code.expect("code generation failed");
        assert_eq!(actual, expected);
    }

    // Expects the prover to find a proof that's one of the provided ones.
    fn expect_proof_in(text: &str, goal_name: &str, expected: &[&[&str]]) {
        let (_, outcome, code) = prove_as_main(text, goal_name);
        assert_eq!(outcome, Outcome::Success);
        let actual = code.expect("code generation failed");

        // There's multiple things it could be that would be fine.
        for e in expected {
            if actual == *e {
                return;
            }
        }

        println!("unexpected code:");
        for line in &actual {
            println!("{}", line);
        }
        panic!("as vec: {:?}", actual);
    }

    // Expects the prover to find a proof but then fail to generate code.
    // fn expect_code_gen_error(text: &str, goal_name: &str, expected: &str) {
    //     let (outcome, code) = prove_as_main(text, goal_name);
    //     assert_eq!(outcome, Outcome::Success);
    //     assert_eq!(code.unwrap_err().error_type(), expected);
    // }

    const THING: &str = r#"
    type Thing: axiom
    let t: Thing = axiom
    let t2: Thing = axiom
    let f: Thing -> Bool = axiom
    let g: (Thing, Thing) -> Thing = axiom
    let h: Thing -> Thing = axiom
    "#;

    // Does one proof in the "thing" environment.
    fn prove_thing(text: &str, goal_name: &str) -> Outcome {
        let text = format!("{}\n{}", THING, text);
        prove_text(&text, goal_name)
    }

    #[test]
    fn test_specialization() {
        let text = r#"
            axiom f_all(x: Thing) { f(x) }
            theorem goal { f(t) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_backward_specialization_fails() {
        let text = r#"
            axiom f_one { f(t) }
            theorem goal(x: Thing) { f(x) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_axiomatic_values_distinct() {
        let text = "theorem goal { t = t2 }";
        assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_finds_example() {
        let text = r#"
            axiom f_one { f(t) }
            theorem goal { exists(x: Thing) { f(x) } }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_finds_negative_example() {
        let text = r#"
            axiom not_f(x: Thing) { not f(x) }
            theorem goal { not f(t) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_extends_equality() {
        let text = r#"
            axiom t_eq_t2 { t = t2 }
            theorem goal { f(t) = f(t2)  }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_composition() {
        let text = r#"
            axiom g_id(x: Thing) { g(x, x) = x }
            axiom f_t { f(t) }
            theorem goal { f(g(t, t)) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    // #[test]
    // fn test_composition_can_fail() {
    //     let text = r#"
    //         axiom f_t: f(t)
    //         axiom g_id(x: Thing): g(x, x) = x
    //         theorem goal { f(g(t, t2)) }
    //         "#;
    //     assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
    // }

    #[test]
    fn test_negative_rewriting() {
        let text = r#"
            axiom not_f_t { not f(t) }
            axiom g_id(x: Thing) { g(x, x) = x }
            theorem goal { not f(g(t, t)) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_extends_ne() {
        let text = r#"
            axiom f_t_ne_f_t2 { f(t) != f(t2) }
            theorem goal { t != t2 }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_equality_resolution() {
        let text = r#"
            axiom foo(x: Thing) { x != t or f(t) }
            theorem goal { f(t) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_equality_factoring() {
        let text = r#"
            axiom foo(x: Thing, y: Thing) { x = t or y = t }
            theorem goal(x: Thing) { x = t2 }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_existence_of_nonequality() {
        // After normalization, this is the same problem as the equality
        // factoring test above. So if one of them works and one doesn't,
        // it's likely to be a prioritization dependency problem.
        let text = r#"
            axiom foo { exists(x: Thing) { x != t2 } }
            theorem goal { exists(x: Thing) { x != t } }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_prover_avoids_loops() {
        let text = r#"
            axiom trivial(x: Thing) { not f(h(x)) or f(h(x)) }
            axiom arbitrary(x: Thing) { f(h(x)) or f(x) }
            theorem goal { f(t) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_synthesis_avoids_loops() {
        let text = r#"
            axiom foo(x: Thing -> Bool) { x(t) or f(h(t)) }
            theorem goal { f(t2) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_higher_order_unification() {
        let text = r#"
            axiom foo(x: Thing -> Bool) { x(t) }
            theorem goal { f(t) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_proof_inside_theorem_block() {
        let text = r#"
            type Thing: axiom
            let t: Thing = axiom
            theorem reflexivity(x: Thing) {
                x = x
            } by {
                reflexivity(t)
            }
            "#;

        expect_proof(text, "reflexivity(t)", &[]);
    }

    #[test]
    fn test_proof_inside_forall_block() {
        let text = r#"
            type Thing: axiom
            let t: Thing = axiom
            let foo: Thing -> Bool = axiom
            axiom foo_t { foo(t) }
            forall(x: Thing) {
                x = t -> foo(x)
            }
            "#;

        expect_proof(text, "x = t -> foo(x)", &[]);
    }

    #[test]
    fn test_proof_inside_if_block() {
        let text = r#"
            type Thing: axiom
            forall(x: Thing, y: Thing) {
                if x = y {
                    x = y
                }
            }
            "#;
        expect_proof(text, "x = y", &[]);
    }

    #[test]
    fn test_extracting_narrow_proof() {
        let text = r#"
            let b: Bool = axiom
            let f1: Bool -> Bool = axiom
            let f2: Bool -> Bool = axiom
            let f3: Bool -> Bool = axiom
            let f4: Bool -> Bool = axiom
            axiom a1 { f1(b) }
            axiom a12(x: Bool) { f1(x) -> f2(x) }
            axiom a23(x: Bool) { f2(x) -> f3(x) }
            axiom a34(x: Bool) { f3(x) -> f4(x) }
            theorem goal(x: Bool) { f4(b) }
        "#;
        expect_proof(text, "goal", &["f2(b)", "f3(b)"]);
    }

    #[test]
    fn test_rewriting_confluence_indirectly() {
        // The facts given by "axiom recursion_base" and "define add" are
        // each rewrite rules.
        // To prove add_zero_right, the naive way applies one backward and one
        // forward rewrite.
        // We need to be able to handle this somehow.
        let text = r#"
            type Nat: axiom
            let zero: Nat = axiom
            let suc: Nat -> Nat = axiom
            define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat { axiom }
            axiom recursion_base(f: Nat -> Nat, a: Nat) { recursion(f, a, zero) = a }
            define add(a: Nat, b: Nat) -> Nat { recursion(suc, a, b) }
            theorem add_zero_right(a: Nat) { add(a, zero) = a }
        "#;

        let expected = &[&[][..], &["recursion(suc, a, zero) = a"][..]];
        expect_proof_in(text, "add_zero_right", expected);
    }

    #[test]
    fn test_second_literal_matches_goal() {
        let text = r#"
            axiom axiom1 { f(g(t, t)) or f(t2) }
            axiom axiom2 { not f(g(t, t)) or f(t2) }
            theorem goal { f(t2) }
        "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_closure_proof() {
        let text = r#"
            type Nat: axiom
            let addx: (Nat, Nat) -> Nat = axiom
            define adder(a: Nat) -> (Nat -> Nat) { function(b: Nat) { addx(a, b) } }
            theorem goal(a: Nat, b: Nat) { addx(a, b) = adder(a)(b) }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_boolean_equality() {
        let text = r#"
            type Nat: axiom
            let addx: (Nat, Nat) -> Nat = axiom
            define ltex(a: Nat, b: Nat) -> Bool { exists(c: Nat) { addx(a, c) = b } }
            define ltx(a: Nat, b: Nat) -> Bool { ltex(a, b) and a != b }
            theorem goal(a: Nat) { not ltx(a, a) }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_using_conditional_existence_theorem() {
        let text = r#"
            type Nat: axiom
            let zero: Nat = axiom
            let one: Nat = axiom
            let suc: Nat -> Nat = axiom
            axiom zero_or_suc(a: Nat) { a = zero or exists(b: Nat) { a = suc(b) } }
            axiom one_neq_zero { one != zero }
            theorem goal { exists(x: Nat) { one = suc(x) } }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_instance_of_conditional_existence_theorem() {
        let text = r#"
            type Nat: axiom
            let zero: Nat = axiom
            let suc: Nat -> Nat = axiom
            let y: Nat = axiom
            axiom zero_or_suc(a: Nat) { a = zero or exists(b: Nat) { a = suc(b) } }
            theorem goal { y = zero or exists(b: Nat) { y = suc(b) } }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_another_instance_of_conditional_existence_theorem() {
        let text = r#"
            type Nat: axiom
            let zero: Nat = axiom
            let suc: Nat -> Nat = axiom
            let y: Nat = axiom
            axiom zero_or_suc(a: Nat) { a = zero or exists(b: Nat) { a = suc(b) } }
            axiom y_not_zero { y != zero }
            theorem goal { y = zero or exists(b: Nat) { y = suc(b) } }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_structure_new_equation() {
        let text = r#"
            structure Pair {
                first: Bool
                second: Bool
            }
            theorem goal(p: Pair) { p = Pair.new(Pair.first(p), Pair.second(p)) }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_structure_first_member_equation() {
        let text = r#"
            structure Pair {
                first: Bool
                second: Bool
            }
            theorem goal(a: Bool, b: Bool) { Pair.first(Pair.new(a, b)) = a }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_structure_second_member_equation() {
        let text = r#"
            structure Pair {
                first: Bool
                second: Bool
            }
            theorem goal(a: Bool, b: Bool) { Pair.second(Pair.new(a, b)) = b }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_inductive_no_confusion_property() {
        let text = r#"
            inductive Nat {
                zero
                suc(Nat)
            }
            theorem goal(a: Nat) { Nat.suc(a) != Nat.zero }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_inductive_canonical_form_principle() {
        let text = r#"
            inductive Nat {
                zero
                suc(Nat)
            }
            theorem goal(a: Nat) { a = Nat.zero or exists(b: Nat) { a = Nat.suc(b) } }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_inductive_constructors_injective() {
        let text = r#"
            inductive Nat {
                zero
                suc(Nat)
            }
            theorem goal(a: Nat, b: Nat) { Nat.suc(a) = Nat.suc(b) -> a = b }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_prover_gets_structural_induction() {
        let text = r#"
            inductive Nat {
                zero
                suc(Nat)
            }
            let f: Nat -> Bool = axiom
            axiom base {
                f(Nat.zero)
            }
            axiom step(k: Nat) {
                f(k) -> f(k.suc)
            }
            theorem goal(n: Nat) {
                f(n)
            }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_proving_parametric_theorem_basic() {
        let text = r#"
            theorem goal<T>(a: T, b: T, c: T) {
                a = b and b = c -> a = c
            } by {
                if (a = b and b = c) {
                    a = c
                }
            }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_proving_parametric_theorem_no_block() {
        let text = r#"
            theorem goal<T>(a: T, b: T, c: T) { a = b and b = c -> a = c }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_citing_parametric_theorem() {
        verify_succeeds(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            theorem foo<T>(a: T) { a = a }
            theorem goal { foo(zero) }
        "#,
        );
    }

    #[test]
    fn test_applying_parametric_function() {
        let text = r#"
            type Nat: axiom
            define foo<T>(a: T) -> Bool { (a = a) }
            let zero: Nat = axiom
            theorem goal { foo(zero) }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_parametric_definition_and_theorem() {
        let text = r#"
            define foo<T>(a: T) -> Bool { axiom }
            axiom foo_true<T>(a: T) { foo(a) }
            type Nat: axiom
            let zero: Nat = axiom
            theorem goal { foo(zero) }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_parameter_name_can_change() {
        let text = r#"
            define foo<T>(a: T) -> Bool { axiom }
            axiom foo_true<U>(a: U) { foo(a) }
            type Nat: axiom
            let zero: Nat = axiom
            theorem goal { foo(zero) }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_finding_inconsistency() {
        let text = r#"
            type Nat: axiom
            let zero: Nat = axiom
            let foo: Nat -> Bool = axiom
            let bar: Nat -> Bool = axiom
            axiom foo_true { foo(zero) }
            axiom foo_false { not foo(zero) }
            theorem goal { bar(zero) }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Inconsistent);
    }

    #[test]
    fn test_using_true_and_false_in_a_proof() {
        let text = r#"
        theorem goal(b: Bool) { b = true or b = false }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_finding_mildly_nontrivial_inconsistency() {
        let text = r#"
            axiom bad { true = false }
            let b: Bool = axiom
            theorem goal { b }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Inconsistent);
    }

    #[test]
    fn test_proving_explicit_false_okay() {
        verify_succeeds(
            r#"
            let b: Bool = axiom
            if b != b {
                false
            }
        "#,
        );
    }

    #[test]
    fn test_subsequent_explicit_false_ok() {
        verify_succeeds(
            r#"
            let b: Bool = axiom
            if b != b {
                b or not b
                false
            }
        "#,
        );
    }

    #[test]
    fn test_explicit_false_mandatory() {
        let text = r#"
            let b: Bool = axiom
            let c: Bool = axiom
            if b != b {
                c
            }
        "#;
        assert_eq!(verify(text), Outcome::Inconsistent);
    }

    #[test]
    fn test_verify_if_else_function() {
        verify_succeeds(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            let one: Nat = axiom
            define sign(a: Nat) -> Nat {
                if a = zero {
                    zero
                } else {
                    one
                }
            }
            theorem goal(a: Nat) {
                sign(a) = zero or sign(a) = one
            }
        "#,
        );
    }

    #[test]
    fn test_verify_complicated_theorem_application() {
        verify_succeeds(
            r#"
            type Nat: axiom
            let a: Nat = axiom
            let b: Nat = axiom
            let c: Nat = axiom
            let f: (Nat, Nat) -> Bool = axiom
            axiom trans(x: Nat, y: Nat, z: Nat) {
                f(x, y) and f(y, z) -> f(x, z)
            }
            axiom fab { f(a, b) }
            axiom fbc { f(b, c) }
            theorem goal {
                f(a, c)
            }
            "#,
        );
    }

    #[test]
    fn test_verify_existence_theorem() {
        verify_succeeds(
            r#"
            type Nat: axiom
            let a: Nat = axiom
            let f: Nat -> Bool = axiom
            let g: (Nat, Nat) -> Bool = axiom
            axiom foo(x: Nat) {
                f(x) -> exists(y: Nat) { g(x, y) and g(y, x) }
            }
            theorem goal {
                f(a) -> exists(y: Nat) { g(a, y) and g(y, a) }
            }
            "#,
        );
    }

    #[test]
    fn test_rewrite_consistency() {
        // In practice this caught an inconsistency that came from bad rewrite logic.
        verify_succeeds(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            let suc: Nat -> Nat = axiom
            let addx: (Nat, Nat) -> Nat = axiom
            let mulx: (Nat, Nat) -> Nat = axiom
            axiom add_suc(a: Nat, b: Nat) { addx(suc(a), b) = suc(addx(a, b)) }
            axiom suc_ne(a: Nat) { suc(a) != a }
            axiom mul_suc(a: Nat, b: Nat) { addx(a, mulx(a, b)) = mulx(a, suc(b)) }
            theorem goal(a: Nat) { suc(a) != a }
        "#,
        );
    }

    #[test]
    fn test_normalization_failure_doesnt_crash() {
        // We can't normalize lambdas inside function calls, but we shouldn't crash on them.
        verify(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            define apply(f: Nat -> Nat, a: Nat) -> Nat { f(a) }
            theorem goal { apply(function(x: Nat) { x }, zero) = zero }
        "#,
        );
    }

    #[test]
    fn test_functional_equality_definition() {
        verify_succeeds(
            r#"
            type Nat: axiom
            let f: Nat -> Nat = axiom
            let g: Nat -> Nat = axiom
            theorem goal { forall(x: Nat) { f(x) = g(x) } -> f = g }
        "#,
        );
    }

    #[test]
    fn test_verify_functional_definition() {
        verify_succeeds(
            r#"
            type Nat: axiom
            define is_min(f: Nat -> Bool) -> (Nat -> Bool) { axiom }
            define gcd_term(p: Nat) -> (Nat -> Bool) { axiom }
            let p: Nat = axiom
            let f: Nat -> Bool = is_min(gcd_term(p))

            theorem goal { is_min(gcd_term(p)) = f }
        "#,
        );
    }

    #[test]
    fn test_functional_substitution() {
        verify_succeeds(
            r#"
            type Nat: axiom
            define find(f: Nat -> Bool) -> Nat { axiom }
            define is_min(f: Nat -> Bool) -> (Nat -> Bool) { axiom }
            define gcd_term(p: Nat) -> (Nat -> Bool) { axiom }
            let p: Nat = axiom
            let f: Nat -> Bool = is_min(gcd_term(p))
            theorem goal { find(is_min(gcd_term(p))) = find(f) }
        "#,
        );
    }

    #[test]
    fn test_proving_with_partial_application() {
        verify_succeeds(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            let addx: (Nat, Nat) -> Nat = axiom
            theorem goal(f: Nat -> Nat) { f = addx(zero) -> f(zero) = addx(zero, zero) }
        "#,
        );
    }

    #[test]
    fn test_using_imported_axiom() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/bar.ac",
            r#"
            type Bar: axiom
            let bar: Bar = axiom
            let morph: Bar -> Bar = axiom
            axiom meq(b: Bar) { morph(b) = morph(bar) }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import bar
            theorem goal(a: bar.Bar, b: bar.Bar) { bar.morph(a) = bar.morph(b) }
        "#,
        );
        let (_, outcome, _) = prove(&mut p, "main", "goal");
        assert_eq!(outcome, Outcome::Success);
    }

    #[test]
    fn test_backward_nonbranching_reasoning() {
        verify_succeeds(
            r#"
            type Nat: axiom
            let suc: Nat -> Nat = axiom
            axiom suc_injective(x: Nat, y: Nat) { suc(x) = suc(y) -> x = y }
            let n: Nat = axiom
            axiom hyp { suc(n) != n }
            theorem goal { suc(suc(n)) != suc(n) }
        "#,
        )
    }

    #[test]
    fn test_basic_unification() {
        verify_succeeds(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            let f: (Nat, Nat) -> Bool = axiom
            axiom f_zero_right(x: Nat) { f(x, zero) }
            theorem goal { exists(x: Nat) { f(zero, x) } }
        "#,
        );
    }

    #[test]
    fn test_indirect_proof_collapses() {
        let text = r#"
            let a: Bool = axiom
            let b: Bool = axiom
            axiom bimpa { b -> a }
            axiom bimpna { b -> not a }
            theorem goal { not b }
        "#;
        expect_proof(text, "goal", &[]);
    }

    #[test]
    fn test_proof_generation_with_forall_goal() {
        let text = r#"
            type Nat: axiom
            let f: Nat -> Bool = axiom
            let g: Nat -> Bool = axiom
            let h: Nat -> Bool = axiom
            axiom fimpg { forall(x: Nat) { f(x) -> g(x) } }
            axiom gimph { forall(x: Nat) { g(x) -> h(x) } }
            theorem goal { forall(x: Nat) { f(x) -> h(x) } }
        "#;
        expect_proof(text, "goal", &[]);
    }

    #[test]
    fn test_proof_generation_with_intermediate_skolem() {
        let text = r#"
        type Nat: axiom
        let b: Bool = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        axiom forg(x: Nat) { f(x) or g(x) }
        axiom fgimpb { forall(x: Nat) { f(x) or g(x) } -> b }
        theorem goal { b }
        "#;
        expect_proof(text, "goal", &[]);
    }

    #[test]
    fn test_assuming_lhs_of_implication() {
        verify_succeeds(
            r#"
            let a: Bool = axiom
            let b: Bool = axiom
            let c: Bool = axiom
            axiom aimpb { a -> b }
            axiom bimpc { b -> c }
            theorem goal { a -> c } by {
                b
            }
        "#,
        );
    }

    #[test]
    fn test_templated_proof() {
        let text = r#"
            type Thing: axiom
            let t1: Thing = axiom
            let t2: Thing = axiom
            let t3: Thing = axiom
            
            define foo<T>(x: T) -> Bool { axiom }

            axiom a12 { foo(t1) -> foo(t2) }
            axiom a23 { foo(t2) -> foo(t3) }
            theorem goal { foo(t1) -> foo(t3) }
            "#;

        expect_proof(text, "goal", &[]);
    }

    #[test]
    fn test_proof_using_else() {
        let text = r#"
        let a: Bool = axiom
        let b: Bool = axiom
        let c: Bool = axiom
        if a {
            b
        } else {
            c
        }
        theorem goal { not a -> c }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_using_else_when_missing_if_block() {
        let text = r#"
        let a: Bool = axiom
        let b: Bool = axiom
        if a {
        } else {
            b
        }
        theorem goal { not a -> b }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_proof_condensing_induction() {
        let text = r#"
        type Nat: axiom
        let zero: Nat = axiom
        let suc: Nat -> Nat = axiom
        axiom induction(f: Nat -> Bool) {
            f(zero) and forall(k: Nat) { f(k) -> f(suc(k)) } -> forall(n: Nat) { f(n) }
        }
        let foo: Nat -> Bool = axiom
        theorem goal { foo(zero) and forall(k: Nat) { foo(k) -> foo(suc(k)) } -> forall(n: Nat) { foo(n) } }
        "#;
        expect_proof(text, "goal", &[]);
    }

    #[test]
    fn test_proof_condensing_false() {
        let text = r#"
        let a: Bool = axiom
        axiom a_true { a }
        if not a {
            false
        }
        "#;
        expect_proof(text, "false", &[]);
    }

    #[test]
    fn test_proof_condensing_combining_two_theorems() {
        let text = r#"
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        axiom fimpg(x: Nat) { f(x) -> g(x) }
        axiom fa { f(a) }
        theorem goal { g(a) }
        "#;
        expect_proof(text, "goal", &[]);
    }

    #[test]
    fn test_proof_indirect_from_goal() {
        let text = r#"
            type Nat: axiom
            let f: Nat -> Bool = axiom
            let g: Nat -> Bool = axiom
            let h: Nat -> Bool = axiom
            axiom fimpg(x: Nat) { f(x) -> g(x) }
            axiom gimph(x: Nat) { g(x) -> h(x) }
            axiom fimpnh(x: Nat) { f(x) -> not h(x) }
            theorem goal(x: Nat) { not f(x) }
        "#;

        let expected = &[
            &["if f(x) {", "\tg(x)", "\tfalse", "}"][..],
            &["if f(x) {", "\tnot h(x)", "\tfalse", "}"][..],
        ];
        expect_proof_in(text, "goal", expected);
    }

    #[test]
    fn test_nested_if_else() {
        let text = r#"
        let a: Bool = axiom
        let b: Bool = axiom
        let c: Bool = axiom
        if a {
            if b {
                c
            } else {
                c
            }
        }
        theorem goal { a -> c }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_infix_addition_goes_left_to_right() {
        let text = r#"
        type Nat: axiom
        class Nat {
            define add(self, other: Nat) -> Nat { axiom }
        }
        theorem goal(a: Nat, b: Nat, c: Nat) { Nat.add(Nat.add(a, b), c) = a + b + c }
        theorem antigoal(a: Nat, b: Nat, c: Nat) { Nat.add(a, Nat.add(b, c)) = a + b + c }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
        assert_eq!(prove_text(text, "antigoal"), Outcome::Exhausted);
    }

    #[test]
    fn test_infix_mul_before_plus() {
        let text = r#"
        type Nat: axiom
        class Nat {
            define add(self, other: Nat) -> Nat { axiom }
            define mul(self, other: Nat) -> Nat { axiom }
        }
        theorem goal1(a: Nat, b: Nat, c: Nat) { Nat.add(Nat.mul(a, b), c) = a * b + c }
        theorem goal2(a: Nat, b: Nat, c: Nat) { Nat.add(a, Nat.mul(b, c)) = a + b * c }
        "#;
        assert_eq!(prove_text(text, "goal1"), Outcome::Success);
        assert_eq!(prove_text(text, "goal2"), Outcome::Success);
    }

    #[test]
    fn test_ways_to_call_methods() {
        let text = r#"
        type Nat: axiom
        class Nat {
            define suc(self) -> Nat { axiom }
            define add(self, other: Nat) -> Nat { axiom }
        }
        theorem goal1(a: Nat) { a.suc.suc = Nat.suc(Nat.suc(a)) }
        theorem goal2(a: Nat) { a.suc.suc = Nat.suc(a).suc }
        theorem goal3(a: Nat, b: Nat) { (a + b).suc = Nat.suc(Nat.add(a, b)) }
        "#;
        assert_eq!(prove_text(text, "goal1"), Outcome::Success);
        assert_eq!(prove_text(text, "goal2"), Outcome::Success);
        assert_eq!(prove_text(text, "goal3"), Outcome::Success);
    }

    #[test]
    fn test_bag_of_digits() {
        let text = r#"
        type Bag: axiom
        class Bag {
            let 1: Bag = axiom
            let 2: Bag = axiom
            define read(self, other: Bag) -> Bag { axiom }
        }
        numerals Bag
        axiom comm(a: Bag, b: Bag) { a.read(b) = b.read(a) }
        theorem goal { 12 = 21 }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_verify_function_satisfy() {
        let text = r#"
        type Nat: axiom
        let zero: Nat = axiom
        let one: Nat = axiom
        axiom zero_neq_one { zero != one }
        let flip(a: Nat) -> b: Nat satisfy {
            a != b
        }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_no_verify_boolean_soup() {
        // This goal is not provable.
        // I'm not sure what ever went wrong, it's a mess of nested boolean formulas.
        let text = r#"
        theorem goal(a: Bool, b: Bool, c: Bool) {
            a = b or a = not c
        }
        "#;
        verify_fails(text);
    }

    #[test]
    fn test_resolution_trap() {
        // This is a trap for the resolution algorithm, because repeated resolution
        // against the negated goal will give longer and longer formulas.
        let text = r#"
        type Nat: axiom
        let f: Nat -> Nat = axiom
        let g: Nat -> Bool = axiom
        let a: Nat = axiom
        axiom ga { g(a) }
        theorem goal {
            not forall(x: Nat) { g(x) -> g(f(x)) }
        }
        "#;
        verify_fails(text);
    }

    #[test]
    fn test_verify_if_else_theorem() {
        let text = r#"
        type Nat: axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        axiom fgh(a: Nat) {
            if f(a) {
                g(a)
            } else {
                h(a)
            }
        }
        theorem goal(a: Nat) {
            g(a) or h(a)
        }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_verify_function_satisfy_with_if_else() {
        let text = r#"
        type Nat: axiom
        let suc: Nat -> Nat = axiom
        let zero: Nat = axiom
        axiom base(a: Nat) {
            a = zero or exists(b: Nat) { a = suc(b) }
        }
        let pred(a: Nat) -> b: Nat satisfy {
            if a = zero {
                b = zero
            } else {
                suc(b) = a
            }
        } by {
            if a != zero {
                exists(b: Nat) { a = suc(b) }
            }
        }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_verify_or_contraction() {
        let text = r#"
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        define some(x: Nat) -> Bool { f(x) or g(x) or h(x) }
        axiom somea { f(a) or g(a) or h(a) }
        theorem goal { some(a) }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_verify_fimp_expansion() {
        let text = r#"
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        define fimp(x: Nat) -> Bool { f(x) -> (g(x) and h(x)) }
        axiom fimpa { fimp(a) }
        theorem goal { f(a) -> (g(a) and h(a)) }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_verify_fimp_contraction() {
        let text = r#"
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        define fimp(x: Nat) -> Bool { f(x) -> (g(x) and h(x)) }
        axiom fimpa { f(a) -> (g(a) and h(a)) }
        theorem goal { fimp(a) }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_definition_trap() {
        // This will infinite loop if you allow free resolutions against definition.
        let text = r#"
        type Nat: axiom
        let z: Nat = axiom
        let f: Nat -> Bool = axiom
        let suc: Nat -> Nat = axiom
        define decr(x: Nat) -> Bool { f(x) and not f(suc(x))}
        axiom fz { f(z) }
        theorem goal { exists(x: Nat) { decr(x) } }
        "#;
        verify_fails(text);
    }

    #[test]
    fn test_verify_functional_existence() {
        // There are two tricky things about this resolution.
        // In one of the directions, you have to resolve x0(x1) against foo(a, b).
        // In the other direction, in the final literal-literal resolution, both sides
        // still have a free variable. So we don't find it via simplification.
        // Nevertheless, intuitively it is just one step.
        let text = r#"
        type Nat: axiom
        let is_min: (Nat -> Bool, Nat) -> Bool = axiom
        let foo: Nat -> (Nat -> Bool) = axiom
        axiom has_min(f: Nat -> Bool, n: Nat) {
            f(n) -> exists(m: Nat) { is_min(f, m) }
        }
        axiom foo_is_true_somewhere(a: Nat) {
            exists(b: Nat) { foo(a, b) }
        }
        let min_foo(a: Nat) -> b: Nat satisfy {
            is_min(foo(a), b)
        }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_verify_free_simplification_trap() {
        // This will infinite loop if you let a 3-to-2 resolution plus a 2-to-1 simplification
        // be zero depth.
        let text = r#"
        type Nat: axiom
        let foo: Nat -> Nat = axiom
        let bar: Nat -> Bool = axiom
        let zap: Nat -> Bool = axiom
        axiom expander(x: Nat) {
            not zap(x) or not bar(x) or zap(foo(x))
        }
        axiom simplifier(x: Nat) {
            bar(foo(x))
        }
        theorem goal(a: Nat) {
            not zap(foo(a))
        }
        "#;
        verify_fails(text);
    }

    #[test]
    fn test_verify_rewrite_trap() {
        // This will infinite loop if you allow complexifying rewrites.
        let text = r#"
        type Nat: axiom
        let f: (Nat, Nat) -> Nat = axiom
        let g: Nat -> Bool = axiom
        axiom fxx(x: Nat) { f(x, x) = x }
        theorem goal(a: Nat) { g(a) }
        "#;
        verify_fails(text);
    }

    #[test]
    fn test_prove_with_imported_skolem() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/foo.ac",
            r#"
            type Nat: axiom

            let f: Nat -> Bool = axiom

            axiom exists_a_fa {
                exists(a: Nat) { f(a) }
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from foo import Nat, f

            theorem goal {
                exists(a: Nat) { f(a) }
            }
        "#,
        );
        let (_, outcome, _) = prove(&mut p, "main", "goal");
        assert_eq!(outcome, Outcome::Success);
    }

    #[test]
    fn test_prove_with_match_in_define() {
        let text = r#"
        inductive Foo {
            bar
            baz
        }
        define foo(f: Foo) -> Bool {
            match f {
                Foo.bar {
                    true
                }
                Foo.baz {
                    true
                }
            }
        }
        theorem goal(f: Foo) {
            foo(f)
        }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_prove_with_match_in_let() {
        let text = r#"
        inductive Foo {
            bar
            baz
        }
        let foo: Bool = match Foo.bar {
            Foo.bar {
                true
            }
            Foo.baz {
                false
            }
        }
        theorem goal {
            foo
        }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_prove_with_match_statement() {
        // An example found when migrating pre-match code.
        let text = r#"
        type Nat: axiom
        class Nat {
            define suc(self) -> Nat { axiom }
        }

        inductive Int {
            from_nat(Nat)
            neg_suc(Nat)
        }
        
        define abs_case_1(a: Int, n: Nat) -> Bool {
            a = Int.from_nat(n)
        }
        
        define abs_case_2(a: Int, n: Nat) -> Bool {
            exists(k: Nat) {
                a = Int.neg_suc(k) and n = k.suc
            }
        }
        
        define abs(a: Int) -> Nat {
            match a {
                Int.from_nat(n) {
                    n
                }
                Int.neg_suc(k) {
                    k.suc
                }
            }
        }
        
        theorem goal(a: Int) {
            abs_case_1(a, abs(a)) or abs_case_2(a, abs(a))
        } by {
            match a {
                Int.from_nat(n) {
                    abs_case_1(a, abs(a))
                }
                Int.neg_suc(k) {
                    abs_case_2(a, abs(a))
                }
            }
        }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_prove_with_recursive_function() {
        let text = r#"
        inductive Nat {
            zero
            suc(Nat)
        }
        define repeat<T>(n: Nat, f: T -> T, a: T) -> T {
            match n {
                Nat.zero {
                    a
                }
                Nat.suc(pred) {
                    repeat(pred, f, f(a))
                }
            }
        }
        theorem goal(n: Nat) {
            repeat(Nat.zero, Nat.suc, n) = n
        }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_prove_with_anonymous_axiom() {
        let text = r#"
        let b: Bool = axiom
        axiom foo {
            b
        }
        theorem goal {
            b
        }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_prove_easy_constraint() {
        let text = r#"
        structure Foo {
            first: Bool
            second: Bool
        } constraint {
            first or second
        }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_prove_impossible_constraint() {
        let text = r#"
        structure Foo {
            first: Bool
        } constraint {
            first and not first
        }
        "#;
        verify_fails(text);
    }

    #[test]
    fn test_prove_constraint_equation() {
        let text = r#"
        structure Foo {
            first: Bool
            second: Bool
        } constraint {
            first or second
        }
        theorem goal(f: Foo) {
            f.first or f.second
        }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_prove_constrained_member_equation() {
        let text = r#"
        type Foo: axiom
        let foo: Foo = axiom
        let foof: Foo -> Bool = axiom
        axiom {
            foof(foo)
        }

        structure Bar {
            f: Foo
        } constraint {
            foof(f)
        }
        theorem goal(f: Foo) {
            foof(f) -> Bar.new(f).f = f
        }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_prove_member_equation_requires_constraint() {
        // This shouldn't work, because maybe Bar.new(f) doesn't meet the constraint.
        let text = r#"
        type Foo: axiom
        let foo: Foo = axiom
        let foof: Foo -> Bool = axiom
        axiom {
            foof(foo)
        }

        structure Bar {
            f: Foo
        } constraint {
            foof(f)
        }
        theorem goal(f: Foo) {
            Bar.new(f).f = f
        }
        "#;
        verify_fails(text);
    }

    #[test]
    fn test_proving_boolean_equality() {
        let text = r#"
        let a: Bool = axiom
        let b: Bool = axiom
        axiom {
            a -> b
        }
        axiom {
            b -> a
        }
        theorem goal {
            a = b
        }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_proving_with_implies_keyword() {
        let text = r#"
        let a: Bool = axiom
        theorem {
            a implies a
        }
        theorem {
            not a implies not a
        }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_code_gen_not_losing_conclusion() {
        // Reproducing a bug found by Dan.
        // This confused the code generator because the final step of the proof
        // uses only a single source, so when you reverse it, it has no premise.
        // (It's using equality resolution to go from "x0 != constant" to a contradiction.)
        let text = r#"
            type Foo: axiom
            let zero: Foo = axiom
            let three: Foo = axiom
            let mul: (Foo, Foo) -> Foo = axiom

            define threeven(n: Foo) -> Bool {
                exists(d: Foo) {
                    mul(three, d) = n
                }
            }

            axiom mul_zero_right(a: Foo, b: Foo) {
                b = zero -> mul(a, b) = zero
            }

            theorem goal {
                threeven(zero)
            }
            "#;
        expect_proof(text, "goal", &["exists(k0: Foo) { zero = k0 }"]);
    }

    #[test]
    fn test_proving_identity_is_surjective() {
        // To prove this, the monomorphizer needs to instantiate the definitions of:
        // is_surjective<V, V>
        // identity<V>
        let text = r#"
            define is_surjective<T, U>(f: T -> U) -> Bool {
                forall(y: U) {
                    exists(x: T) {
                        f(x) = y
                    }
                }
            }

            define identity<T>(x: T) -> T {
                x
            }

            theorem identity_is_surjective<V> {
                is_surjective(identity<V>)
            }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_proving_with_generic_structure() {
        // Just testing that we can define something, then immediately prove the definition.
        let text = r#"
            structure Pair<T, U> {
                first: T
                second: U
            }

            class Pair<T, U> {
                define swap(self) -> Pair<U, T> {
                    Pair.new(self.second, self.first)
                }
            }

            theorem swap_def<T, U>(p: Pair<T, U>) {
                p.swap = Pair.new(p.second, p.first)
            }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_proving_with_generic_structure_definition() {
        // These theorems are direct implications of the structure definition.
        let text = r#"
            structure Pair<T, U> {
                first: T
                second: U
            }

            theorem check_first<T, U>(t: T, u: U) {
                Pair.new(t, u).first = t
            }

            theorem check_second<T, U>(t: T, u: U) {
                Pair.new(t, u).second = u
            }

            theorem check_new<T, U>(p: Pair<T, U>) {
                Pair.new(p.first, p.second) = p
            }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_prove_with_imported_generic_structure() {
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

            theorem check_first<T, U>(t: T, u: U) {
                Pair.new(t, u).first = t
            }

            theorem check_second<T, U>(t: T, u: U) {
                Pair.new(t, u).second = u
            }

            theorem check_new<T, U>(p: Pair<T, U>) {
                Pair.new(p.first, p.second) = p
            }
        "#,
        );
        let (_, outcome, _) = prove(&mut p, "main", "check_first");
        assert_eq!(outcome, Outcome::Success);
        let (_, outcome, _) = prove(&mut p, "main", "check_second");
        assert_eq!(outcome, Outcome::Success);
        let (_, outcome, _) = prove(&mut p, "main", "check_new");
        assert_eq!(outcome, Outcome::Success);
    }

    #[test]
    fn test_proving_with_instance_of_generic_structure() {
        let text = r#"
            structure Pair<T, U> {
                first: T
                second: U
            }

            type Foo: axiom

            theorem foo_pair_first(a: Foo, b: Foo) {
                Pair.new(a, b).first = a
            }

            theorem foo_pair_second(a: Foo, b: Foo) {
                Pair.new(a, b).second = b
            }

            theorem foo_pair_new(p: Pair<Foo, Foo>) {
                Pair.new(p.first, p.second) = p
            }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_proving_with_generic_constraint() {
        let text = r#"
            structure EqCheckedPair<T> {
                first: T
                second: T
                eq: Bool
            } constraint {
                eq implies first = second
            }

            type Foo: axiom

            theorem check_constraint(p: EqCheckedPair<Foo>) {
                p.eq implies p.first = p.second
            }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_useful_fact_extraction() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            type Foo: axiom
            let foo: Foo -> Bool = axiom
            let bar: Foo = axiom
            let baz: Foo = axiom
            axiom foo_bar {
                foo(bar)
            }
            axiom foo_bar_imp_foo_baz {
                foo(bar) implies foo(baz)
            }
            theorem goal {
               foo(baz)
            }
        "#,
        );
        let (prover, outcome, _) = prove(&mut p, "main", "goal");
        assert_eq!(outcome, Outcome::Success);
        let mut name_set = HashSet::new();
        prover.get_useful_source_names(&mut name_set);
        let mut names = name_set
            .into_iter()
            .map(|(_, name)| name)
            .collect::<Vec<_>>();
        names.sort();
        assert_eq!(names, &["foo_bar", "foo_bar_imp_foo_baz"]);
    }

    #[test]
    fn test_prover_handles_instance_let() {
        let text = r#"
            inductive Z1 {
                zero
            }

            typeclass T: TwoColored {
                is_red: T -> Bool
            }

            instance Z1: TwoColored {
                let is_red: Z1 -> Bool = function(z: Z1) {
                    true
                }
            }

            theorem goal {
                TwoColored.is_red(Z1.zero)
            }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_prover_handles_instance_define() {
        let text = r#"
            inductive Z1 {
                zero
            }

            typeclass T: TwoColored {
                is_red: T -> Bool
            }

            instance Z1: TwoColored {
                define is_red(self) -> Bool {
                    true
                }
            }

            theorem goal {
                TwoColored.is_red(Z1.zero)
            }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_prover_handles_parametrized_constants() {
        let text = r#"
            inductive Z1 {
                zero
            }

            typeclass S: Singleton {
                value: S

                unique(x: S) {
                    x = S.value
                }
            }

            instance Z1: Singleton {
                let value: Z1 = Z1.zero
            }

            theorem goal {
                Z1.zero = Singleton.value<Z1>
            }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_prover_fails_on_bad_instance() {
        let text = r#"
            inductive Z2 {
                zero
                one
            }

            typeclass S: Singleton {
                value: S

                unique(x: S) {
                    x = S.value
                }
            }

            instance Z2: Singleton {
                let value: Z2 = Z2.zero
            }
        "#;
        verify_fails(text);
    }

    #[test]
    fn test_prover_succeeds_on_good_instance() {
        let text = r#"
            inductive Z1 {
                zero
            }

            typeclass S: Singleton {
                value: S

                unique(x: S) {
                    x = S.value
                }
            }

            instance Z1: Singleton {
                let value: Z1 = Z1.zero
            }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_prover_respects_typeclasses() {
        // Singleton.unique should not be misapplied to Z2.
        let text = r#"
            inductive Z2 {
                zero
                one
            }

            define is_equal<T>(x: T, y: T) -> Bool {
                x = y
            }

            typeclass S: Singleton {
                element: S

                unique(x: S, y: S) {
                    is_equal(x, y)
                }
            }

            theorem goal {
                is_equal(Z2.zero, Z2.one)
            }
        "#;
        verify_fails(text);
    }

    #[test]
    fn test_prover_can_use_typeclass_theorems() {
        // These axioms should be combinable via the instance relationship.
        let text = r#"
            typeclass F: Foo {
                foo: F -> Bool
            }

            axiom always_foo<F: Foo>(x: F) {
                x.foo
            }

            inductive Bar {
                bar
            }

            let qux: Bool = axiom

            instance Bar: Foo {
                define foo(self) -> Bool {
                    qux
                }
            }

            theorem goal {
                qux
            } by {
                Foo.foo(Bar.bar)
            }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_normalizing_instance_aliases() {
        let text = r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            inductive Foo {
                foo
            }

            class Foo {
                define mul(self, other: Foo) -> Foo {
                    Foo.foo
                }
            }

            instance Foo: Magma {
                let mul: (Foo, Foo) -> Foo = Foo.mul
            }

            theorem goal(a: Foo) {
                Magma.mul(a, a) = a * a
            }
        "#;
        let (prover, outcome, _) = prove_as_main(text, "goal");
        assert_eq!(outcome, Outcome::Success);
        if let Some(final_step) = prover.get_final_step() {
            // TODO: the goal should have just normalized to Foo.mul(x0, x0) = Foo.mul(x0, x0)
            // i.e. a trivial one.
            if !final_step.rule.is_assumption() {
                panic!("final step is not trivial: {:?}", final_step);
            }
        } else {
            panic!("expected a final step");
        }
    }
}

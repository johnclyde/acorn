use std::path::PathBuf;

use crate::builder::{BuildStatus, Builder};
use crate::environment::LineType;
use crate::module::ModuleDescriptor;
use crate::project::Project;
use indoc::indoc;

const FOO_AC: &str = r#"
// Imported by other tests
type Foo: axiom
type AlsoFoo: Foo
type NotFoo: axiom
let foo: Foo = axiom
define fooify(x: Foo) -> Foo { foo }
"#;

#[test]
fn test_basic_import() {
    let mut p = Project::new_mock();
    p.mock("/mock/foo.ac", FOO_AC);
    p.mock("/mock/main.ac", "import foo");
    p.expect_ok("main");
}

#[test]
fn test_direct_import_nonexistent() {
    let mut p = Project::new_mock();
    p.expect_load_err("main");
}

#[test]
fn test_indirect_import_nonexistent() {
    let mut p = Project::new_mock();
    p.mock("/mock/main.ac", "import nonexistent");
    p.expect_module_err("main");
}

#[test]
fn test_nonexistent_property() {
    let mut p = Project::new_mock();
    p.mock("/mock/foo.ac", FOO_AC);
    p.mock(
        "/mock/main.ac",
        r#"
        import foo
        let bar: foo.nonexistent = axiom
    "#,
    );
    p.expect_module_err("main");
}

#[test]
fn test_circular_imports() {
    let mut p = Project::new_mock();
    p.mock("/mock/a.ac", "import b");
    p.mock("/mock/b.ac", "import c");
    p.mock("/mock/c.ac", "import a");
    p.expect_module_err("a");
    // The error should show up in c.ac, not in a.ac
    assert!(p.errors().len() > 0);
}

#[test]
fn test_self_import() {
    let mut p = Project::new_mock();
    p.mock("/mock/a.ac", "import a");
    p.expect_module_err("a");
}

#[test]
fn test_import_from_subdir() {
    let mut p = Project::new_mock();
    p.mock("/mock/stuff/foo.ac", FOO_AC);
    p.mock("/mock/main.ac", "import stuff.foo");
    p.expect_ok("main");
}

#[test]
fn test_good_imported_types() {
    let mut p = Project::new_mock();
    p.mock("/mock/foo.ac", FOO_AC);
    p.mock(
        "/mock/main.ac",
        r#"
        import foo
        type MyFoo: foo.AlsoFoo
        let x: foo.Foo = axiom
        let y: MyFoo = axiom
        let z: Bool = (x = y)
    "#,
    );
    p.expect_ok("main");
}

#[test]
fn test_bad_imported_types() {
    let mut p = Project::new_mock();
    p.mock("/mock/foo.ac", FOO_AC);
    p.mock(
        "/mock/main.ac",
        r#"
        import foo
        type MyFoo: foo.NotFoo
        let x: foo.Foo = axiom
        let y: MyFoo = axiom
        let z: Bool = (x = y)
    "#,
    );
    p.expect_module_err("main");
}

#[test]
fn test_imported_constants() {
    let mut p = Project::new_mock();
    p.mock("/mock/foo.ac", FOO_AC);
    p.mock(
        "/mock/main.ac",
        r#"
        import foo
        let x: foo.Foo = axiom
        let y: foo.Foo = foo.foo
        let z: Bool = (x = y)
    "#,
    );
    p.expect_ok("main");
}

#[test]
fn test_building_project() {
    let mut p = Project::new_mock();
    p.mock("/mock/foo.ac", FOO_AC);
    p.mock(
        "/mock/main.ac",
        r#"
        import foo
        let new_foo: foo.Foo = axiom
        theorem goal { foo.fooify(new_foo) = foo.foo }
    "#,
    );
    p.load_module_by_name("foo").expect("loading foo failed");
    p.load_module_by_name("main").expect("loading main failed");
    p.add_target_by_name("foo")
        .expect("adding foo target failed");
    p.add_target_by_name("main")
        .expect("adding main target failed");
    p.expect_build_ok();
}

#[test]
fn test_target_outside_library() {
    let mut p = Project::new_mock();
    let outside_path = "/outside/foo.ac";
    p.mock(outside_path, FOO_AC);
    p.add_target_by_path(&PathBuf::from(outside_path))
        .expect("adding outside target failed");
    p.expect_build_ok();
}

#[test]
fn test_build_catches_unsolved_solve_blocks() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        let b: Bool = axiom
        solve b by {
        }
    "#,
    );
    p.expect_ok("main");
    p.expect_build_fails();
}

#[test]
fn test_repeated_verification() {
    let mut p = Project::new_mock();
    let nat_text = r#"
    inductive Nat {
        0
        suc(Nat)
    }

    let nz: Nat = axiom
    axiom nz_nonzero {
        nz != Nat.0
    }
    "#;
    p.mock("/mock/nat.ac", nat_text);
    let main_text = r#"
        from nat import Nat
        let x: Nat = axiom
        let y: Nat = axiom

        theorem goal1(a: Nat) {
            a != x or a != y or x = y
        } by {
            if a = x {
                if a = y {
                    x = y
                }
                a != y or x = y
            }
            a != x or a != y or x = y
        }

        // Relies on imported things
        theorem goal2 {
            exists(b: Nat) { nat.nz = b.suc }
        }
        "#;
    p.mock("/mock/main.ac", main_text);

    let main_descriptor = ModuleDescriptor::Name("main".to_string());
    let env = p.get_env(&main_descriptor).unwrap();
    let goal_count = env.iter_goals().count() as i32;
    assert_eq!(goal_count, 5);

    // The first verification should populate the cache, starting from an empty cache.
    let mut builder = Builder::new(|_| {});
    p.verify_module(&main_descriptor, &env, &mut builder);
    assert_eq!(builder.status, BuildStatus::Good);
    assert_eq!(builder.metrics.searches_total, 5);
    assert_eq!(builder.metrics.searches_full, 5);
    assert_eq!(builder.metrics.searches_filtered, 0);
    let module_cache = p.build_cache.get_cloned(&main_descriptor).unwrap();
    assert_eq!(module_cache.blocks.len(), 2);
    module_cache.assert_premises_eq("goal1", &[]);
    module_cache.assert_premises_eq("goal2", &["nat:Nat.new", "nat:nz_nonzero"]);

    // Run a second verification with no changes. This should use the cache.
    let mut builder = Builder::new(|_| {});
    p.verify_module(&main_descriptor, &env, &mut builder);
    assert_eq!(builder.status, BuildStatus::Good);
    assert_eq!(builder.metrics.searches_total, 0);
    assert_eq!(builder.metrics.searches_full, 0);
    assert_eq!(builder.metrics.searches_filtered, 0);
    let module_cache = p.build_cache.get_cloned(&main_descriptor).unwrap();
    assert_eq!(module_cache.blocks.len(), 2);
    module_cache.assert_premises_eq("goal1", &[]);
    module_cache.assert_premises_eq("goal2", &["nat:Nat.new", "nat:nz_nonzero"]);

    // After we bust all the hashes, it should use the premise cache.
    p.mock("/mock/nat.ac", format!("// \n{}", nat_text).as_str());
    let env = p.get_env(&main_descriptor).unwrap();
    let mut builder = Builder::new(|_| {});
    p.verify_module(&main_descriptor, &env, &mut builder);
    assert_eq!(builder.status, BuildStatus::Good);
    assert_eq!(builder.metrics.searches_total, 5);
    assert_eq!(builder.metrics.searches_full, 0);
    assert_eq!(builder.metrics.searches_filtered, 5);
    let module_cache = p.build_cache.get_cloned(&main_descriptor).unwrap();
    assert_eq!(module_cache.blocks.len(), 2);
    module_cache.assert_premises_eq("goal1", &[]);
    module_cache.assert_premises_eq("goal2", &["nat:Nat.new", "nat:nz_nonzero"]);

    // When we rename a theorem, it should do a fallback.
    let new_nat_text = nat_text.replace("nz_nonzero", "nz_nonzero_renamed");
    p.mock("/mock/nat.ac", new_nat_text.as_str());
    let env = p.get_env(&main_descriptor).unwrap();
    let mut builder = Builder::new(|_| {});
    p.verify_module(&main_descriptor, &env, &mut builder);
    assert_eq!(builder.status, BuildStatus::Good);
    assert_eq!(builder.metrics.searches_total, 5);
    assert_eq!(builder.metrics.searches_full, 1);
    assert_eq!(builder.metrics.searches_filtered, 5);
    let module_cache = p.build_cache.get_cloned(&main_descriptor).unwrap();
    assert_eq!(module_cache.blocks.len(), 2);
    module_cache.assert_premises_eq("goal1", &[]);
    module_cache.assert_premises_eq("goal2", &["nat:Nat.new", "nat:nz_nonzero_renamed"]);
}

#[test]
fn test_completions() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/nat.ac",
        r#"
        inductive Nat {
            0
            suc(Nat)
        }

        theorem ugly {
            true = true
        }
        "#,
    );
    let main = PathBuf::from("/mock/main.ac");
    p.mock(
        main.to_str().unwrap(),
        r#"
        from nat import Nat
        let foo: Nat = axiom
        let bar: Nat = axiom
        theorem goal(bop: Nat) {
            bop != foo or bop != bar or foo = bar
        } by {
            // This should be line 7. Let's test completions here.
        }
        "#,
    );
    let env = p
        .get_env(&ModuleDescriptor::Name("main".to_string()))
        .unwrap();

    // Make sure the indexes are what we expect
    assert_eq!(env.get_line_type(0), Some(LineType::Empty));
    assert_eq!(env.get_line_type(1), Some(LineType::Other));
    assert_eq!(env.get_line_type(2), Some(LineType::Other));
    assert_eq!(env.get_line_type(3), Some(LineType::Other));
    assert_eq!(env.get_line_type(4), Some(LineType::Node(0)));
    assert_eq!(env.get_line_type(5), Some(LineType::Node(0)));
    assert_eq!(env.get_line_type(6), Some(LineType::Node(0)));
    assert_eq!(env.get_line_type(7), Some(LineType::Node(0)));
    assert_eq!(env.get_line_type(8), Some(LineType::Node(0)));
    assert_eq!(env.get_line_type(9), None);

    let check = |prefix: &str, line: u32, expected: &[&str]| {
        let completions = match p.get_completions(Some(&main), line, prefix) {
            Some(c) => c,
            None => {
                assert!(expected.is_empty(), "no completions found for '{}'", prefix);
                return;
            }
        };
        let labels: Vec<_> = completions.iter().map(|c| &c.label).collect();
        assert_eq!(labels, expected, "completions for '{}'", prefix);
    };

    // Test completions
    check("from nat import N", 0, &["Nat"]);
    check("ba", 7, &["bar"]);
    check("fo", 7, &["forall", "foo"]);
    check("b", 7, &["by", "bar", "bop"]);
    check("Nat.s", 7, &["suc"]);
    check("foo.s", 7, &["suc"]);
    check("nat.N", 7, &["Nat"]);
    check("(ba", 7, &["bar"]);
    check("nat.u", 7, &[]);
    check("nat.", 7, &["Nat"]);
    check("foo.", 7, &["0", "induction", "suc"]);
}

#[test]
fn test_build_cache() {
    let mut p = Project::new_mock();
    let lib_text = r#"
    let thing1: Bool = axiom
    let thing2: Bool = thing1

    theorem one {
        thing1 = thing2
    }
    "#;
    let main_text = r#"
    import lib
    theorem two {
        lib.thing1 = lib.thing2
    }
    "#;
    p.mock("/mock/lib.ac", lib_text);
    p.mock("/mock/main.ac", main_text);
    let num_success = p.expect_build_ok();
    assert_eq!(num_success, 2);
    assert_eq!(p.build_cache.len(), 2);

    // Just rebuilding a second time should require no work
    let num_success = p.expect_build_ok();
    assert_eq!(num_success, 0);

    // If we change main, we should only have to rebuild main
    let touched_main = format!("// Touch\n{}", main_text);
    p.update_file(PathBuf::from("/mock/main.ac"), &touched_main, 1)
        .expect("update failed");
    let num_success = p.expect_build_ok();
    assert_eq!(num_success, 1);

    // If we change lib, we should have to rebuild both
    let touched_lib = format!("// Touch\n{}", lib_text);
    p.update_file(PathBuf::from("/mock/lib.ac"), &touched_lib, 1)
        .expect("update failed");
    let num_success = p.expect_build_ok();
    assert_eq!(num_success, 2);
}

#[test]
fn test_build_cache_partial_rebuild() {
    let mut p = Project::new_mock();
    let mut lines = vec![
        "theorem one {",
        "    true = true",
        "}",
        "theorem two {",
        "    true = true",
        "}",
        "theorem three {",
        "    true = true",
        "}",
    ];
    let filename = "/mock/main.ac";
    p.mock(filename, &lines.join("\n"));
    let num_success = p.expect_build_ok();
    assert_eq!(num_success, 3);

    // Change the middle theorem
    lines[4] = "    false = false";
    p.update_file(PathBuf::from(filename), &lines.join("\n"), 1)
        .expect("update failed");
    let num_success = p.expect_build_ok();
    assert_eq!(num_success, 2);
}

#[test]
fn test_module_name_forbidden_as_function_arg() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        let foobool: Bool = true
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        import foo

        let bar: Bool -> Bool = function(foo: Bool) {
            true
        }
        "#,
    );
    p.expect_module_err("main");
}

#[test]
fn test_module_name_forbidden_as_define_arg() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        let foobool: Bool = true
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        import foo

        define bar(foo: Bool) -> Bool {
            true
        }
        "#,
    );
    p.expect_module_err("main");
}

#[test]
fn test_instance_of_imported_typeclass() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/semigroup.ac",
        r#"
        typeclass S: Semigroup {
            // Semigroups have a binary operation
            mul: (S, S) -> S

            // The operation must be associative
            associative(x: S, y: S, z: S) {
                (x * y) * z = x * (y * z)
            }
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        from semigroup import Semigroup

        inductive Foo {
            foo
        }

        attributes Foo {
            define mul(self, f: Foo) -> Foo {
                Foo.foo
            }
        }

        instance Foo: Semigroup {
            let mul: (Foo, Foo) -> Foo = Foo.mul
        }
        "#,
    );
    p.expect_ok("semigroup");
    p.expect_ok("main");
}

#[test]
fn test_indirect_importing() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        inductive Foo {
            foo
        }

        attributes Foo {
            let a: Bool = true
        }
        "#,
    );
    p.mock(
        "/mock/bar.ac",
        r#"
        from foo import Foo

        attributes Foo {
            let b: Bool = true
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        from bar import Foo

        let a: Bool = Foo.a
        let b: Bool = Foo.b
        "#,
    );
    p.expect_ok("bar");
    p.expect_ok("main");
}

#[test]
fn test_importing_let_attr_conflict() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        inductive Foo {
            foo
        }

        attributes Foo {
            let a: Bool = true
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        from foo import Foo

        attributes Foo {
            let a: Bool = false
        }
        "#,
    );
    p.expect_ok("foo");
    p.expect_module_err("main");
}

#[test]
fn test_importing_define_attr_conflict() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        inductive Foo {
            foo
        }

        attributes Foo {
            define a(self) -> Bool { true }
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        from foo import Foo

        attributes Foo {
            define a(self) -> Bool { true }
        }
        "#,
    );
    p.expect_ok("foo");
    p.expect_module_err("main");
}

#[test]
fn test_diamond_attribute_conflict() {
    // bar and baz are both all right on their own, but they conflict with each other.
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        inductive Foo {
            foo
        }
        "#,
    );
    p.mock(
        "/mock/bar.ac",
        r#"
        from foo import Foo

        attributes Foo {
            let a: Bool = false
        }
        "#,
    );
    p.mock(
        "/mock/baz.ac",
        r#"
        from foo import Foo

        attributes Foo {
            let a: Bool = true
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        import bar
        import baz
        "#,
    );
    p.expect_ok("bar");
    p.expect_ok("baz");
    p.expect_module_err("main");
}

#[test]
fn test_instance_separate_from_class_and_typeclass() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        inductive Foo {
            foo
        }
        "#,
    );
    p.mock(
        "/mock/pointed.ac",
        r#"
        typeclass P: Pointed {
            origin: P
        }
        "#,
    );
    p.mock(
        "/mock/relate.ac",
        r#"
        from foo import Foo
        from pointed import Pointed

        instance Foo: Pointed {
            let origin: Foo = Foo.foo
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        from foo import Foo
        from pointed import Pointed
        import relate

        define get_point<P: Pointed>(p: P) -> P {
            P.origin
        }

        let p: Foo = get_point(Foo.foo)
        "#,
    );
    p.expect_ok("relate");
    p.expect_ok("main");
}

#[test]
fn test_diamond_instance_conflict() {
    // bar and baz are both all right on their own, but they conflict with each other.
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        typeclass P: Pointed {
            origin: P
        }

        inductive Foo {
            foo1
            foo2
        }
        "#,
    );
    p.mock(
        "/mock/bar.ac",
        r#"
        from foo import Foo, Pointed

        instance Foo: Pointed {
            let origin: Foo = Foo.foo1
        }
        "#,
    );
    p.mock(
        "/mock/baz.ac",
        r#"
        from foo import Foo, Pointed

        instance Foo: Pointed {
            let origin: Foo = Foo.foo2
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        import bar
        import baz
        "#,
    );
    p.expect_ok("bar");
    p.expect_ok("baz");
    p.expect_module_err("main");
}

#[test]
fn test_mixed_in_attribute() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        inductive Foo {
            foo
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        from foo import Foo

        attributes Foo {
            define a(self) -> Bool { true }
        }

        theorem goal {
            Foo.foo.a
        }
        "#,
    );
    p.expect_ok("foo");
    p.expect_ok("main");
}

#[test]
fn test_hover_basic() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        indoc! {r#"
    /// Nat_doc_comment
    inductive Nat {                           // line 1
        0                                     // line 2
        suc(Nat)                              // line 3
    }
    // 3456789012345678901234567890
    let one: Nat = Nat.suc(Nat.0)             // line 6
    define make_nat(odd: Bool) -> Nat {       // line 7
        if odd {                              // line 8
            one                               // line 9
        } else {
            Nat.suc(one)                      // line 11
        }
    }
    /// HasZero_doc_comment                   // line 14
    typeclass Z: HasZero {
        0: Z
    }
    // 34567890123456789012345678901
    instance Nat: HasZero {                   // line 19
        let 0 = Nat.0                         // line 20
    }
    theorem eq_zero<Z: HasZero>(a: Z) {       // line 22
        a = Z.0                               // line 23
    } by {
        let b: Z = a                          // line 25
    }
    /// equals_doc_comment
    define equals<T>(x: T, y: T) -> Bool {    // line 28
        x = y                             
    }
    let z_eq_z = equals(Nat.0, Nat.0)         // line 31
    /// num_doc_comment
    let num: Nat = make_nat(true)             // line 33
    /// List_doc_comment
    inductive List<T> {                       // line 35
        nil
        cons(T, List<T>)
    }
    let l = List.cons(num, List.nil<Nat>)     // line 39
    // 34567890123456789012345678901
    let m: Nat satisfy {                      // line 41
        m = m
    }
    "#},
    );
    p.expect_ok("main");
    let desc = ModuleDescriptor::Name("main".to_string());
    let env = p.get_env(&desc).expect("no env for main");
    assert!(p.hover(&env, 6, 9).is_some()); // Nat
    assert!(p.hover(&env, 6, 19).is_some()); // suc
    assert!(p.hover(&env, 6, 24).is_some()); // Nat
    assert!(p.hover(&env, 6, 26).is_none()); // .
    assert!(p.hover(&env, 6, 27).is_some()); // 0
    assert!(p.hover(&env, 6, 30).is_none()); // past end of line
    assert!(p.hover(&env, 7, 22).is_some()); // Bool
    assert!(p.hover(&env, 7, 30).is_some()); // Nat
    assert!(p.hover(&env, 8, 9).is_some()); // odd
    assert!(p.hover(&env, 9, 9).is_some()); // one
    assert!(p.hover(&env, 11, 9).is_some()); // Nat
    assert!(p.hover(&env, 11, 13).is_some()); // suc
    assert!(p.hover(&env, 11, 17).is_some()); // one
    assert!(p.hover(&env, 19, 9).is_some()); // Nat
    assert!(p.hover(&env, 19, 14).is_some()); // HasZero
    assert!(p.hover(&env, 20, 12).is_some()); // Nat
    assert!(p.hover(&env, 20, 16).is_some()); // 0
    assert!(p.hover(&env, 22, 19).is_some()); // HasZero
    assert!(p.hover(&env, 22, 31).is_some()); // Z
    assert!(p.hover(&env, 23, 4).is_some()); // a
    assert!(p.hover(&env, 23, 8).is_some()); // Z
    assert!(p.hover(&env, 23, 10).is_some()); // 0
    assert!(p.hover(&env, 25, 11).is_some()); // Z
    assert!(p.hover(&env, 25, 15).is_some()); // a
    assert!(p.hover(&env, 28, 20).is_some()); // T
    assert!(p.hover(&env, 31, 20).is_some()); // Nat
    assert!(p.hover(&env, 41, 8).is_some()); // Nat

    // Check hovers

    let nat_hover = format!("{:?}", p.hover(&env, 6, 11));
    assert!(nat_hover.contains("Nat_doc_comment"));

    let has_zero_hover = format!("{:?}", p.hover(&env, 19, 19));
    assert!(has_zero_hover.contains("HasZero_doc_comment"));

    let equals_hover = format!("{:?}", p.hover(&env, 31, 14));
    assert!(equals_hover.contains("equals_doc_comment"));

    let num_hover = format!("{:?}", p.hover(&env, 39, 18));
    assert!(num_hover.contains("num_doc_comment"));

    let list_hover = format!("{:?}", p.hover(&env, 39, 23));
    assert!(list_hover.contains("List_doc_comment"));

    // Check that "Go to" links are present
    let nat_hover_str = format!("{:?}", p.hover(&env, 6, 11));
    assert!(nat_hover_str.contains("Go to Nat"));

    let has_zero_hover_str = format!("{:?}", p.hover(&env, 19, 19));
    assert!(has_zero_hover_str.contains("Go to HasZero"));
}

#[test]
fn test_hover_with_imports() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        indoc! {r"
        /// module_doc_comment
        
        /// type_doc_comment
        inductive Foo {               // line 3
            foo
        }

        /// val_doc_comment
        let bar = (Foo.foo = Foo.foo)
        "},
    );
    p.mock(
        "/mock/main.ac",
        indoc! {r#"
        // 3456789012345678901234567890  
        from foo import Foo, bar         // line 1
        "#},
    );
    let desc = ModuleDescriptor::Name("main".to_string());
    let env = p.get_env(&desc).expect("no env for main");
    assert!(p.hover(&env, 1, 2).is_none()); // from
    assert!(p.hover(&env, 1, 7).is_some()); // foo
    assert!(p.hover(&env, 1, 10).is_none()); // import
    assert!(p.hover(&env, 1, 17).is_some()); // Foo
    assert!(p.hover(&env, 1, 21).is_some()); // bar

    // Check hovers

    let module_hover = format!("{:?}", p.hover(&env, 1, 7));
    assert!(module_hover.contains("module_doc_comment"));
    assert!(!module_hover.contains("type_doc_comment"));

    let type_hover = format!("{:?}", p.hover(&env, 1, 17));
    assert!(!type_hover.contains("module_doc_comment"));
    assert!(type_hover.contains("type_doc_comment"));

    let val_hover = format!("{:?}", p.hover(&env, 1, 21));
    assert!(val_hover.contains("val_doc_comment"));
}

#[test]
fn test_import_default_ac() {
    let mut p = Project::new_mock();

    // Create a module in foo/default.ac
    p.mock(
        "/mock/foo/default.ac",
        r#"
        type Foo: axiom
        let foo_value: Foo = axiom
        "#,
    );

    // Import from foo should find foo/default.ac
    p.mock(
        "/mock/main.ac",
        r#"
        import foo
        let x: foo.Foo = foo.foo_value
        "#,
    );

    p.expect_ok("main");
}

#[test]
fn test_import_from_default_ac() {
    let mut p = Project::new_mock();

    // Create a module in bar/default.ac
    p.mock(
        "/mock/bar/default.ac",
        r#"
        inductive Bar {
            bar1
            bar2
        }
        let bar_constant: Bar = Bar.bar1
        "#,
    );

    // Test various import styles
    p.mock(
        "/mock/main.ac",
        r#"
        from bar import Bar, bar_constant
        let b1: Bar = Bar.bar1
        let b2: Bar = bar_constant
        "#,
    );

    p.expect_ok("main");
}

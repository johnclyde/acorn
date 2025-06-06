use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;

use crate::builder::{BuildEvent, BuildMetrics, BuildStatus};
use crate::project::Project;

/// Output from running the verifier
#[derive(Debug)]
pub struct VerifierOutput {
    /// The overall build status
    pub status: BuildStatus,

    /// Build metrics collected during verification
    pub metrics: BuildMetrics,

    /// All build events collected during verification
    pub events: Vec<BuildEvent>,
}

impl VerifierOutput {
    /// How many verification events were collected.
    pub fn num_verified(&self) -> usize {
        self.events.iter().filter(|e| e.verified.is_some()).count()
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ProverMode {
    /// Uses the cache, skipping modules entirely if they are already built.
    /// This is the default mode.
    Standard,

    /// Does not use the cache, and builds everything from scratch.
    Full,

    /// Uses the cache, but only for filtering premise retrieval. Does not skip modules.
    Filtered,
}

pub struct Verifier {
    mode: ProverMode,

    /// The target module to verify.
    /// If None, all modules are verified.
    target: Option<String>,

    /// If true, a dataset is created, for training.
    create_dataset: bool,

    /// The starting path to find the acorn library from.
    start_path: PathBuf,
}

impl Verifier {
    pub fn new(
        start_path: PathBuf,
        mode: ProverMode,
        target: Option<String>,
        create_dataset: bool,
    ) -> Self {
        Self {
            mode,
            target,
            create_dataset,
            start_path,
        }
    }

    /// Returns VerifierOutput on success, or an error string if verification fails.
    pub fn run(&self) -> Result<VerifierOutput, String> {
        let mut project = match Project::new_local(&self.start_path, self.mode) {
            Ok(p) => p,
            Err(e) => return Err(format!("Error: {}", e)),
        };

        if let Some(target) = &self.target {
            if target.ends_with(".ac") {
                // Looks like a filename
                let path = PathBuf::from(&target);
                if let Err(e) = project.add_target_by_path(&path) {
                    return Err(format!("{}", e));
                }
            } else {
                if let Err(e) = project.add_target_by_name(&target) {
                    return Err(format!("{}", e));
                }
            }
        } else {
            project.add_all_targets();
        }

        // Create a vector to collect events
        let events = Rc::new(RefCell::new(Vec::new()));
        let events_clone = events.clone();

        // Set up the builder
        let mut builder = project.builder(move |event| {
            // Also print log messages as before
            if let Some(m) = &event.log_message {
                if let Some(diagnostic) = &event.diagnostic {
                    println!(
                        "{}, line {}: {}",
                        event.module,
                        diagnostic.range.start.line + 1,
                        m
                    );
                } else {
                    println!("{}", m);
                }
            }

            // Store the event
            events_clone.borrow_mut().push(event);
        });

        if self.mode == ProverMode::Filtered {
            builder.log_when_slow = true;
        }
        if self.create_dataset {
            builder.create_dataset();
        }
        if self.target.is_none() {
            builder.log_secondary_errors = false;
        }

        // Build
        project.build(&mut builder);
        builder.metrics.print(builder.status);
        if let Some(dataset) = builder.dataset {
            dataset.save();
        }

        if self.mode == ProverMode::Filtered && builder.metrics.searches_fallback > 0 {
            println!("Warning: the filtered prover was not able to handle all goals.");
        }

        // Create the output
        let output = VerifierOutput {
            status: builder.status,
            metrics: builder.metrics,
            events: events.take(),
        };

        Ok(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_fs::fixture::ChildPath;
    use assert_fs::prelude::*;
    use assert_fs::TempDir;

    /// Creates a standard Acorn project layout with acorn.toml, src/, and build/ directories.
    /// Returns (project dir, src_dir, build_dir) for use in tests.
    /// Close the project directory after use to clean up.
    fn setup() -> (TempDir, ChildPath, ChildPath) {
        let temp = TempDir::new().unwrap();
        temp.child("acorn.toml").write_str("").unwrap();
        let src = temp.child("src");
        src.create_dir_all().unwrap();
        let build = temp.child("build");
        build.create_dir_all().unwrap();
        (temp, src, build)
    }

    #[test]
    fn test_verifier_with_simple_acornlib() {
        // Create a temporary directory with acornlib structure
        let temp = TempDir::new().unwrap();
        let acornlib = temp.child("acornlib");
        acornlib.create_dir_all().unwrap();

        // Create foo.ac with a simple theorem
        let foo_ac = acornlib.child("foo.ac");
        foo_ac
            .write_str(
                r#"
                theorem simple_truth {
                    true
                }
                "#,
            )
            .unwrap();

        // Create a verifier and test that it can run successfully
        let verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProverMode::Standard,
            Some("foo".to_string()),
            false,
        );

        // Test that the verifier was created successfully with the right parameters
        assert_eq!(verifier.start_path, acornlib.path());
        assert_eq!(verifier.mode, ProverMode::Standard);
        assert_eq!(verifier.target, Some("foo".to_string()));
        assert_eq!(verifier.create_dataset, false);

        // Test that the verifier can run successfully on our simple theorem
        let result = verifier.run();
        assert!(
            result.is_ok(),
            "Verifier should successfully verify the simple theorem: {:?}",
            result
        );

        // Check that we actually proved something
        let output = result.unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.goals_total, 1); // Should have 1 theorem to prove
        assert_eq!(output.metrics.goals_success, 1); // Should have successfully proven 1 theorem
        assert!(output.metrics.searches_total > 0); // Should have performed at least one search
        assert!(!output.events.is_empty());
        assert!(output.num_verified() > 0);

        temp.close().unwrap();
    }

    #[test]
    fn test_verifier_with_acorn_toml_layout() {
        // Create a temporary directory with the new acorn.toml + src layout
        let (acornlib, src, build) = setup();

        // Create foo.ac inside the src directory
        let foo_ac = src.child("foo.ac");
        foo_ac
            .write_str(
                r#"
                theorem simple_truth {
                    true
                }
                "#,
            )
            .unwrap();

        // Create a verifier starting from the acornlib directory
        // The verifier should find the src directory and use it as the root
        let verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProverMode::Standard,
            Some("foo".to_string()),
            false,
        );

        // Test that the verifier can run successfully on our theorem in the src directory
        let result = verifier.run();
        assert!(
            result.is_ok(),
            "Verifier should successfully verify the theorem in src directory: {:?}",
            result
        );

        // Check that we actually proved something
        let output = result.unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.goals_total, 1); // Should have 1 theorem to prove
        assert_eq!(output.metrics.goals_success, 1); // Should have successfully proven 1 theorem
        assert!(output.metrics.searches_total > 0); // Should have performed at least one search

        // Check that we created a file in the build directory
        let build_file = build.child("foo.yaml");
        assert!(build_file.exists(),);

        // Verify again - should use the cache
        let result2 = verifier.run();
        assert!(
            result2.is_ok(),
            "Second verifier should successfully run: {:?}",
            result2
        );

        // Check that the cache was used
        let output2 = result2.unwrap();
        assert_eq!(output2.status, BuildStatus::Good);
        assert_eq!(
            output2.metrics.searches_total, 0,
            "Should use cache and perform no searches"
        );

        acornlib.close().unwrap();
    }

    #[test]
    fn test_verifier_uses_nested_cache() {
        // Create a temporary directory with the new acorn.toml + src layout
        let (acornlib, src, build) = setup();

        // Create a nested directory structure
        let foo_dir = src.child("foo");
        foo_dir.create_dir_all().unwrap();

        // Create a file at foo/bar.ac with one theorem
        let bar_ac = foo_dir.child("bar.ac");
        bar_ac
            .write_str(
                r#"
                theorem nested_truth {
                    true
                }
                "#,
            )
            .unwrap();

        // Create a verifier targeting the nested module
        let verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProverMode::Standard,
            Some("foo.bar".to_string()),
            false,
        );

        // Run the verifier the first time
        let result = verifier.run();
        assert!(
            result.is_ok(),
            "First verifier run should succeed: {:?}",
            result
        );

        // Check that we actually proved something
        let output = result.unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.goals_total, 1); // Should have 1 theorem to prove
        assert_eq!(output.metrics.goals_success, 1); // Should have successfully proven 1 theorem
        assert!(output.metrics.searches_total > 0); // Should have performed at least one search

        // Check that we created a file in the nested build directory
        let build_foo_dir = build.child("foo");
        let build_file = build_foo_dir.child("bar.yaml");
        assert!(
            build_file.exists(),
            "Cache file should exist at build/foo/bar.yaml"
        );

        // Verify again - should use the cache
        let result2 = verifier.run();
        assert!(
            result2.is_ok(),
            "Second verifier should successfully run: {:?}",
            result2
        );

        // Check that the cache was used
        let output2 = result2.unwrap();
        assert_eq!(output2.status, BuildStatus::Good);
        assert_eq!(
            output2.metrics.searches_total, 0,
            "Should use cache and perform no searches"
        );

        acornlib.close().unwrap();
    }

    #[test]
    fn test_verifier_filter_picks_up_imported_extends() {
        let (acornlib, src, _) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
            typeclass F: Foo {
                foo_property: Bool
            }

            typeclass B: Bar extends Foo {
                bar_property: Bool
            }

            axiom bar_has_foo_property<B: Bar> {
                B.foo_property
            }

            typeclass Baz extends Bar {
                baz_property: Bool
            }
        "#,
            )
            .unwrap();

        src.child("main.ac")
            .write_str(
                r#"
            from foo import Baz

            // To prove this, we need to know that Baz extends Bar.
            theorem baz_has_foo_property<B: Baz> {
                B.foo_property
            }
        "#,
            )
            .unwrap();

        let verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProverMode::Standard,
            Some("main".to_string()),
            false,
        );
        assert!(verifier1.run().is_ok(), "Verifier should run successfully");

        let verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProverMode::Filtered,
            Some("main".to_string()),
            false,
        );
        let output = verifier2.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good,);
        assert_eq!(output.metrics.searches_fallback, 0,);

        acornlib.close().unwrap();
    }

    #[test]
    fn test_verifier_filter_picks_up_local_extends() {
        let (acornlib, src, _) = setup();

        src.child("main.ac")
            .write_str(
                r#"
            typeclass F: Foo {
                foo_property: Bool
            }

            typeclass B: Bar extends Foo {
                bar_property: Bool
            }

            axiom bar_has_foo_property<B: Bar> {
                B.foo_property
            }

            typeclass Baz extends Bar {
                baz_property: Bool
            }

            // To prove this, we need to know that Baz extends Bar.
            theorem baz_has_foo_property<B: Baz> {
                B.foo_property
            }
        "#,
            )
            .unwrap();

        let verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProverMode::Standard,
            Some("main".to_string()),
            false,
        );
        let output = verifier1.run().unwrap();
        assert_eq!(output.num_verified(), 5);

        let verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProverMode::Filtered,
            Some("main".to_string()),
            false,
        );
        let output = verifier2.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good,);
        assert_eq!(output.metrics.searches_fallback, 0,);
        assert_eq!(output.num_verified(), 5);

        acornlib.close().unwrap();
    }

    #[test]
    fn test_verifier_fails_on_circular_import() {
        let (acornlib, src, _) = setup();

        src.child("foo.ac").write_str("import bar").unwrap();
        src.child("bar.ac").write_str("import foo").unwrap();

        let verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProverMode::Standard,
            Some("foo".to_string()),
            false,
        );

        let result = verifier.run();
        let Err(err) = result else {
            panic!("Verifier should fail on circular import: {:?}", result);
        };

        assert!(
            err.contains("circular"),
            "Expected circular import error, got: {}",
            err
        );

        if err.lines().map(|l| l.contains("^^^^^")).count() != 1 {
            panic!(
                "Expected exactly one ^^^^^^ line in the error message, got:\n{}",
                err
            );
        }

        acornlib.close().unwrap();
    }

    #[test]
    fn test_verifier_fails_on_ambiguous_import() {
        let (acornlib, src, _) = setup();

        // Create both foo.ac and foo/default.ac
        src.child("foo.ac").write_str("type Foo: axiom").unwrap();
        std::fs::create_dir_all(src.child("foo").path()).unwrap();
        src.child("foo")
            .child("default.ac")
            .write_str("type Bar: axiom")
            .unwrap();

        // Try to import the ambiguous module
        src.child("main.ac").write_str("import foo").unwrap();

        let verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProverMode::Standard,
            Some("main".to_string()),
            false,
        );

        let result = verifier.run();
        let Ok(output) = result else {
            panic!(
                "Verifier should run but report compilation error: {:?}",
                result
            );
        };

        // The verifier should report a compilation error
        assert_eq!(output.status, BuildStatus::Error);

        // Check that the error message contains "ambiguous"
        let error_messages: Vec<String> = output
            .events
            .iter()
            .filter_map(|e| e.log_message.as_ref())
            .cloned()
            .collect();
        let error_text = error_messages.join("\n");
        assert!(
            error_text.contains("ambiguous"),
            "Expected ambiguous import error, got: {}",
            error_text
        );

        acornlib.close().unwrap();
    }
}

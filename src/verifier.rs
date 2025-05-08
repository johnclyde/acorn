use std::path::PathBuf;

use crate::project::Project;

#[derive(Debug, PartialEq, Eq)]
pub enum VerifierMode {
    Standard,
    Full,
    Filtered,
}

pub struct Verifier {
    mode: VerifierMode,
    target: Option<String>,
    create_dataset: bool,
}

impl Verifier {
    pub fn new(mode: VerifierMode, target: Option<String>, create_dataset: bool) -> Self {
        Self {
            mode,
            target,
            create_dataset,
        }
    }

    pub fn run(&self) {
        let use_cache = self.mode != VerifierMode::Full;

        let mut project = Project::new_local(use_cache).unwrap();
        if self.mode == VerifierMode::Filtered {
            project.check_hashes = false;
        }

        if let Some(target) = &self.target {
            if target.ends_with(".ac") {
                // Looks like a filename
                let path = PathBuf::from(&target);
                if !project.add_target_by_path(&path) {
                    println!("File not found: {}", target);
                    return;
                }
            } else {
                if !project.add_target_by_name(&target) {
                    println!("Module not found: {}", target);
                    return;
                }
            }
        } else {
            project.add_all_targets();
        }

        // Set up the builder
        let mut builder = project.builder(|event| {
            if let Some(m) = event.log_message {
                if let Some(diagnostic) = event.diagnostic {
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
        });
        builder.log_when_slow = true;
        if self.create_dataset {
            builder.create_dataset();
        }

        // Build
        project.build(&mut builder);
        builder.print_stats();
        if let Some(dataset) = builder.dataset {
            dataset.save();
        }

        if self.mode == VerifierMode::Filtered && builder.searches_full > 0 {
            println!("\nWarning: the filtered prover was not able to handle all goals.");
            std::process::exit(1);
        }
    }
}

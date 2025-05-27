use std::path::PathBuf;

use crate::block::NodeCursor;
use crate::project::Project;
use crate::prover::{Outcome, Prover};
use crate::verifier::ProverMode;

pub struct Searcher {
    /// The target module or file to search in.
    target: String,

    /// The line number to search at (1-based, as provided by the user).
    line_number: u32,

    /// The starting path to find the acorn library from.
    start_path: PathBuf,

    /// The mode to use for the verifier.
    mode: ProverMode,
}

impl Searcher {
    pub fn new(start_path: PathBuf, mode: ProverMode, target: String, line_number: u32) -> Self {
        Self {
            target,
            line_number,
            start_path,
            mode,
        }
    }

    /// Runs the search and returns an error string if the search fails.
    pub fn run(&self) -> Result<(), String> {
        let mut project = match Project::new_local(&self.start_path, self.mode) {
            Ok(p) => p,
            Err(e) => return Err(format!("Error: {}", e)),
        };

        // Convert from 1-based (external) to 0-based (internal) line number
        let internal_line_number = self.line_number - 1;

        let module_id = project
            .load_module_by_name(&self.target)
            .map_err(|e| format!("Failed to load module '{}': {}", self.target, e))?;

        let env = project
            .get_env_by_id(module_id)
            .ok_or_else(|| format!("No environment found for module '{}'", self.target))?;

        let path = env.path_for_line(internal_line_number).map_err(|s| {
            format!(
                "no proposition for line {} in {}: {}",
                self.line_number, self.target, s
            )
        })?;

        let cursor = NodeCursor::from_path(env, &path);
        let goal_context = cursor.goal_context().map_err(|e| {
            format!(
                "Error getting goal at line {} in {}: {}",
                self.line_number, self.target, e
            )
        })?;

        println!("proving {} ...", goal_context.description);

        let verbose = true;
        let mut prover = if self.mode == ProverMode::Filtered {
            // Try to use the filtered prover if we're in filtered mode
            let module_descriptor = project
                .get_module_descriptor(module_id)
                .ok_or_else(|| format!("Module {} not found", module_id))?;
            let module_cache = project.get_module_cache(module_descriptor);

            match project.make_filtered_prover(&cursor, &module_cache) {
                Some(filtered_prover) => {
                    println!("using filtered prover");
                    filtered_prover
                }
                None => {
                    return Err(format!(
                        "Cannot create filtered prover: no cached premises found for {} at line {}. \
                        Run verification in standard mode first to build the cache.",
                        cursor.block_name(),
                        self.line_number
                    ));
                }
            }
        } else {
            // Use full prover in other modes
            let mut prover = Prover::new(&project, verbose);
            for fact in cursor.usable_facts(&project) {
                prover.add_fact(fact);
            }
            prover
        };

        prover.strict_codegen = true;
        prover.set_goal(&goal_context);

        loop {
            let outcome = prover.partial_search();

            match outcome {
                Outcome::Success => {
                    println!("success!");

                    prover.get_and_print_proof(&project, &env.bindings);
                    let proof = prover.get_condensed_proof().unwrap();
                    match proof.to_code(&env.bindings) {
                        Ok(code) => {
                            println!("generated code:\n");
                            for line in &code {
                                println!("{}", line);
                            }
                        }
                        Err(e) => {
                            eprintln!("\nerror generating code: {}", e);
                        }
                    }
                }
                Outcome::Inconsistent => {
                    println!("Found inconsistency!");
                    prover.get_and_print_proof(&project, &env.bindings);
                }
                Outcome::Exhausted => {
                    println!("All possibilities have been exhausted.");
                }
                Outcome::Timeout => {
                    println!("activated {} steps", prover.num_activated());
                    continue;
                }
                Outcome::Interrupted => {
                    println!("Interrupted.");
                }
                Outcome::Constrained => {
                    println!("Constrained.");
                }
                Outcome::Error(s) => {
                    println!("Error: {}", s);
                }
            }

            break;
        }

        Ok(())
    }
}

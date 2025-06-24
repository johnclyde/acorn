use std::path::PathBuf;

use crate::block::NodeCursor;
use crate::project::Project;
use crate::prover::{Outcome, Prover};
use crate::verifier::ProverMode;

pub enum SearchTarget {
    Line(u32),
    Name(String),
}

pub struct Searcher {
    /// The target module or file to search in.
    module: String,

    /// What we're searching for - either a line number or theorem name
    target: SearchTarget,

    /// The starting path to find the acorn library from.
    start_path: PathBuf,

    /// The mode to use for the verifier.
    mode: ProverMode,
}

impl Searcher {
    pub fn new_by_line(start_path: PathBuf, mode: ProverMode, module: String, line_number: u32) -> Self {
        Self {
            module,
            target: SearchTarget::Line(line_number),
            start_path,
            mode,
        }
    }

    pub fn new_by_name(start_path: PathBuf, mode: ProverMode, module: String, theorem_name: String) -> Self {
        Self {
            module,
            target: SearchTarget::Name(theorem_name),
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

        let module_id = project
            .load_module_by_name(&self.module)
            .map_err(|e| format!("Failed to load module '{}': {}", self.module, e))?;

        let env = project
            .get_env_by_id(module_id)
            .ok_or_else(|| format!("No environment found for module '{}'", self.module))?;

        // Get the cursor based on the search target
        let cursor = match &self.target {
            SearchTarget::Line(line_number) => {
                // Convert from 1-based (external) to 0-based (internal) line number
                let internal_line_number = line_number - 1;
                
                let path = env.path_for_line(internal_line_number).map_err(|s| {
                    format!(
                        "no proposition for line {} in {}: {}",
                        line_number, self.module, s
                    )
                })?;
                
                NodeCursor::from_path(env, &path)
            }
            SearchTarget::Name(theorem_name) => {
                // Find the node by theorem name
                match env.iter_goals().find(|node| {
                    node.goal_context()
                        .map(|ctx| ctx.description == *theorem_name)
                        .unwrap_or(false)
                }) {
                    Some(cursor) => cursor,
                    None => {
                        // List available theorems to help the user
                        let available: Vec<String> = env.iter_goals()
                            .filter_map(|node| {
                                node.goal_context()
                                    .ok()
                                    .map(|ctx| ctx.description)
                            })
                            .collect();
                        
                        if available.is_empty() {
                            return Err(format!(
                                "No theorem named '{}' found in module '{}'. No theorems found in this module.",
                                theorem_name, self.module
                            ));
                        } else {
                            return Err(format!(
                                "No theorem named '{}' found in module '{}'. Available theorems:\n  {}",
                                theorem_name, self.module, available.join("\n  ")
                            ));
                        }
                    }
                }
            }
        };

        let goal_context = cursor.goal_context().map_err(|e| {
            format!(
                "Error getting goal for {}: {}",
                match &self.target {
                    SearchTarget::Line(n) => format!("line {}", n),
                    SearchTarget::Name(n) => format!("theorem '{}'", n),
                },
                e
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

            let block_name = cursor.block_name();
            match project.make_filtered_prover(env, &block_name, &module_cache) {
                Some(mut filtered_prover) => {
                    println!("using filtered prover");
                    for fact in cursor.block_facts() {
                        filtered_prover.add_fact(fact);
                    }
                    filtered_prover
                }
                None => {
                    println!("filtered prover failed, using full prover");
                    Prover::new(&project, verbose)
                }
            }
        } else {
            Prover::new(&project, verbose)
        };

        for fact in cursor.usable_facts(&project) {
            prover.add_fact(fact);
        }

        prover.set_goal(&goal_context);
        let outcome = prover.full_search();

        match outcome {
            Outcome::Success => {
                println!("success!");
                let proof = prover.get_and_print_proof(&project, &env.bindings);
                if let Some(p) = proof {
                    match p.to_code(&env.bindings) {
                        Ok(code) => {
                            for line in code {
                                println!("  {}", line);
                            }
                        }
                        Err(e) => {
                            println!("code generation error: {:?}", e);
                        }
                    }
                }
            }
            Outcome::Exhausted => {
                println!("proof search exhausted");
            }
            Outcome::Inconsistent => {
                println!("inconsistent axioms");
            }
            Outcome::Constrained => {
                println!("proof attempt was constrained by typechecking");
            }
            Outcome::Timeout => {
                println!("timeout");
            }
            Outcome::Interrupted => {
                println!("interrupted");
            }
            Outcome::Error(e) => {
                println!("error: {}", e);
            }
        }

        Ok(())
    }
}

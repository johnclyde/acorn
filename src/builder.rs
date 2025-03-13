use std::sync::atomic::AtomicU32;
use std::time::Duration;

use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity};

use crate::block::NodeCursor;
use crate::compilation::Error;
use crate::dataset::Dataset;
use crate::environment::Environment;
use crate::features::Features;
use crate::goal::GoalContext;
use crate::module::ModuleDescriptor;
use crate::prover::{Outcome, Prover};

static NEXT_BUILD_ID: AtomicU32 = AtomicU32::new(1);

// A "build" is when we verify a set of goals, determined by a Project.
// For each build, we report many  build events.
#[derive(Debug)]
pub struct BuildEvent {
    // Which build this is an event for.
    pub build_id: u32,

    // Current progress is done / total.
    // This is across all modules.
    pub progress: Option<(i32, i32)>,

    // Human-readable
    pub log_message: Option<String>,

    // The module that the build event is coming from.
    pub module: ModuleDescriptor,

    // Whenever we run into a problem, report a diagnostic.
    pub diagnostic: Option<Diagnostic>,

    // Whenever we verify a goal, report the lines that the goal covers.
    // Note that this is only the final goal. Subgoals might have failed to verify.
    pub verified: Option<(u32, u32)>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BuildStatus {
    // No problems of any kind
    Good,

    // Warnings indicate code that parses okay but can't be verified
    Warning,

    // Errors indicate either the user entered bad code, or we ran into a bug in the build process
    Error,
}

impl BuildStatus {
    pub fn verb(&self) -> &str {
        match self {
            BuildStatus::Good => "succeeded",
            BuildStatus::Warning => "warned",
            BuildStatus::Error => "errored",
        }
    }

    pub fn warn(&mut self) {
        if *self == BuildStatus::Good {
            *self = BuildStatus::Warning;
        }
    }

    pub fn is_error(&self) -> bool {
        match self {
            BuildStatus::Error => true,
            _ => false,
        }
    }

    pub fn is_good(&self) -> bool {
        match self {
            BuildStatus::Good => true,
            _ => false,
        }
    }
}

// The Builder contains all the mutable state for a single build.
// This is separate from the Project because you can read information from the Project from other
// threads while a build is ongoing, but a Builder is only used by the build itself.
pub struct Builder<'a> {
    // A single event handler is used across all modules.
    event_handler: Box<dyn FnMut(BuildEvent) + 'a>,

    pub status: BuildStatus,

    // A unique id for each build.
    pub id: u32,

    // The total number of goals to be verified.
    // Counted up during the loading phase.
    pub goals_total: i32,

    // The number of goals that we have processed in the build.
    // This includes cache hits, successful searches, and unsuccessful searches.
    pub goals_done: i32,

    // The number of goals that were successfully proven, either via search or via cache.
    pub goals_success: i32,

    // When this flag is set, we emit build events when a goal is slow.
    pub log_when_slow: bool,

    // The current module we are proving.
    current_module: Option<ModuleDescriptor>,

    // Whether the current module has neither errors nor warnings.
    // I guess if there is no current module, it's vacuously good.
    current_module_good: bool,

    // If dataset is not None, we are gathering data for training.
    pub dataset: Option<Dataset>,

    // The Builder also tracks statistics.
    // When we use the cache, we don't use it to modify these statistics.

    // How many proof searches we did.
    pub searches_total: i32,

    // Number of proof searches that ended in success.
    pub searches_success: i32,

    // The number of searches that we ran the full prover on.
    pub searches_full: i32,

    // The number of searches that we ran the filtered prover on.
    // This plus searches_full can sum to more than searches_total because we run both sometimes.
    pub searches_filtered: i32,

    // The total number of clauses activated.
    pub clauses_activated: i32,

    // Total sum of square num_activated.
    pub clauses_sum_square_activated: u64,

    // Total number of clauses scored, both active and passive.
    pub clauses_total: i32,

    // The total amount of time spent proving, in seconds.
    pub proving_time: f64,
}

impl<'a> Builder<'a> {
    pub fn new(event_handler: impl FnMut(BuildEvent) + 'a) -> Self {
        let event_handler = Box::new(event_handler);
        Builder {
            event_handler,
            status: BuildStatus::Good,
            id: NEXT_BUILD_ID.fetch_add(1, std::sync::atomic::Ordering::SeqCst),
            goals_total: 0,
            goals_done: 0,
            goals_success: 0,
            log_when_slow: false,
            current_module: None,
            current_module_good: true,
            dataset: None,
            searches_total: 0,
            searches_success: 0,
            searches_full: 0,
            searches_filtered: 0,
            clauses_activated: 0,
            clauses_sum_square_activated: 0,
            clauses_total: 0,
            proving_time: 0.0,
        }
    }

    fn default_event(&self) -> BuildEvent {
        BuildEvent {
            build_id: self.id,
            progress: None,
            log_message: None,
            module: self.module().clone(),
            diagnostic: None,
            verified: None,
        }
    }

    // Returns Anonymous while loading
    fn module(&self) -> ModuleDescriptor {
        match &self.current_module {
            None => ModuleDescriptor::Anonymous,
            Some(m) => m.clone(),
        }
    }

    // Called when a single module is loaded successfully.
    pub fn module_loaded(&mut self, env: &Environment) {
        self.goals_total += env.iter_goals().count() as i32;
    }

    // When create_dataset is called, that tells the Builder to gather data for training.
    // Only call this before the build starts.
    pub fn create_dataset(&mut self) {
        assert_eq!(self.goals_done, 0);
        self.dataset = Some(Dataset::new());
    }

    // Called when the entire loading phase is done.
    pub fn loading_phase_complete(&mut self) {
        let event = BuildEvent {
            progress: Some((0, self.goals_total)),
            ..self.default_event()
        };
        (self.event_handler)(event);
    }

    // Logs an informational message that doesn't change build status.
    pub fn log_info(&mut self, message: String) {
        let event = BuildEvent {
            log_message: Some(message),
            ..self.default_event()
        };
        (self.event_handler)(event);
    }

    // Logs an error during the loading phase, that can be localized to a particular place.
    pub fn log_loading_error(&mut self, descriptor: &ModuleDescriptor, error: &Error) {
        let diagnostic = Diagnostic {
            range: error.range(),
            severity: Some(DiagnosticSeverity::ERROR),
            message: error.to_string(),
            ..Diagnostic::default()
        };
        let event = BuildEvent {
            log_message: Some(format!("compilation error: {}", error)),
            module: descriptor.clone(),
            diagnostic: Some(diagnostic),
            ..self.default_event()
        };
        (self.event_handler)(event);
        self.status = BuildStatus::Error;
    }

    // Called when we start proving a module.
    pub fn module_proving_started(&mut self, descriptor: ModuleDescriptor) {
        self.current_module = Some(descriptor);
        self.current_module_good = true;
    }

    // Returns whether the module completed without any errors or warnings.
    pub fn module_proving_complete(&mut self, module: &ModuleDescriptor) -> bool {
        assert_eq!(&self.module(), module);
        let answer = self.current_module_good;
        self.current_module = None;
        self.current_module_good = true;
        answer
    }

    // Called when a single proof search completes.
    // Statistics are tracked here.
    pub fn search_finished(
        &mut self,
        prover: &Prover,
        goal_context: &GoalContext,
        outcome: Outcome,
        elapsed: Duration,
    ) {
        // Time conversion
        let secs = elapsed.as_secs() as f64;
        let subsec_nanos = elapsed.subsec_nanos() as f64;
        let elapsed_f64 = secs + subsec_nanos * 1e-9;
        let elapsed_str = format!("{:.3}s", elapsed_f64);

        // Tracking statistics
        self.goals_done += 1;
        self.searches_total += 1;
        self.proving_time += elapsed_f64;
        let clauses_activated = prover.num_activated() as i32;
        self.clauses_activated += clauses_activated;
        let num_passive = prover.num_passive() as i32;
        self.clauses_total += clauses_activated + num_passive;
        self.clauses_sum_square_activated += (clauses_activated * clauses_activated) as u64;

        match outcome {
            Outcome::Success => match prover.get_condensed_proof() {
                None => self.log_proving_warning(&prover, &goal_context, "had a missing proof"),
                Some(proof) => {
                    if proof.needs_simplification() {
                        self.log_proving_warning(&prover, &goal_context, "needs simplification");
                    } else {
                        // Both of these count as a search success.
                        self.goals_success += 1;
                        self.searches_success += 1;
                        if self.log_when_slow && elapsed_f64 > 0.1 {
                            self.log_proving_info(
                                &prover,
                                &goal_context,
                                &format!("took {}", elapsed_str),
                            );
                        } else {
                            self.log_proving_success(goal_context);
                        }
                    }

                    // As long as we have a proof, we can collect data for our dataset.
                    if let Some(ref mut dataset) = self.dataset {
                        for (id, step) in prover.iter_active_steps() {
                            let features = Features::new(step);
                            let label = proof.has_active_id(id);
                            dataset.add(features, label);
                        }
                    }
                }
            },
            Outcome::Exhausted => {
                self.log_proving_warning(&prover, &goal_context, "could not be verified")
            }
            Outcome::Inconsistent => {
                self.log_proving_warning(&prover, &goal_context, "- prover found an inconsistency")
            }
            Outcome::Timeout => self.log_proving_warning(
                &prover,
                &goal_context,
                &format!("timed out after {}", elapsed_str),
            ),
            Outcome::Interrupted => {
                self.log_proving_error(&prover, &goal_context, "was interrupted");
            }
            Outcome::Error => {
                self.log_proving_error(&prover, &goal_context, "had an error");
            }
            Outcome::Constrained => self.log_proving_warning(
                &prover,
                &goal_context,
                "stopped after hitting constraints",
            ),
        }
    }

    // Logs a successful proof.
    fn log_proving_success(&mut self, goal_context: &GoalContext) {
        let line_pair = (goal_context.first_line, goal_context.last_line);
        let event = BuildEvent {
            progress: Some((self.goals_done, self.goals_total)),
            verified: Some(line_pair),
            ..self.default_event()
        };
        (self.event_handler)(event);
    }

    // Logs a cache hit for this node and every child of it.
    // Returns the cursor to its initial state when done.
    pub fn log_proving_cache_hit(&mut self, node: &mut NodeCursor) {
        if node.num_children() > 0 {
            node.descend(0);
            loop {
                self.log_proving_cache_hit(node);
                if node.has_next() {
                    node.next();
                } else {
                    break;
                }
            }
            node.ascend();
        }
        if node.current().has_goal() {
            let goal_context = node.goal_context().unwrap();
            self.goals_done += 1;
            self.goals_success += 1;
            self.log_proving_success(&goal_context);
        }
    }

    // Create a build event for a proof that was other than successful.
    fn make_event(
        &mut self,
        prover: &Prover,
        goal_context: &GoalContext,
        message: &str,
        sev: DiagnosticSeverity,
    ) -> BuildEvent {
        let mut full_message = format!("{} {}", goal_context.description, message);
        if let Some(e) = &prover.error {
            full_message.push_str(&format!(": {}", e));
        }
        let diagnostic = Diagnostic {
            range: goal_context.goal.range(),
            severity: Some(sev),
            message: full_message.clone(),
            ..Diagnostic::default()
        };
        BuildEvent {
            progress: Some((self.goals_done, self.goals_total)),
            log_message: Some(full_message),
            diagnostic: Some(diagnostic),
            ..self.default_event()
        }
    }

    fn log_proving_info(&mut self, prover: &Prover, goal_context: &GoalContext, message: &str) {
        let event = self.make_event(
            prover,
            goal_context,
            message,
            DiagnosticSeverity::INFORMATION,
        );
        (self.event_handler)(event);
    }

    // Logs a warning. Warnings can only happen during the proving phase.
    fn log_proving_warning(&mut self, prover: &Prover, goal_context: &GoalContext, message: &str) {
        let event = self.make_event(prover, goal_context, message, DiagnosticSeverity::WARNING);
        (self.event_handler)(event);
        self.current_module_good = false;
        self.status.warn();
    }

    // Logs an error during the proving phase.
    fn log_proving_error(&mut self, prover: &Prover, goal_context: &GoalContext, message: &str) {
        let mut event = self.make_event(prover, goal_context, message, DiagnosticSeverity::WARNING);

        // Set progress as complete, because an error will halt the build
        event.progress = Some((self.goals_total, self.goals_total));
        (self.event_handler)(event);
        self.current_module_good = false;
        self.status = BuildStatus::Error;
    }

    pub fn print_stats(&self) {
        println!();
        match self.status {
            BuildStatus::Error => {
                println!("Build failed.");
                return;
            }
            BuildStatus::Warning => {
                println!("Build completed with warnings.");
            }
            BuildStatus::Good => {
                println!("Build completed successfully.");
            }
        }
        println!("{}/{} OK", self.goals_success, self.goals_total);
        println!("{} searches performed", self.searches_total);
        if self.searches_total > 0 {
            let success_percent = 100.0 * self.searches_success as f64 / self.searches_total as f64;
            println!("{:.1}% search success rate", success_percent);
            let num_activated = self.clauses_activated as f64 / self.searches_success as f64;
            println!("{:.2} average activations", num_activated);
            let mean_square_activated =
                self.clauses_sum_square_activated as f64 / self.searches_total as f64;
            println!("{:.1} mean square activations", mean_square_activated);
            let num_clauses = self.clauses_total as f64 / self.searches_total as f64;
            println!("{:.2} average clauses", num_clauses);
            let proving_time_ms = 1000.0 * self.proving_time / self.searches_total as f64;
            println!("{:.1} ms average proving time", proving_time_ms);
        }
    }
}

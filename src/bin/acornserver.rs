// The Acorn Language Server. This is typically invoked by a VS Code extension.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use acorn::builder::BuildEvent;
use acorn::live_document::LiveDocument;
use chrono;
use clap::Parser;
use color_backtrace::BacktracePrinter;
use dashmap::DashMap;
use tokio::sync::{mpsc, RwLock, RwLockWriteGuard};
use tower_lsp::jsonrpc;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use acorn::block::NodeCursor;
use acorn::interfaces::{
    DocumentProgress, InfoParams, InfoResponse, ProgressParams, ProgressResponse, SearchParams,
    SearchResponse, SearchStatus,
};
use acorn::module::{LoadState, ModuleDescriptor};
use acorn::project::Project;
use acorn::prover::{Outcome, Prover};

#[derive(Parser)]
struct Args {
    // The root folder the user has open
    #[clap(long)]
    workspace_root: Option<String>,

    // The root folder of the extension
    #[clap(long)]
    extension_root: String,
}

// These messages will show up in the "Acorn Language Server" channel in the output tab.
// User-visible, if the user looks for them.
fn log(message: &str) {
    let timestamp = chrono::Local::now().format("%H:%M:%S%.3f");
    let stamped = format!("[{}] {}", timestamp, message);
    eprintln!("{}", stamped);
}

// Only converts to path if it's a file scheme.
// The Rust docs claim that the regular to_file_path shouldn't be relied on for this.
fn to_path(url: &Url) -> Option<PathBuf> {
    if url.scheme() == "file" {
        url.to_file_path().ok()
    } else {
        None
    }
}

fn log_with_url(url: &Url, version: i32, message: &str) {
    let versioned = format!("{} v{}: {}", url, version, message);
    log(&versioned);
}

// A search task is a long-running task that searches for a proof.
// The language server can work on one search task at a time.
// The SearchTask tracks information around that request.
// It is clonable so that it can be used both by the thread doing the task, and
// threads handling requests.
// The thread doing the search updates the task with its information, while threads handling
// concurrent user requests can read it.
#[derive(Clone)]
struct SearchTask {
    project: Arc<RwLock<Project>>,
    url: Url,
    version: i32,

    // While we are proving, most of the time the thread running the 'run' method
    // will hold a write lock on the prover.
    // The task will release and reacquire the lock intermittently, and the RwLock is fair so other
    // threads get a chance to use the prover.
    prover: Arc<RwLock<Prover>>,

    // The module that we're searching for a proof in
    descriptor: ModuleDescriptor,

    // The line in the document the user selected to kick off this task.
    selected_line: u32,

    // The path to the goal
    path: Vec<usize>,

    // A displayable name for the goal
    goal_name: String,

    // The range of the goal in the document
    goal_range: Range,

    // The Status is periodically updated by the task.
    // It can indicate either partial progress or completion.
    status: Arc<RwLock<SearchStatus>>,

    // Set this flag to true when a subsequent search task has been created
    superseded: Arc<AtomicBool>,

    // Zero-based line where we would insert a proof for this goal
    proof_insertion_line: u32,

    // Whether we need to also insert a block, if we do insert a proof.
    insert_block: bool,

    // The search id set by the extenson for the original search that created this task.
    // The extension may send new searches with essentially the same parameters, that we
    // discard. This is inevitable because the extension doesn't have enough information to
    // disambiguate searches. Only the language server does.
    // Thus, when we get redundant searches, we keep using the original id downstream.
    id: i32,
}

impl SearchTask {
    // Makes a response based on the current state of the task
    async fn response(&self) -> SearchResponse {
        let status = self.status.read().await.clone();
        SearchResponse {
            uri: self.url.clone(),
            version: self.version,
            failure: None,
            loading: false,
            goal_name: Some(self.goal_name.clone()),
            goal_range: Some(self.goal_range.clone()),
            status,
            proof_insertion_line: self.proof_insertion_line,
            insert_block: self.insert_block,
            id: self.id,
        }
    }

    // Runs the search task.
    async fn run(&self) {
        // This holds a read lock on the project the whole time.
        // It seems like we should be able to avoid this, but maybe it's just fine.
        let project = self.project.read().await;
        let env = match project.get_env(&self.descriptor) {
            Some(env) => env,
            None => {
                log(&format!("no environment for {:?}", self.descriptor));
                return;
            }
        };

        log(&format!("running search task for {}", self.goal_name));

        loop {
            // Each iteration through the loop reacquires the write lock on the prover.
            // This lets other threads access the prover in between iterations.
            let mut prover = self.prover.write().await;
            let outcome = prover.partial_search();
            let status = match &outcome {
                Outcome::Success => {
                    let proof = prover.get_condensed_proof().unwrap();
                    let steps = prover.to_proof_info(&project, &env.bindings, &proof);

                    let (code, error) = match proof.to_code(&env.bindings) {
                        Ok(code) => (Some(code), None),
                        Err(e) => (None, Some(e.to_string())),
                    };

                    SearchStatus::success(code, error, steps, proof.needs_simplification(), &prover)
                }

                Outcome::Inconsistent
                | Outcome::Exhausted
                | Outcome::Constrained
                | Outcome::Error(_) => SearchStatus::stopped(&prover, &outcome),

                Outcome::Timeout => SearchStatus::pending(&prover),

                Outcome::Interrupted => {
                    // No point in providing a result for this task, since nobody is listening.
                    log(&format!("goal {} interrupted", self.goal_name));
                    return;
                }
            };

            // Update the status
            let mut locked_status = self.status.write().await;
            *locked_status = status;

            if outcome != Outcome::Timeout {
                // We're done
                log(&format!("search task for {} completed", self.goal_name));
                break;
            }
        }
    }
}

// The part of the Build that is relevant to a single document.
struct DocumentBuildInfo {
    // The version of the document that we built with.
    // If we got it from the filesystem, there is no version.
    version: Option<i32>,

    // The line ranges with goals that have been verified.
    // Should not include any ranges that are subsumed, or overlap with diagnostics.
    verified: Vec<(u32, u32)>,

    // Errors and warnings that have been generated for this document.
    diagnostics: Vec<Diagnostic>,
}

impl DocumentBuildInfo {
    fn new(version: Option<i32>) -> DocumentBuildInfo {
        DocumentBuildInfo {
            version,
            verified: vec![],
            diagnostics: vec![],
        }
    }

    // Called when a new goal has been verified.
    fn verify(&mut self, first_line: u32, last_line: u32) {
        if let Some(diagnostic) = self.diagnostics.last() {
            // If the last diagnostic overlaps with this goal, that means we can verify
            // the final step of the proof, but not all the previous steps.
            // In this case, we don't report the verification downstream.
            if diagnostic.range.end.line >= first_line && diagnostic.range.start.line <= last_line {
                return;
            }
        }

        // We can clear any previous verifications that are subsumed by this one.
        while let Some((line, _)) = self.verified.last() {
            if *line < first_line {
                break;
            }
            self.verified.pop();
        }
        self.verified.push((first_line, last_line));
    }

    // Called when a new problem has been reported.
    fn add_diagnostic(&mut self, diagnostic: Diagnostic) {
        self.diagnostics.push(diagnostic);
    }
}

// Information about the most recent build.
struct BuildInfo {
    // An id for the build, unique per run of the language server.
    // If this is None, we do not intend to be showing information for any build.
    id: Option<u32>,

    // How many goals have been verified.
    done: i32,
    total: i32,

    // Whether the build is finished or not.
    // Distinguishes the scenarios:
    //   1. This build is 0/0 complete because it finished its zero goals
    //   2. This build is 0/0 complete because it hasn't counted the goals yet
    finished: bool,

    // Per-document information
    docs: HashMap<Url, DocumentBuildInfo>,
}

impl BuildInfo {
    // A placeholder representing no build.
    fn none() -> BuildInfo {
        BuildInfo {
            id: None,
            done: 0,
            total: 0,
            finished: false,
            docs: HashMap::new(),
        }
    }

    // Turn the known build information into a progress response.
    fn progress(&self) -> ProgressResponse {
        let mut docs = HashMap::new();
        for (url, doc) in &self.docs {
            // No need to report verified lines for files that aren't open.
            if let Some(version) = doc.version {
                docs.insert(
                    url.clone(),
                    DocumentProgress {
                        version,
                        verified: doc.verified.clone(),
                    },
                );
            }
        }
        ProgressResponse {
            build_id: self.id,
            done: self.done,
            total: self.total,
            finished: self.finished,
            docs,
        }
    }

    fn finish(&mut self) {
        self.finished = true;
    }

    // Take a function that modifies a DocumentBuildInfo and apply it to the document.
    // Creates a new entry if the document is not already in the map.
    fn with_doc(
        &mut self,
        url: &Url,
        f: impl FnOnce(&mut DocumentBuildInfo),
    ) -> &DocumentBuildInfo {
        let doc = self
            .docs
            .entry(url.clone())
            .or_insert_with(|| DocumentBuildInfo::new(None));
        f(doc);
        doc
    }

    // Clears everything in preparation for a new build.
    // Then sets docs for the open documents.
    async fn reset(&mut self, project: &Project, client: &Client) {
        // Clear the diagnostics for all the open documents.
        let mut new_docs = HashMap::new();
        for (url, version) in project.open_urls() {
            client
                .publish_diagnostics(url.clone(), vec![], Some(version))
                .await;
            new_docs.insert(url, DocumentBuildInfo::new(Some(version)));
        }
        // Clear the diagnostics for any closed documents.
        for url in self.docs.keys() {
            if !new_docs.contains_key(url) {
                client.publish_diagnostics(url.clone(), vec![], None).await;
            }
        }
        *self = BuildInfo::none();
        self.docs = new_docs;
    }

    async fn handle_event(&mut self, project: &Project, client: &Client, event: &BuildEvent) {
        if Some(event.build_id) != self.id {
            if self.id.is_some() {
                log("warning: a new build started without clearing the old one");
                return;
            }
            self.id = Some(event.build_id);
        }
        if let Some((done, total)) = event.progress {
            self.done = done;
            self.total = total;
        }
        if let Some(message) = &event.log_message {
            log(message);
        }
        if let Some(url) = project.url_from_descriptor(&event.module) {
            if let Some((first_line, last_line)) = &event.verified {
                self.with_doc(&url, |doc| {
                    doc.verify(*first_line, *last_line);
                });
            }
            if let Some(diagnostic) = &event.diagnostic {
                let doc = self.with_doc(&url, |doc| {
                    doc.add_diagnostic(diagnostic.clone());
                });
                client
                    .publish_diagnostics(url, doc.diagnostics.clone(), doc.version)
                    .await;
            }
        }
    }
}

// One Backend per root folder.
// The Backend implements a similar API to the LanguageServer API, but it doesn't implement
// "initialize" because that's used by the LazyBackend to create the Backend.
struct Backend {
    client: Client,

    // The project we're working on
    project: Arc<RwLock<Project>>,

    // Information about the most recent build to run.
    build: Arc<RwLock<BuildInfo>>,

    // Maps uri to its document. The LiveDocument tracks changes.
    documents: DashMap<Url, Arc<RwLock<LiveDocument>>>,

    // The current search task, if any
    search_task: Arc<RwLock<Option<SearchTask>>>,
}

// Finds the acorn library to use, given the root folder for the current workspace.
// Falls back to the library bundled with the extension.
// Also returns a flag for whether the library looks writable.
// Panics if we can't find either.
fn find_acorn_library(args: &Args) -> (PathBuf, bool) {
    // Check for a local library, near the code
    if let Some(workspace_root) = &args.workspace_root {
        let path = PathBuf::from(&workspace_root);
        if let Some(library_root) = Project::find_local_acorn_library(&path) {
            return (library_root, true);
        }
    }

    // Use the bundled library.
    let library_root = PathBuf::from(&args.extension_root).join("acornlib");
    if !library_root.exists() {
        panic!(
            "packaging error: no acorn library at {}",
            library_root.display()
        );
    }
    (library_root, false)
}

impl Backend {
    // Creates a new backend.
    // Determines which library to use based on the root of the current workspace.
    // If we can't find one in a logical location based on the editor, we use
    // the library bundled with the extension.
    fn new(client: Client) -> Backend {
        let args = Args::parse();
        let (library_root, cache_writable) = find_acorn_library(&args);

        log(&format!(
            "using acorn library at {}",
            library_root.display()
        ));

        // The cache is always readable, only sometimes writable.
        let project = Project::new(library_root, true, cache_writable);
        Backend {
            project: Arc::new(RwLock::new(project)),
            client,
            build: Arc::new(RwLock::new(BuildInfo::none())),
            documents: DashMap::new(),
            search_task: Arc::new(RwLock::new(None)),
        }
    }

    // Run a build in a background thread, proving the goals in all open documents.
    // Both spawned threads hold a read lock on the project while doing their work.
    // This ensures that the project doesn't change for the duration of the build.
    // The caller is responsible for stopping the previous build.
    fn spawn_build(&self) {
        let start_time = chrono::Local::now();

        // This channel passes the build events
        let (tx, mut rx) = mpsc::unbounded_channel();

        // Spawn a thread to run the build.
        let project = self.project.clone();
        tokio::spawn(async move {
            let project = project.read().await;

            tokio::task::block_in_place(move || {
                let mut builder = project.builder(move |event| {
                    tx.send(event).unwrap();
                });
                project.build(&mut builder);

                let duration = chrono::Local::now() - start_time;
                let seconds = duration.num_milliseconds() as f64 / 1000.0;
                log(&format!(
                    "verification {} after {:.2}s",
                    builder.status.verb(),
                    seconds
                ));
            });
        });

        // Spawn a thread to process the build events.
        let project = self.project.clone();
        let build = self.build.clone();
        let client = self.client.clone();
        tokio::spawn(async move {
            let project = project.read().await;
            build.write().await.reset(&project, &client).await;

            while let Some(event) = rx.recv().await {
                build
                    .write()
                    .await
                    .handle_event(&project, &client, &event)
                    .await;
            }

            build.write().await.finish();
        });
    }

    // Update the full text of the document.
    // For an open, we get the document version.
    // For a save, we don't, but we can find the version, because the version we're saving is the same
    // as the version of the last change we received.
    // After this call both the live version and the saved version should be the same.
    async fn set_full_text(&self, url: Url, text: String, version: Option<i32>) {
        // Update the live document in the document map
        let version = match version {
            Some(version) => {
                // This is an "open".
                // This document might have been open before. Just create a new one.
                log_with_url(&url, version, "new document");
                let doc = LiveDocument::new(&text, version);
                self.documents
                    .insert(url.clone(), Arc::new(RwLock::new(doc)));
                if text.is_empty() {
                    // Opening an empty file usually happens as the first of two events, when
                    // a previously untitled file has been saved. Let's not mess with the project yet.
                    return;
                }
                version
            }
            None => {
                // This is a "save".
                // We should have a document already, so mutate it.
                let doc = match self.documents.get(&url) {
                    Some(doc) => doc,
                    None => {
                        log(&format!("no document available for {}", url));
                        return;
                    }
                };
                let mut doc = doc.write().await;
                doc.save(&text)
            }
        };

        let path = match to_path(&url) {
            Some(path) => path,
            None => {
                // We don't pass on untitled documents to the project.
                return;
            }
        };

        {
            // Check if the project already has this document state.
            // If the update is a no-op, there's no need to stop the build.
            // This can happen if we are opening a document that the project is already using.
            let project = self.project.read().await;
            if project.has_version(&path, version) {
                return;
            }
        }

        let mut project = self.stop_build_and_get_project().await;
        log(&format!(
            "updating {} with {} bytes",
            path.display(),
            text.len()
        ));
        match project.update_file(path, &text, version) {
            Ok(()) => {}
            Err(e) => log(&format!("update failed: {:?}", e)),
        }
        self.spawn_build();
    }

    // If there is a build happening, stops it.
    // Acquires the write lock on the project.
    // Returns a writable reference to the project.
    async fn stop_build_and_get_project(&self) -> RwLockWriteGuard<Project> {
        {
            let project = self.project.read().await;
            project.stop_build();
        }
        // Reallow the build once we acquire the write lock
        let mut project = self.project.write().await;
        project.allow_build();
        project
    }

    fn search_fail(&self, params: SearchParams, message: &str) -> jsonrpc::Result<SearchResponse> {
        log(message);
        Ok(SearchResponse {
            failure: Some(message.to_string()),
            ..SearchResponse::new(params)
        })
    }

    async fn handle_progress_request(
        &self,
        _params: ProgressParams,
    ) -> jsonrpc::Result<ProgressResponse> {
        let progress = self.build.read().await.progress();
        Ok(progress)
    }

    // Cancels any current search task.
    // Runs the new task, if it is not None.
    async fn set_search_task(&self, new_task: Option<SearchTask>) {
        // Replace the locked singleton task
        {
            let mut locked_task = self.search_task.write().await;
            if let Some(old_task) = locked_task.as_ref() {
                // Cancel the old task
                old_task
                    .superseded
                    .store(true, std::sync::atomic::Ordering::Relaxed);
            }
            *locked_task = new_task.clone();
        }

        if let Some(new_task) = new_task {
            tokio::spawn(async move {
                new_task.run().await;
            });
        }
    }

    async fn handle_search_request(&self, params: SearchParams) -> jsonrpc::Result<SearchResponse> {
        let doc = match self.documents.get(&params.uri) {
            Some(doc) => doc,
            None => {
                return self.search_fail(params, "no text available");
            }
        };
        let doc = doc.read().await;

        // Check if this request matches our current task, based on the selected line.
        // This is less general than checking the full path, but we don't have the
        // full path until we acquire a lock on the project.
        if let Some(current_task) = self.search_task.read().await.as_ref() {
            if current_task.url == params.uri
                && current_task.version == params.version
                && current_task.selected_line == params.selected_line
            {
                return Ok(current_task.response().await);
            }
        }

        let project = self.project.read().await;
        let path = match to_path(&params.uri) {
            Some(path) => path,
            None => {
                // There should be a path available, because we don't run this task without one.
                return self.search_fail(params, "no path available in SearchTask::run");
            }
        };
        match project.get_version(&path) {
            Some(project_version) => {
                if params.version < project_version {
                    let message = &format!(
                        "user requested version {} but the project has version {}",
                        params.version, project_version
                    );
                    return self.search_fail(params, message);
                }
                if params.version > project_version {
                    // The requested version is not loaded yet.
                    return Ok(SearchResponse {
                        loading: true,
                        ..SearchResponse::new(params)
                    });
                }
            }
            None => {
                return self.search_fail(
                    params,
                    &format!("the project has not opened {}", path.display()),
                );
            }
        }
        let descriptor = match project.descriptor_from_path(&path) {
            Ok(name) => name,
            Err(e) => {
                return self.search_fail(params, &format!("descriptor_from_path failed: {:?}", e))
            }
        };
        let env = match project.get_module(&descriptor) {
            LoadState::Ok(env) => env,
            _ => {
                return self.search_fail(
                    params,
                    &format!("could not load module from {:?}", descriptor),
                );
            }
        };

        let path = match env.path_for_line(params.selected_line) {
            Ok(path) => path,
            Err(s) => return self.search_fail(params, &s),
        };

        // Check if this request matches our current task, based on the full path of the goal.
        // This is slower (because we had to acquire the project lock first)
        // but catches more situations than just checking the selected line.
        if let Some(current_task) = self.search_task.read().await.as_ref() {
            if current_task.url == params.uri
                && current_task.version == params.version
                && current_task.path == path
            {
                return Ok(current_task.response().await);
            }
        }
        let node = NodeCursor::from_path(env, &path);
        let goal_context = match node.goal_context() {
            Ok(goal_context) => goal_context,
            Err(s) => return self.search_fail(params, &s),
        };
        let superseded = Arc::new(AtomicBool::new(false));
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            prover.add_fact(fact);
        }
        prover.set_goal(&goal_context);
        prover.stop_flags.push(superseded.clone());
        let status = SearchStatus::pending(&prover);

        // Create a new search task
        let new_task = SearchTask {
            project: self.project.clone(),
            url: params.uri.clone(),
            version: doc.saved_version(),
            prover: Arc::new(RwLock::new(prover)),
            descriptor,
            selected_line: params.selected_line,
            path,
            goal_name: goal_context.description.clone(),
            goal_range: goal_context.goal.range(),
            status: Arc::new(RwLock::new(status)),
            superseded,
            proof_insertion_line: goal_context.proof_insertion_line,
            insert_block: goal_context.insert_block,
            id: params.id,
        };

        // A minimal response before any data has been collected
        let mut response = new_task.response().await;
        response.loading = true;

        self.set_search_task(Some(new_task)).await;

        Ok(response)
    }

    fn info_fail(&self, params: InfoParams, message: &str) -> jsonrpc::Result<InfoResponse> {
        log(message);
        Ok(InfoResponse {
            search_id: params.search_id,
            failure: Some(message.to_string()),
            result: None,
        })
    }

    async fn handle_info_request(&self, params: InfoParams) -> jsonrpc::Result<InfoResponse> {
        let locked_task = self.search_task.read().await;

        let task = match locked_task.as_ref() {
            Some(task) => task,
            None => return self.info_fail(params, "no search task available"),
        };
        if task.id != params.search_id {
            let failure = format!(
                "info request has search id {}, task has id {}",
                params.search_id, task.id
            );
            return self.info_fail(params, &failure);
        }
        let project = self.project.read().await;
        let prover = task.prover.read().await;
        let env = match project.get_env(&task.descriptor) {
            Some(env) => env,
            None => {
                return self.info_fail(params, "no environment available");
            }
        };
        let result = prover.info_result(&project, &env.bindings, params.clause_id);
        let failure = match result {
            Some(_) => None,
            None => Some(format!("no info available for clause {}", params.clause_id)),
        };
        Ok(InfoResponse {
            search_id: params.search_id,
            failure,
            result,
        })
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _params: InitializeParams) -> jsonrpc::Result<InitializeResult> {
        let sync_options = TextDocumentSyncCapability::Options(TextDocumentSyncOptions {
            open_close: Some(true),
            change: Some(TextDocumentSyncKind::INCREMENTAL),
            save: Some(TextDocumentSyncSaveOptions::SaveOptions(SaveOptions {
                include_text: Some(true),
            })),
            ..TextDocumentSyncOptions::default()
        });

        Ok(InitializeResult {
            server_info: None,
            capabilities: ServerCapabilities {
                text_document_sync: Some(sync_options),
                completion_provider: Some(CompletionOptions::default()),
                ..ServerCapabilities::default()
            },
        })
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        let url = params.text_document.uri;
        let text = match params.text {
            Some(text) => text,
            None => {
                log("no text available in did_save");
                return;
            }
        };

        self.set_full_text(url, text, None).await;
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let url = params.text_document.uri;
        let text = params.text_document.text;

        let version = params.text_document.version;
        self.set_full_text(url, text, Some(version)).await;
    }

    // Just updates the current version, doesn't rebuild anything
    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let url = params.text_document.uri;
        let version = params.text_document.version;
        if let Some(doc) = self.documents.get(&url) {
            let mut doc = doc.write().await;
            for change in params.content_changes {
                if let Err(e) = doc.change(change.range, &change.text, version) {
                    log(&format!("change failed: {}", e));
                }
            }
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;
        if let Some(old_doc) = self.documents.get(&uri) {
            log_with_url(&uri, old_doc.read().await.saved_version(), "closed");
        }
        self.documents.remove(&uri);
        let path = match to_path(&uri) {
            Some(path) => path,
            None => {
                // Looks like we're closing an untitled document.
                return;
            }
        };
        let mut project = self.stop_build_and_get_project().await;
        match project.close_file(path) {
            Ok(()) => {}
            Err(e) => log(&format!("close failed: {:?}", e)),
        }
    }

    async fn completion(
        &self,
        params: CompletionParams,
    ) -> jsonrpc::Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri;
        let path = to_path(&uri);
        let pos = params.text_document_position.position;
        let doc = match self.documents.get(&uri) {
            Some(doc) => doc,
            None => {
                log("no document available for completion");
                return Ok(None);
            }
        };
        let doc = doc.read().await;
        let env_line = doc.get_env_line(pos.line);
        let prefix = doc.get_prefix(pos.line, pos.character);
        let project = self.project.read().await;
        match project.get_completions(path.as_deref(), env_line, &prefix) {
            Some(items) => {
                let response = CompletionResponse::List(CompletionList {
                    is_incomplete: false,
                    items,
                });
                Ok(Some(response))
            }
            None => Ok(None),
        }
    }

    async fn shutdown(&self) -> jsonrpc::Result<()> {
        log("shutdown");
        Ok(())
    }
}

#[tokio::main]
async fn main() {
    // By default the stack traces contain a bunch of incomprehensible framework stuff.
    // This tries to clean it up.
    BacktracePrinter::new()
        .add_frame_filter(Box::new(|frames| {
            frames.retain(|frame| {
                let name = frame.name.as_deref().unwrap_or("");
                for retain in &["acorn::", "acornserver::"] {
                    if name.contains(retain) {
                        return true;
                    }
                }
                false
            });
        }))
        .install(color_backtrace::default_output_stream());

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::build(Backend::new)
        .custom_method("acorn/info", Backend::handle_info_request)
        .custom_method("acorn/progress", Backend::handle_progress_request)
        .custom_method("acorn/search", Backend::handle_search_request)
        .finish();

    Server::new(stdin, stdout, socket).serve(service).await;
}

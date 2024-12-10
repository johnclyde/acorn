use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::{fmt, io};

use regex::Regex;
use tower_lsp::lsp_types::{CompletionItem, Url};
use walkdir::WalkDir;

use crate::binding_map::BindingMap;
use crate::block::NodeCursor;
use crate::builder::{BuildEvent, BuildStatus, Builder};
use crate::compilation;
use crate::environment::Environment;
use crate::fact::Fact;
use crate::goal::GoalContext;
use crate::module::{Module, ModuleId, ModuleRef, FIRST_NORMAL};
use crate::prover::Prover;
use crate::token::Token;

// The Project is responsible for importing different files and assigning them module ids.
pub struct Project {
    // The root directory of the library.
    // This is used to resolve all imports.
    // Note that it may be different from the editor root, which is where the user is working.
    // Set to "/mock" for mock projects.
    library_root: PathBuf,

    // Whether we permit loading files from the filesystem
    use_filesystem: bool,

    // For "open" files, we use the content we are storing rather than the content on disk.
    // This can store either test data that doesn't exist on the filesystem at all, or
    // work in progress whose state is "owned" by an IDE via the language server protocol.
    //
    // Maps filename -> (contents, version number).
    // The version number can mean whatever the caller wants it to mean.
    // From vscode, it'll be the vscode version number.
    open_files: HashMap<PathBuf, (String, i32)>,

    // modules[module_id] is the (ref, Module) for the given module id.
    // Built-in modules have no name.
    modules: Vec<(ModuleRef, Module)>,

    // module_map maps from a module ref to its id
    module_map: HashMap<ModuleRef, ModuleId>,

    // The module names that we want to build.
    targets: HashSet<ModuleRef>,

    // Used as a flag to stop a build in progress.
    pub build_stopped: Arc<AtomicBool>,
}

// An error found while importing a module.
// Not an error in the code of the module itself.
#[derive(Debug)]
pub struct LoadError(pub String);

impl From<io::Error> for LoadError {
    fn from(error: io::Error) -> Self {
        LoadError(format!("{}", error))
    }
}

impl fmt::Display for LoadError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

fn new_modules() -> Vec<(ModuleRef, Module)> {
    let mut modules = vec![];
    while modules.len() < FIRST_NORMAL as usize {
        modules.push((ModuleRef::Anonymous, Module::None));
    }
    modules
}

fn check_valid_module_part(s: &str, error_name: &str) -> Result<(), LoadError> {
    if s.is_empty() {
        return Err(LoadError(format!("empty module part: {}", error_name)));
    }
    if !s.chars().next().unwrap().is_ascii_lowercase() {
        return Err(LoadError(format!(
            "module parts must start with a lowercase letter: {}",
            error_name
        )));
    }
    for char in s.chars() {
        if !char.is_ascii_alphanumeric() && char != '_' {
            return Err(LoadError(format!(
                "invalid character in module name: '{}' in {}",
                char, error_name
            )));
        }
    }
    Ok(())
}

impl Project {
    pub fn new(library_root: PathBuf) -> Project {
        Project {
            library_root,
            use_filesystem: true,
            open_files: HashMap::new(),
            modules: new_modules(),
            module_map: HashMap::new(),
            targets: HashSet::new(),
            build_stopped: Arc::new(AtomicBool::new(false)),
        }
    }

    // Finds a directory named acornlib, based on the provided path.
    // It can be either:
    //   a parent directory of the provided path
    //   a directory named "acornlib" next to one named "acorn"
    pub fn find_local_acorn_library(start: &Path) -> Option<PathBuf> {
        let mut current = Some(start);

        while let Some(path) = current {
            // Check if path is an acornlib
            if path.ends_with("acornlib") {
                return Some(path.to_path_buf());
            }

            // Check if path has a sibling named acornlib
            if path.ends_with("acorn") {
                let library_path = path.with_file_name("acornlib");
                if library_path.is_dir() {
                    return Some(library_path);
                }
            }

            current = path.parent();
        }

        None
    }

    // A Project based on the current working directory.
    // Returns None if we can't find an acorn library.
    pub fn new_local() -> Option<Project> {
        let current_dir = std::env::current_dir().ok()?;
        let library_root = Project::find_local_acorn_library(&current_dir)?;
        Some(Project::new(library_root))
    }

    // A Project where nothing can be imported.
    pub fn new_mock() -> Project {
        let mock_dir = PathBuf::from("/mock");
        let mut p = Project::new(mock_dir);
        p.use_filesystem = false;
        p
    }

    // Dropping existing modules lets you update the project for new data.
    // TODO: do this incrementally instead of dropping everything.
    fn drop_modules(&mut self) {
        self.modules = new_modules();
        self.module_map = HashMap::new();
    }

    // You only need read access to an RwLock<Project> to stop the build.
    // When the build is stopped, threads that didn't stop the build themselves should
    // finish any long-running process with an "interrupted" behavior, and give up their
    // locks on the project.
    pub fn stop_build(&self) {
        self.build_stopped
            .store(true, std::sync::atomic::Ordering::Relaxed);
    }

    // You need to have write access to a RwLock<Project> to re-allow the build.
    //
    // To change the project, acquire a read lock, stop the build, acquire a write lock, mess
    // around with the project state however you wanted, then re-allow the build.
    //
    // This asymmetry ensures that when we quickly stop and re-allow the build, any build in
    // progress will in fact stop.
    pub fn allow_build(&mut self) {
        self.build_stopped = Arc::new(AtomicBool::new(false));
    }

    // Returns whether it loaded okay.
    // Either way, it's still added as a target.
    fn add_target_by_ref(&mut self, module_ref: &ModuleRef) -> bool {
        let answer = self.load_module_by_ref(module_ref).is_ok();
        self.targets.insert(module_ref.clone());
        answer
    }

    // Returns whether it loaded okay.
    pub fn add_target_by_name(&mut self, module_name: &str) -> bool {
        self.add_target_by_ref(&ModuleRef::Name(module_name.to_string()))
    }

    // Returns whether it loaded okay.
    pub fn add_target_by_path(&mut self, path: &Path) -> bool {
        let module_ref = self.module_ref_from_path(path).unwrap();
        self.add_target_by_ref(&module_ref)
    }

    // Adds a target for all files in this directory.
    pub fn add_all_targets(&mut self) {
        if !self.use_filesystem {
            panic!("cannot add all targets without filesystem access")
        }
        for entry in WalkDir::new(&self.library_root)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            if entry.file_type().is_file() {
                let path = entry.path();

                // TODO: remove this when we want to check problems
                // Skip the file if it has the word "problems" in it
                if path.to_str().unwrap().contains("problems") {
                    continue;
                }

                if path.extension() == Some(std::ffi::OsStr::new("ac")) {
                    self.add_target_by_path(path);
                }
            }
        }
    }

    // Whether we currently have this version of a file.
    pub fn has_version(&self, path: &PathBuf, version: i32) -> bool {
        if let Some((_, v)) = self.open_files.get(path) {
            &version == v
        } else {
            false
        }
    }

    // Returns None if we don't have this file at all.
    pub fn get_version(&self, path: &PathBuf) -> Option<i32> {
        self.open_files.get(path).map(|(_, version)| *version)
    }

    // Updating a file makes us treat it as "open". When a file is open, we use the
    // content in memory for it, rather than the content on disk.
    // Updated files are also added as build targets.
    pub fn update_file(
        &mut self,
        path: PathBuf,
        content: &str,
        version: i32,
    ) -> Result<(), LoadError> {
        if self.has_version(&path, version) {
            // No need to do anything
            return Ok(());
        }
        let module_ref = self.module_ref_from_path(&path)?;
        let mut reload_modules = vec![module_ref];
        if self.open_files.contains_key(&path) {
            // We're changing the value of an existing file. This could invalidate
            // current modules.
            // For now, we just drop everything and reload the targets.
            // TODO: figure out precisely which ones are invalidated.
            self.drop_modules();
            for target in &self.targets {
                reload_modules.push(target.clone());
            }
        }
        self.open_files.insert(path, (content.to_string(), version));
        for module_ref in &reload_modules {
            self.add_target_by_ref(module_ref);
        }
        Ok(())
    }

    pub fn close_file(&mut self, path: PathBuf) -> Result<(), LoadError> {
        if !self.open_files.contains_key(&path) {
            // No need to do anything
            return Ok(());
        }
        self.open_files.remove(&path);
        let module_ref = self.module_ref_from_path(&path)?;
        self.drop_modules();
        self.targets.remove(&module_ref);
        let targets = self.targets.clone();
        for target in targets {
            self.add_target_by_ref(&target);
        }
        Ok(())
    }

    // Builds all open modules, logging build events.
    pub fn build(&self, builder: &mut Builder) {
        // Build in alphabetical order by module name for consistency.
        let mut targets = self.targets.iter().collect::<Vec<_>>();
        targets.sort();

        builder.log_info(format!(
            "verifying modules: {}",
            targets
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ));

        // The first phase is the "loading phase". We load modules and look for errors.
        // If there are errors, we won't try to do proving.
        let mut envs = vec![];
        for target in &targets {
            let module = self.get_module_by_ref(target);
            match module {
                Module::Ok(env) => {
                    builder.module_loaded(&env);
                    envs.push(env);
                }
                Module::Error(e) => {
                    if e.secondary {
                        // The real problem is in a different module.
                        // So we don't want to locate the error in this module.
                        builder.log_info(format!("error: {}", e));
                    } else {
                        builder.log_loading_error(target, e);
                    }
                }
                Module::None => {
                    // Targets are supposed to be loaded already.
                    builder.log_info(format!("error: module {} is not loaded", target));
                }
                Module::Loading => {
                    // Happens if there's a circular import. A more localized error should
                    // show up elsewhere, so let's just log.
                    builder.log_info(format!("error: module {} stuck in loading", target));
                }
            }
        }

        if builder.status.is_error() {
            return;
        }

        builder.loading_phase_complete();

        // The second pass is the "proving phase".
        for (target, env) in targets.into_iter().zip(envs) {
            self.verify_target(&target, env, builder);
            if builder.status.is_error() {
                return;
            }
        }
    }

    // Verifies all goals within this target.
    // Returns the status for this file alone.
    fn verify_target(&self, target: &ModuleRef, env: &Environment, builder: &mut Builder) {
        builder.module_proving_started(env.module_id, target, env.bindings.direct_dependencies());

        // Fast and slow modes should be interchangeable here.
        // If we run into a bug with fast mode, try using slow mode to debug.
        self.for_each_prover_fast(env, &mut |prover, goal_context| {
            self.prove(prover, goal_context, builder)
        });

        builder.module_proving_complete(target);
    }

    // Create a prover for each goal in this environment, and call the callback on it.
    // An error status makes us stop early.
    // Return the combined build status.
    // Slow version that is more simple, for debugging.
    pub fn for_each_prover_slow(
        &self,
        env: &Environment,
        callback: &mut impl FnMut(Prover, GoalContext) -> bool,
    ) {
        for node in env.iter_goals() {
            let goal_context = node.goal_context().expect("no goal context");
            let mut prover = Prover::new(&self, false);
            for fact in node.usable_facts(&self) {
                prover.add_fact(fact);
            }
            prover.set_goal(&goal_context);
            if !callback(prover, goal_context) {
                return;
            }
        }
    }

    // Create a prover for each goal in this environment, and call the callback on it.
    // An error status makes us stop early.
    // Return the combined build status.
    // Fast version that tries to clone prover state rather than rebuilding.
    pub fn for_each_prover_fast(
        &self,
        env: &Environment,
        callback: &mut impl FnMut(Prover, GoalContext) -> bool,
    ) {
        if env.nodes.is_empty() {
            // Nothing to prove
            return;
        }
        let mut prover = Prover::new(&self, false);
        for fact in self.imported_facts(env.module_id) {
            prover.add_fact(fact);
        }
        let mut node = NodeCursor::new(&env, 0);

        while self.for_each_prover_fast_helper(&prover, &mut node, callback) {
            if !node.has_next() {
                break;
            }
            prover.add_fact(node.get_fact());
            node.next();
        }
    }

    // Create a prover for every goal within this node, and call the callback on it.
    // Returns true if we should keep building, false if we should stop.
    // Prover should have all facts loaded before node, but nothing for node itself.
    // This should leave node the same way it found it, although it can mutate it
    // mid-operation.
    // If we return false, node can be left in some unusable state.
    fn for_each_prover_fast_helper(
        &self,
        prover: &Prover,
        node: &mut NodeCursor,
        callback: &mut impl FnMut(Prover, GoalContext) -> bool,
    ) -> bool {
        if node.num_children() == 0 && !node.current().has_goal() {
            // There's nothing to do here
            return true;
        }

        let mut prover = prover.clone();
        if node.num_children() > 0 {
            // We need to recurse into children
            node.descend(0);
            loop {
                if !self.for_each_prover_fast_helper(&prover, node, callback) {
                    return false;
                }

                prover.add_fact(node.get_fact());
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
            prover.set_goal(&goal_context);
            if !callback(prover, goal_context) {
                return false;
            }
        }

        true
    }

    // Proves a single goal in the target, using the provided prover.
    // Reports using the handler as appropriate.
    // Returns true if we should keep building, false if we should stop.
    fn prove(&self, mut prover: Prover, goal_context: GoalContext, builder: &mut Builder) -> bool {
        let start = std::time::Instant::now();
        let outcome = prover.verification_search();

        builder.search_finished(&prover, &goal_context, outcome, start.elapsed());

        !builder.status.is_error()
    }

    // Does the build and returns all events when it's done, rather than asynchronously.
    pub fn sync_build(&self) -> (BuildStatus, Vec<BuildEvent>) {
        let mut events = vec![];
        let status = {
            let mut builder = Builder::new(|event| events.push(event));
            self.build(&mut builder);
            builder.status
        };
        (status, events)
    }

    // Set the file content. This has priority over the actual filesystem.
    pub fn mock(&mut self, filename: &str, content: &str) {
        assert!(!self.use_filesystem);
        self.update_file(PathBuf::from(filename), content, 0)
            .expect("mock file update failed");
    }

    pub fn get_module_by_id(&self, module_id: ModuleId) -> &Module {
        match self.modules.get(module_id as usize) {
            Some((_, module)) => module,
            None => &Module::None,
        }
    }

    pub fn get_module_by_ref(&self, module_ref: &ModuleRef) -> &Module {
        match self.module_map.get(module_ref) {
            Some(id) => self.get_module_by_id(*id),
            None => &Module::None,
        }
    }

    pub fn get_env_by_id(&self, module_id: ModuleId) -> Option<&Environment> {
        if let Module::Ok(env) = self.get_module_by_id(module_id) {
            Some(env)
        } else {
            None
        }
    }

    // You have to use the canonical module ref, here. You can't use the path for a module
    // that can also be referenced by name.
    pub fn get_env_by_ref(&self, module_ref: &ModuleRef) -> Option<&Environment> {
        if let Some(module_id) = self.module_map.get(&module_ref) {
            self.get_env_by_id(*module_id)
        } else {
            None
        }
    }

    pub fn errors(&self) -> Vec<(ModuleId, &compilation::Error)> {
        let mut errors = vec![];
        for (module_id, module) in self.modules.iter().enumerate() {
            if let (_, Module::Error(e)) = module {
                errors.push((module_id as ModuleId, e));
            }
        }
        errors
    }

    fn read_file(&mut self, path: &PathBuf) -> Result<String, LoadError> {
        if let Some((content, _)) = self.open_files.get(path) {
            return Ok(content.clone());
        }
        if !self.use_filesystem {
            return Err(LoadError(format!("no mocked file for: {}", path.display())));
        }
        match std::fs::read_to_string(&path) {
            Ok(s) => Ok(s),
            Err(e) => Err(LoadError(format!(
                "error loading {}: {}",
                path.display(),
                e
            ))),
        }
    }

    // Returns the canonical module ref for a path.
    // Returns a load error if this isn't a valid path for an acorn file.
    pub fn module_ref_from_path(&self, path: &Path) -> Result<ModuleRef, LoadError> {
        let relative = match path.strip_prefix(&self.library_root) {
            Ok(relative) => relative,
            Err(_) => return Ok(ModuleRef::File(path.to_path_buf())),
        };
        let components: Vec<_> = relative
            .components()
            .map(|comp| comp.as_os_str().to_string_lossy())
            .collect();
        let mut name = String::new();
        for (i, component) in components.iter().enumerate() {
            let part = if i + 1 == components.len() {
                if !component.ends_with(".ac") {
                    return Err(LoadError(format!(
                        "path {} does not end with .ac",
                        path.display()
                    )));
                }
                component[..component.len() - 3].to_string()
            } else {
                component.to_string()
            };
            if i > 0 {
                name.push('.');
            }
            name.push_str(&part);
            check_valid_module_part(&part, &name)?;
        }

        Ok(ModuleRef::Name(name))
    }

    pub fn path_from_module_name(&self, module_name: &str) -> Result<PathBuf, LoadError> {
        let mut path = self.library_root.clone();
        let parts: Vec<&str> = module_name.split('.').collect();

        for (i, part) in parts.iter().enumerate() {
            check_valid_module_part(part, module_name)?;

            let component = if i + 1 == parts.len() {
                format!("{}.ac", part)
            } else {
                part.to_string()
            };
            path.push(component);
        }
        Ok(path)
    }

    pub fn path_from_module_ref(&self, module_ref: &ModuleRef) -> Option<PathBuf> {
        let name = match module_ref {
            ModuleRef::Name(name) => name,
            ModuleRef::File(path) => return Some(path.clone()),
            ModuleRef::Anonymous => return None,
        };

        match self.path_from_module_name(&name) {
            Ok(path) => Some(path),
            Err(_) => None,
        }
    }

    pub fn url_from_module_ref(&self, module_ref: &ModuleRef) -> Option<Url> {
        let path = self.path_from_module_ref(module_ref)?;
        Url::from_file_path(path).ok()
    }

    pub fn path_from_module_id(&self, module_id: ModuleId) -> Option<PathBuf> {
        self.path_from_module_ref(&self.modules[module_id as usize].0)
    }

    // Loads a module from cache if possible, or else from the filesystem.
    // Module names are a .-separated list where each one must be [a-z_].
    // Each component maps to a subdirectory, except the last one, which maps to a .ac file.
    // load returns an error if the module-loading process itself has an error.
    // For example, we might have an invalid name, the file might not exist, or this
    // might be a circular import.
    // If there is an error in the file, the load will return a module id, but the module
    // for the id will have an error.
    // If "open" is passed, then we cache this file's content in open files.
    fn load_module_by_ref(&mut self, module_ref: &ModuleRef) -> Result<ModuleId, LoadError> {
        if let Some(module_id) = self.module_map.get(&module_ref) {
            if *module_id < FIRST_NORMAL {
                panic!("module {} should not be loadable", module_id);
            }
            if let Module::Loading = self.get_module_by_id(*module_id) {
                return Err(LoadError(format!("circular import of {}", module_ref)));
            }
            return Ok(*module_id);
        }

        let path = match self.path_from_module_ref(module_ref) {
            Some(path) => path,
            None => {
                return Err(LoadError(format!(
                    "unloadable module ref: {:?}",
                    module_ref
                )))
            }
        };
        let text = self.read_file(&path)?;

        // Give this module an id before parsing it, so that we can catch circular imports.
        let module_id = self.modules.len() as ModuleId;
        self.modules.push((module_ref.clone(), Module::Loading));
        self.module_map.insert(module_ref.clone(), module_id);

        let mut env = Environment::new(module_id);
        let tokens = Token::scan(&text);
        let module = if let Err(e) = env.add_tokens(self, tokens) {
            Module::Error(e)
        } else {
            Module::Ok(env)
        };
        self.modules[module_id as usize].1 = module;

        Ok(module_id)
    }

    pub fn load_module_by_name(&mut self, module_name: &str) -> Result<ModuleId, LoadError> {
        let module_ref = ModuleRef::Name(module_name.to_string());
        self.load_module_by_ref(&module_ref)
    }

    // Appends all dependencies, including chains of direct dependencies.
    // Ie, if A imports B and B imports C, then A depends on B and C.
    // The order will be the "pop order", so that each module is added only
    // after all of its dependencies are added.
    pub fn all_dependencies(&self, original_module_id: ModuleId) -> Vec<ModuleId> {
        let mut answer = vec![];
        let mut seen = HashSet::new();
        self.append_dependencies(&mut seen, &mut answer, original_module_id);
        answer
    }

    // Helper function for all_dependencies.
    // Returns "false" if we have already seen this dependency.
    // Does not append module_id itself. If we want it, add that in last.
    fn append_dependencies(
        &self,
        seen: &mut HashSet<ModuleId>,
        output: &mut Vec<ModuleId>,
        module_id: ModuleId,
    ) -> bool {
        if !seen.insert(module_id) {
            return false;
        }
        if let Module::Ok(env) = self.get_module_by_id(module_id) {
            for dep in env.bindings.direct_dependencies() {
                if self.append_dependencies(seen, output, dep) {
                    output.push(dep);
                }
            }
        }
        true
    }

    pub fn get_bindings(&self, module_id: ModuleId) -> Option<&BindingMap> {
        if let Module::Ok(env) = self.get_module_by_id(module_id) {
            Some(&env.bindings)
        } else {
            None
        }
    }

    // All facts that the given module imports.
    pub fn imported_facts(&self, module_id: ModuleId) -> Vec<Fact> {
        let mut facts = vec![];
        for dependency in self.all_dependencies(module_id) {
            let env = self.get_env_by_id(dependency).unwrap();
            facts.extend(env.exported_facts());
        }
        facts
    }

    // path is the file we're in.
    // env_line is zero-based. It's the closest unchanged line, to use for finding the environment.
    // prefix is the entire line they've typed so far. Generally different from env_line.
    // Returns a list of completions, or None if we don't have any.
    pub fn get_completions(
        &self,
        path: Option<&Path>,
        env_line: u32,
        prefix: &str,
    ) -> Option<Vec<CompletionItem>> {
        let re = Regex::new(r"[a-zA-Z0-9._]+").unwrap();
        let parts: Vec<&str> = re.find_iter(prefix).map(|mat| mat.as_str()).collect();
        if parts.len() == 4 && parts[0] == "from" && parts[2] == "import" {
            // We are in a "from X import Y" statement.
            let name = parts[1];
            let partial = parts[3];
            let module_ref = ModuleRef::Name(name.to_string());
            let env = match self.get_env_by_ref(&module_ref) {
                Some(env) => env,
                None => {
                    // The module isn't loaded, so we don't know what names it has.
                    if name == "nat" && "Nat".starts_with(partial) {
                        // Cheat to optimize the tutorial.
                        // If we always loaded nat, we wouldn't need this.
                        return Some(vec![CompletionItem {
                            label: "Nat".to_string(),
                            kind: Some(tower_lsp::lsp_types::CompletionItemKind::CLASS),
                            ..Default::default()
                        }]);
                    }
                    return None;
                }
            };
            return env.bindings.get_completions(&self, partial, true);
        }

        // If we don't have a path, we can only complete imports.
        let path = path?;

        // Check if we have a completable word
        let word = match parts.last() {
            Some(word) => *word,
            None => return None,
        };

        if !word.chars().all(|c| Token::identifierish(c) || c == '.') {
            return None;
        }

        // Find the right environment
        let module_ref = self.module_ref_from_path(&path).ok()?;
        let env = match self.get_env_by_ref(&module_ref) {
            Some(env) => env,
            None => return None,
        };
        let env = env.env_for_line(env_line);

        env.bindings.get_completions(&self, word, false)
    }

    // Yields (url, version) for all open files.
    pub fn open_urls(&self) -> impl Iterator<Item = (Url, i32)> + '_ {
        self.open_files.iter().filter_map(|(path, (_, version))| {
            Url::from_file_path(path.clone())
                .ok()
                .map(|url| (url, *version))
        })
    }

    // Expects the module to load successfully and for there to be no errors in the loaded module.
    // Only for testing.
    pub fn expect_ok(&mut self, module_name: &str) -> ModuleId {
        let module_id = self.load_module_by_name(module_name).expect("load failed");
        match self.get_module_by_id(module_id) {
            Module::Ok(_) => module_id,
            Module::Error(e) => panic!("error in {}: {}", module_name, e),
            _ => panic!("logic error"),
        }
    }

    // This expects there to be an error during loading itself.
    #[cfg(test)]
    fn expect_load_err(&mut self, module_name: &str) {
        assert!(self.load_module_by_name(module_name).is_err());
    }

    // This expects the module to load, but for there to be an error in the loaded module.
    #[cfg(test)]
    fn expect_module_err(&mut self, module_name: &str) {
        let module_id = self.load_module_by_name(module_name).expect("load failed");
        if let Module::Error(_) = self.get_module_by_id(module_id) {
            // What we expected
        } else {
            panic!("expected error");
        }
    }

    // Checks that the given expression can be parsed and turned back into code.
    #[cfg(test)]
    fn check_code_into(&mut self, module_name: &str, input: &str, expected: &str) {
        use crate::expression::Expression;
        let module_id = self.expect_ok(module_name);
        let expression = Expression::expect_value(input);
        let env = self.get_env_by_id(module_id).expect("no env");
        let value = env
            .bindings
            .evaluate_value(self, &expression, None)
            .expect("could not evaluate");
        let output = env
            .bindings
            .value_to_code(&value)
            .expect("could not convert to code");

        if output != expected {
            panic!(
                "\nconverted:\n  {}\nto value:\n  {}\nand back to:\n  {}\nbut expected:\n  {}\n",
                input, value, output, expected
            );
        }
    }

    #[cfg(test)]
    fn check_code(&mut self, module_name: &str, code: &str) {
        self.check_code_into(module_name, code, code);
    }

    #[cfg(test)]
    fn expect_build_ok(&mut self) {
        let (status, events) = self.sync_build();
        assert_eq!(status, BuildStatus::Good);
        assert!(events.len() > 0);
    }

    #[cfg(test)]
    fn expect_build_fails(&mut self) {
        let (status, _) = self.sync_build();
        assert_ne!(status, BuildStatus::Good, "expected build to fail");
    }
}

#[cfg(test)]
mod tests {
    use crate::environment::LineType;

    use super::*;

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
        p.add_target_by_name("foo");
        p.add_target_by_name("main");
        p.expect_build_ok();
    }

    #[test]
    fn test_target_outside_library() {
        let mut p = Project::new_mock();
        let outside_path = "/outside/foo.ac";
        p.mock(outside_path, FOO_AC);
        p.add_target_by_path(&PathBuf::from(outside_path));
        p.expect_build_ok();
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
    fn test_build_catches_unsolved_solve_blocks() {
        let mut p = Project::new_mock();
        p.mock("/mock/main.ac", "solve false by {\n}");
        p.expect_ok("main");
        p.expect_build_fails();
    }

    #[test]
    fn test_imported_numbers_codegen() {
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
    fn test_prover_iteration_methods() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/nat.ac",
            r#"
            inductive Nat {
                0
                suc(Nat)
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from nat import Nat
            let x: Nat = axiom
            let y: Nat = axiom
            theorem goal(a: Nat) {
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
            "#,
        );

        let env = p
            .get_env_by_ref(&ModuleRef::Name("main".to_string()))
            .unwrap();

        let mut fast_count = 0;
        let mut slow_count = 0;

        p.for_each_prover_slow(env, &mut |_, _| {
            slow_count += 1;
            true
        });

        p.for_each_prover_fast(env, &mut |_, _| {
            fast_count += 1;
            true
        });

        assert_eq!(fast_count, slow_count);

        // I could test more here. But do I need to?
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
            .get_env_by_ref(&ModuleRef::Name("main".to_string()))
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
}

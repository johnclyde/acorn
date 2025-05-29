// The Acorn CLI.
// You can run a language server, verify a file, or verify the whole project.

use acorn::searcher::Searcher;
use acorn::server::{run_server, ServerArgs};
use acorn::verifier::{ProverMode, Verifier};
use clap::Parser;

const VERSION: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/VERSION"));

#[derive(Parser)]
#[clap(
    name = "acorn",
    about = "A theorem prover and programming language",
    long_about = "Acorn is a theorem prover and programming language.\n\nYou can:\n- Run a language server for IDE integration\n- Verify theorems and proofs\n- Search for proofs at specific locations",
    version = VERSION
)]
struct Args {
    /// The root folder the user has open (language server mode only)
    #[clap(long, hide = true)]
    workspace_root: Option<String>,

    /// The root folder of the extension (enables language server mode)
    #[clap(long, hide = true)]
    extension_root: Option<String>,

    /// Target module or file to verify (can be a filename or module name)
    #[clap(
        value_name = "TARGET",
        help = "Module or filename to verify. If not provided, verifies all files in the library."
    )]
    target: Option<String>,

    /// Create a dataset from the prover logs
    #[clap(long, help = "Create a dataset from the prover logs.")]
    dataset: bool,

    /// Ignore the cache and do a full reverify
    #[clap(long, help = "Ignore the cache and do a full reverify.")]
    full: bool,

    /// Use the cache only for the filtered prover, not for hash checking
    #[clap(
        long,
        help = "Use the cache only for the filtered prover, not for hash checking.",
        conflicts_with = "full"
    )]
    filtered: bool,

    /// Search for a proof at a specific line number (requires target)
    #[clap(
        long,
        help = "Search for a proof at a specific line number.",
        value_name = "LINE"
    )]
    line: Option<u32>,
}

#[tokio::main]
async fn main() {
    let args = Args::parse();

    // Check for language server mode.
    if let Some(extension_root) = args.extension_root {
        let server_args = ServerArgs {
            workspace_root: args.workspace_root,
            extension_root,
        };
        run_server(&server_args).await;
        return;
    }

    if args.workspace_root.is_some() {
        println!("--workspace-root is only relevant in language server mode.");
        std::process::exit(1);
    }

    let mode = if args.full {
        if args.filtered {
            println!("--full and --filtered are incompatible.");
            std::process::exit(1);
        }
        ProverMode::Full
    } else if args.filtered {
        ProverMode::Filtered
    } else {
        ProverMode::Standard
    };

    let current_dir = match std::env::current_dir() {
        Ok(dir) => dir,
        Err(e) => {
            println!("Error getting current directory: {}", e);
            std::process::exit(1);
        }
    };

    // Check if we should run the searcher.
    if let Some(line) = args.line {
        let Some(target) = args.target else {
            println!("Error: --line requires a target module or file to be specified.");
            std::process::exit(1);
        };
        let searcher = Searcher::new(current_dir, mode, target, line);
        if let Err(e) = searcher.run() {
            println!("{}", e);
            std::process::exit(1);
        }
        return;
    }

    // Run the verifier.
    let verifier = Verifier::new(current_dir, mode, args.target, args.dataset);
    if let Err(e) = verifier.run() {
        println!("{}", e);
        std::process::exit(1);
    }
}

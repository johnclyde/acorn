// The Acorn CLI.
// You can run a language server, verify a file, or verify the whole project.

use acorn::server::{run_server, ServerArgs};
use acorn::verifier::{Verifier, VerifierMode};
use clap::Parser;

#[derive(Parser)]
struct Args {
    // The root folder the user has open.
    // Only relevant in language server mode.
    #[clap(long)]
    workspace_root: Option<String>,

    // The root folder of the extension.
    // Presence of this flag indicates that we should run in language server mode.
    #[clap(long)]
    extension_root: Option<String>,

    // The following flags only apply in CLI mode.

    // Verify a single module.
    // Can be either a filename or a module name.
    #[clap()]
    target: Option<String>,

    // Create a dataset from the prover logs.
    #[clap(long)]
    dataset: bool,

    // If --full is set, ignore the cache and do a full reverify.
    #[clap(long)]
    full: bool,

    // Use the cache, but only for the filtered prover, not for hash checking.
    // Incompatible with --full.
    #[clap(long)]
    filtered: bool,
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

    // Run the verifier.
    let mode = if args.full {
        if args.filtered {
            println!("--full and --filtered are incompatible.");
            std::process::exit(1);
        }
        VerifierMode::Full
    } else if args.filtered {
        VerifierMode::Filtered
    } else {
        VerifierMode::Standard
    };
    let verifier = Verifier::new(mode, args.target, args.dataset);
    verifier.run();
}

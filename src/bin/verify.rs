// Verifies an acorn file, or the whole project.
//
// This is the CLI equivalent of what the IDE runs when you save.
//
// By default, this will verify every module in the project, and output verification metrics.
// It's a good idea to run this for complicated changes.
//
// Try:
//   cargo build --release --bin=verify; time ~/acorn/target/release/verify

use acorn::verifier::{Verifier, VerifierMode};
use clap::Parser;

#[derive(Parser)]
struct Args {
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

    let mode = if args.full {
        if args.filtered {
            println!("--full and --filtered are incompatible.");
            return;
        }
        VerifierMode::Full
    } else if args.filtered {
        VerifierMode::Filtered
    } else {
        VerifierMode::Standard
    };
    
    let current_dir = match std::env::current_dir() {
        Ok(dir) => dir,
        Err(e) => {
            println!("Error getting current directory: {}", e);
            std::process::exit(1);
        }
    };
    
    let verifier = Verifier::new(current_dir, mode, args.target, args.dataset);
    if let Err(e) = verifier.run() {
        println!("{}", e);
        std::process::exit(1);
    }
}

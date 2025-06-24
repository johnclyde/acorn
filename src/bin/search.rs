// Searches for a proof for a particular goal in an acorn file.
//
// This is the CLI equivalent of what the IDE runs when you click on a proposition.
//
// The user can pass either:
// - A line number (for backwards compatibility)
// - A theorem name (new feature)
//
// Don't forget that the release build is much faster than debug.

const USAGE: &str = "Usage: cargo run --release --bin=search <module name> <line number or theorem name>

Examples:
  cargo run --release --bin=search my_module 42         # Search at line 42
  cargo run --release --bin=search my_module my_theorem  # Search for theorem named 'my_theorem'";

use acorn::searcher::Searcher;
use acorn::verifier::ProverMode;

#[tokio::main]
async fn main() {
    // Parse command line arguments
    let mut args = std::env::args().skip(1);
    let module_name = match args.next() {
        Some(name) => name,
        None => {
            eprintln!("{}", USAGE);
            std::process::exit(1);
        }
    };
    
    let target = match args.next() {
        Some(target) => target,
        None => {
            eprintln!("{}", USAGE);
            std::process::exit(1);
        }
    };

    let current_dir = match std::env::current_dir() {
        Ok(dir) => dir,
        Err(e) => {
            eprintln!("Error getting current directory: {}", e);
            std::process::exit(1);
        }
    };

    // Try to parse as a line number first
    let searcher = match target.parse::<u32>() {
        Ok(line_number) => {
            // It's a line number (backwards compatibility)
            Searcher::new_by_line(current_dir, ProverMode::Full, module_name, line_number)
        }
        Err(_) => {
            // It's a theorem name
            Searcher::new_by_name(current_dir, ProverMode::Full, module_name, target)
        }
    };
    
    if let Err(e) = searcher.run() {
        eprintln!("{}", e);
        std::process::exit(1);
    }
}

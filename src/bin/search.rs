// Searches for a proof for a particular goal in an acorn file.
//
// This is the CLI equivalent of what the IDE runs when you click on a proposition.
//
// The user passes the line in externally-visible line number, which starts at 1.
// Don't forget that the release build is much faster than debug.

const USAGE: &str = "cargo run --release --bin=search <module name> <line number>";

use acorn::searcher::Searcher;

#[tokio::main]
async fn main() {
    // Parse command line arguments
    let mut args = std::env::args().skip(1);
    let module_name = args.next().expect(USAGE);
    let line_number = args.next().expect(USAGE).parse::<u32>().expect(USAGE);

    let current_dir = match std::env::current_dir() {
        Ok(dir) => dir,
        Err(e) => {
            eprintln!("Error getting current directory: {}", e);
            std::process::exit(1);
        }
    };

    let searcher = Searcher::new(current_dir, module_name, line_number);
    if let Err(e) = searcher.run() {
        eprintln!("{}", e);
        std::process::exit(1);
    }
}

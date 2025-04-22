// Verifies an acorn file, or the whole project.
//
// This is the CLI equivalent of what the IDE runs when you save.
//
// By default, this will verify every module in the project, and output verification metrics.
// It's a good idea to run this for complicated changes.
//
// Try:
//   cargo build --release --bin=verify; time ~/acorn/target/release/verify

use std::path::PathBuf;

use acorn::project::Project;
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

    // Use the cache normally if --cache is set.
    // By default, the cache is not used.
    #[clap(long)]
    cache: bool,

    // Use the cache, but only for the filtered prover, not for hash checking.
    // Incompatible with --cache.
    #[clap(long)]
    filtered: bool,
}

#[tokio::main]
async fn main() {
    let args = Args::parse();

    let use_cache = args.cache || args.filtered;
    if args.cache && args.filtered {
        println!("--cache and --filtered are incompatible.");
        return;
    }

    let mut project = Project::new_local(use_cache).unwrap();
    if args.filtered {
        project.check_hashes = false;
    }

    if let Some(target) = args.target {
        if target.ends_with(".ac") {
            // Looks like a filename
            let path = PathBuf::from(&target);
            if !project.add_target_by_path(&path) {
                println!("File not found: {}", target);
                return;
            }
        } else {
            if !project.add_target_by_name(&target) {
                println!("Module not found: {}", target);
                return;
            }
        }
    } else {
        project.add_all_targets();
    }

    // Set up the builder
    let mut builder = project.builder(|event| {
        if let Some(m) = event.log_message {
            if let Some(diagnostic) = event.diagnostic {
                println!(
                    "{}, line {}: {}",
                    event.module,
                    diagnostic.range.start.line + 1,
                    m
                );
            } else {
                println!("{}", m);
            }
        }
    });
    builder.log_when_slow = true;
    if args.dataset {
        builder.create_dataset();
    }

    // Build
    project.build(&mut builder);
    builder.print_stats();
    if let Some(dataset) = builder.dataset {
        dataset.save();
    }

    if args.filtered && builder.searches_full > 0 {
        println!("\nWarning: the filtered prover was not able to handle all goals.");
        std::process::exit(1);
    }
}

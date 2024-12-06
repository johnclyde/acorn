// Verifies an acorn file, or the whole project.
//
// This is the CLI equivalent of what the IDE runs when you save.
//
// Try:
//   cargo build --release --bin=verify; time ~/acorn/target/release/verify

use std::path::PathBuf;

use acorn::builder::Builder;
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
}

#[tokio::main]
async fn main() {
    let mut project = Project::new_local().unwrap();

    let args = Args::parse();
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
    let mut builder = Builder::new(|event| {
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
}

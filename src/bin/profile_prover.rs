// A representative run of the prover, to use for profiling.
// To profile using samply:
//
//   cargo build --bin=profile_prover --profile=fastdev
//   samply record target/fastdev/profile_prover

use acorn::project::Project;
use acorn::verifier::ProverMode;

fn main() {
    let current_dir = std::env::current_dir().unwrap();
    for _ in 0..10 {
        let mut project = Project::new_local(&current_dir, ProverMode::Full).unwrap();
        project.add_target_by_name("nat").expect("Failed to add nat target");
        project.add_target_by_name("nat_gcd").expect("Failed to add nat_gcd target");
        project.add_target_by_name("int").expect("Failed to add int target");
        let mut logger = project.builder(|event| {
            if let Some(m) = event.log_message {
                println!("{}", m);
            }
            if let Some((d, t)) = event.progress {
                if d == t {
                    println!("{}/{} done", d, t);
                }
            }
        });
        project.build(&mut logger);
    }
}

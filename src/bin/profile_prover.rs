// A representative run of the prover, to use for profiling.
// To profile using samply:
//
//   cargo build --bin=profile_prover --profile=fastdev
//   samply record target/fastdev/profile_prover

use acorn::builder::Builder;
use acorn::project::Project;

fn main() {
    for _ in 0..10 {
        let mut project = Project::new_local().unwrap();
        assert!(project.add_target_by_name("nat"));
        assert!(project.add_target_by_name("nat_gcd"));
        assert!(project.add_target_by_name("int"));
        let mut logger = Builder::new(project.build_cache.clone(), |event| {
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

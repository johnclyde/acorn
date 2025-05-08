// The Acorn CLI.
// You can run a language server, verify a file, or verify the whole project.

use acorn::server::{run_server, ServerArgs};
use clap::Parser;

#[derive(Parser)]
struct Args {
    // The root folder the user has open
    #[clap(long)]
    workspace_root: Option<String>,

    // The root folder of the extension.
    // Presence of this flag indicates that we should run in language server mode.
    #[clap(long)]
    extension_root: Option<String>,
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

    todo!("run the verifier.");
}

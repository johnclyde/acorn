# acorn

The core implementation of the Acorn language.

## Who should use this repository?

The primary way to use Acorn is through the VS Code extension. For that, you don't need to use this repository.

If you are making changes to the theorem prover itself, or to the UI of the VS Code extension, you
do need to use this repository.

## Installing acorn from source

Fork this and `acorn-library`, then clone them to your development machine.

These instructions will assume you have this repository cloned in `~/acorn` and the library cloned
in `~/acorn-library`.

Fork this repository, then clone the fork to your local machine. Install rust and node, then verify tests
pass locally:

```bash
cd ~/acorn
cargo test -q
```

If there are any errors, submit an issue.

Then, install dependencies for the VS Code extension.

```bash
cd ~/acorn/vscode/extension
npm install
cd ~/acorn/vscode/info
npm install
```

## Running the prover

Open up this repository in VS Code. You can open this exact file, if you like. You'll use this instance
of VS Code to make changes to the prover and the extension.

Hit F5. This will open up a new VS Code window. Use this window to open `~/acorn-library`. You'll use this instance of VS Code to test our your local changes.

## Dependencies for cross-platform release

You can build for both Linux and Mac from Linux.
You will need these dependencies.

All commands are run from `~/acorn`.

Mac support:

Download a [Mac OS X SDK](https://github.com/joseluisq/macosx-sdks)
somewhere, then symlink to it from `~/macsdk`.

```bash
rustup target add aarch64-apple-darwin
snap install zig --classic --beta
cargo install --locked cargo-zigbuild
```

TODO: explain how Windows works

## Creating new releases

When we create a new release, we release a new language server, and then a new VSCode extension.

All commands are run from `~/acorn`.

1. Bump the version using the `version.py` tool.

   ```bash
   ./python/version.py 0.0.1
   ```

2. Do the cross-platform build.

   ```bash
   ./crossbuild.sh
   ```

3. Make a tag for the new language server release, "v" plus the version.

   First, make sure all your local changes are merged upstream, so that the tag picks up the right files.

   Then:

   ```bash
   git tag v0.0.1
   git push upstream v0.0.1
   ```

4. Write a release description [here](https://github.com/acornprover/acorn/releases/new).

5. Publish the language server binaries to GitHub

   ```bash
   ./publish.sh
   ```

   If you've already published the binaries for a tag and want to update them, run

   ```bash
   ./publish.sh --clobber
   ```

6. Publish the VS Code extension

   ```bash
   ~/acorn$ cd vscode/extension
   ~/acorn/vscore/extension$ vsce package
   ```

   (This doesn't publish the extension, it just creates it.)

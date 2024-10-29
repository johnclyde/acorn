# acorn

The core implementation of the Acorn language.

# Who should use this repository?

The primary way to use Acorn is through the VS Code extension. For that, you don't need to use this repository.

If you are making changes to the theorem prover itself, or to the UI of the VS Code extension, you
do need to use this repository.

# Installing acorn from source

Fork this and `acorn-library`, then clone them to your development machine.

These instructions will assume you have this repository cloned in `~/acorn` and the library cloned
in `~/acorn-library`.

Fork this repository, then clone the fork to your local machine. Install rust and node, then verify tests
pass locally:

```
cd ~/acorn
cargo test -q
```

If there are any errors, submit an issue.

Then, install dependencies for the VS Code extension.

```
cd ~/acorn/vscode/extension
npm install
cd ~/acorn/vscode/search
npm install
```

# Running the prover

Open up this repository in VS Code. You can open this exact file, if you like. You'll use this instance
of VS Code to make changes to the prover and the extension.

Hit F5. This will open up a new VS Code window. Use this window to open `~/acorn-library`. You'll use this instance of VS Code to test our your local changes.

# Dependencies for cross-platform release

To create new releases, you need to build for all supported platforms, which you can do from Linux.
You will need these dependencies.

All commands are run from `~/acorn`.

Windows support:

```
rustup target add x86_64-pc-windows-msvc
cargo install xwin
xwin --accept-license splat --output ~/.xwin

# A workaround for case insensitivity that xwin for some reason doesn't autofix
cp ~/.xwin/sdk/lib/um/x86_64/directml.lib ~/.xwin/sdk/lib/um/x86_64/DirectML.lib
cp ~/.xwin/sdk/lib/um/x86_64/pathcch.lib ~/.xwin/sdk/lib/um/x86_64/PathCch.lib
```

Mac support:

Download a [Mac OS X SDK](https://github.com/joseluisq/macosx-sdks)
somewhere, then symlink to it from `~/macsdk`.

```
rustup target add aarch64-apple-darwin
snap install zig --classic --beta
cargo install --locked cargo-zigbuild
```

It would probably be better to do these builds from a continuous integration service, rather than
cross-compiling.

# Creating new releases

When we create a new release, we release a new language server, and then a new VSCode extension.

All commands are run from `~/acorn`.

1. Bump the version using the `version.py` tool.

```
./python/version.py 0.0.1
```

2. Do the cross-platform build.

```
./crossbuild.sh
```

3. Make a tag for the new language server release, "v" plus the version.

First, make sure all your local changes are merged upstream, so that the tag picks up the right files.

Then:

```
git tag v0.0.1
git push upstream v0.0.1
```

4. Write a release description [here](https://github.com/acornprover/acorn/releases/new).

5. Publish the language server binaries to GitHub

```
./publish.sh
```

If you've already published the binaries for a tag and want to update them, run

```
./publish.sh --clobber
```

6. Publish the VS Code extension

```
~/acorn$ cd vscode/extension
~/acorn/vscore/extension$ vsce package
```

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

# Creating new releases

When we create a new release, we usually need to release both a new language server and a new VSCode extension. If there are only changes to the extension, we don't need to release a new language server. But if there are only changes to the language server, we do need to release a new extension, so that clients
know to update their language server.

1. Bump the version in `vscode/extension/package.json`.

2. Make a tag for the new language server release, "v" plus the version.

```
~/acorn$ git tag v0.0.1
~/acorn$ git push upstream v0.0.1
```

3. Write a release description [here](https://github.com/acornprover/acorn/releases/new).

4. TODO

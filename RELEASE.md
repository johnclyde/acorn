# The release process

To do a full release, you'll need to do the Linux/Mac build on a Linux machine, and then
GitHub Actions will handle the Windows build.

## Linux/Mac release builds

You can build for both Linux and Mac, from Linux.
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

## The whole release process

When we create a new release, we release a new language server, and then a new VSCode extension.

All commands are run from `~/acorn`.

1. Before you release, consider whether you also want to update the built-in copy of acornlib. If you do:

   ```
   cd vscode/extension/acornlib
   git pull
   cd ../../..
   ```

   Then check in the updated submodule reference and merge it upstream.

2. Bump the version using the `version.py` tool. Or you can set it manually for bigger version changes.

   ```bash
   ./python/version.py bump
   ```

   Commit all changes and merge them upstream with `git push upstream master`.

3. Do the cross-platform build.

   ```bash
   ./crossbuild.sh
   ```

4. Make a tag for the new language server release, "v" plus the version. Then push it upstream.

   ```bash
   ./python/tag.py
   ```

   or to do it step by step:

   ```bash
   git tag v0.0.1
   git push upstream v0.0.1
   ```

   This should automatically trigger a Windows release build of the language server.

   Check that the [GitHub Actions](https://github.com/acornprover/acorn/actions) succeed.
   They might take 7-8 minutes. At the end of it, a GitHub release should be created automatically.

5. Edit the release description [here](https://github.com/acornprover/acorn/releases).

6. Upload the Linux and Mac language server binaries to GitHub

   ```bash
   ./upload.sh
   ```

   If you've already published the binaries for a tag and want to update them, run

   ```bash
   ./upload.sh --clobber
   ```

   This also uploads the extension to GitHub. If you just want to test a new extension, you can stop here. On the test machine, get the `.vsix` file from the GitHub release, and
   install that into VS Code with:

   ```bash
   code --install-extension acorn-<version>.vsix
   ```

7. Publish the extension to the Visual Studio Marketplace.

   From the acorn/vscode/extension directory, after uploading:

   ```bash
   cd vscode/extension
   vsce publish
   ```

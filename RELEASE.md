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

1. Bump the version using the `version.py` tool.

   ```bash
   ./python/version.py 0.0.1
   ```

   Commit all changes and merge them upstream.

2. Do the cross-platform build.

   ```bash
   ./crossbuild.sh
   ```

3. Make a tag for the new language server release, "v" plus the version.

   Then:

   ```bash
   git tag v0.0.1
   git push upstream v0.0.1
   ```

   This should automatically trigger a Windows release build of the language server.

   Check that the [GitHub Action](https://github.com/acornprover/acorn/actions) succeeds.
   It might take 7-8 minutes.

4. Write a release description [here](https://github.com/acornprover/acorn/releases/new).

5. Upload the language server binaries to GitHub

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

6. Publish the extension to the Visual Studio Marketplace.

   From the acorn/vscode/extension directory, after uploading:

   ```bash
   vsce publish
   ```

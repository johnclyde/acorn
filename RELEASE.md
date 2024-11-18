# The release process

To do a full release, you'll need both a Linux machine and a Windows machine. Yes, it would
be nice to do this all via GitHub action.

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

## Windows release builds

Windows builds only work on Windows.

For releases we need to statically link the Acorn language server.

Download `onnxruntime` to your home directory, then build it from the `onnxruntime` directory with:

```powershell
./build.bat --config Release --parallel --skip_tests --enable_msvc_static_runtime --cmake_generator "Visual Studio 17 2022"
```

Then do the release build from the `acorn` directory with:

```powershell
./winbuild.bat
```

## The whole release process

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

6. Upload the Windows binary to GitHub

   Follow the instructions in the previous section to do a Windows release build. It will give you a `gh` command to run to publish the resulting binary to GitHub.

7. Publish the extension to the Visual Studio Marketplace.

   TODO: do this, and explain this, and link the extension from the readme.

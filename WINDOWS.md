## Windows release builds

Usually this should happen automatically through GitHub Actions. These notes are to do it yourself.

Windows builds only work on Windows.

Use the Developer PowerShell that ships with Visual Studio. If you use the wrong shell, the script won't be able to find all the tools it needs.

Download `onnxruntime` to your home directory, then build it from the `onnxruntime` directory with:

```powershell
./build.bat --config Release --parallel --skip_tests --enable_msvc_static_runtime --cmake_generator "Visual Studio 17 2022"
```

Then do the release build from the `acorn` directory with:

```powershell
./winbuild.bat
```

The release build should statically link the Acorn language server.

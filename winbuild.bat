@echo off
setlocal

if /I not "%~dp0" == "%cd%\" (
    echo Run this from the acorn directory.
    exit /b 1
) else (
    echo Good work, you ran this script from the correct directory.
)

cmd /c "exit /b 1"

set "ORT_LIB_LOCATION=%USERPROFILE%\onnxruntime\build\Windows\Release"

if not exist "%ORT_LIB_LOCATION%\" (
    echo Please build onnxruntime locally before running this script.
    exit /b 1
)

echo Building...
cargo build --release --bin acornserver --target x86_64-pc-windows-msvc || exit /b

rem Set the path to the built binary
set "buildBin=.\target\x86_64-pc-windows-msvc\release\acornserver.exe"

echo DLLs used by the acornserver binary:
dumpbin /imports "%buildBin%" | findstr /i ".dll"

if not exist "files\release" mkdir "files\release"

set /p version=<VERSION
set "tag=v%version%"

rem Set the destination path with the versioned name
set "releaseBin=files\release\acornserver-%version%-win32-x64.exe"

copy "%buildBin%" "%releaseBin%"

echo Build for %tag% successful.
echo To upload to GitHub, run:
echo gh release upload %tag% %releaseBin% [--clobber]
@echo off

if /I not "%~dp0" == "%cd%\" (
    echo Run this from the acorn directory.
    exit /b 1
) else (
    echo Good work, you ran this script from the correct directory.
)

setlocal enabledelayedexpansion
cmd /c "exit /b 1"

set "ORT_LIB_LOCATION=%USERPROFILE%\onnxruntime\build\Windows\Release"

if not exist "%ORT_LIB_LOCATION%\" (
    echo Please build onnxruntime locally before running this script.
    exit /b 1
)

echo Building...
cargo build --release --bin acornserver --target x86_64-pc-windows-msvc || exit /b

REM Path to the binary
set "binary=.\target\x86_64-pc-windows-msvc\release\acornserver.exe"

echo DLLs used by the acornserver binary:
dumpbin /imports "%binary%" | findstr /i ".dll"
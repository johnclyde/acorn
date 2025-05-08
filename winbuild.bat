@echo off
setlocal

if /I not "%~dp0" == "%cd%\" (
    echo Run this from the acorn directory.
    exit /b 1
) else (
    echo Good work, you ran this script from the correct directory.
)

cmd /c "exit /b 1"

if not defined ORT_LIB_LOCATION (
    echo no ORT_LIB_LOCATION defined. inferring
    set "ORT_LIB_LOCATION=%USERPROFILE%\onnxruntime\build\Windows\Release"
)

if not exist "%ORT_LIB_LOCATION%\" (
    echo Checked ORT_LIB_LOCATION - "%ORT_LIB_LOCATION%" - but found no onnxruntime build.
    echo Please build onnxruntime locally before running this script.
    exit /b 1
)

echo Building...
cargo build --release --bin acorn --target x86_64-pc-windows-msvc || exit /b

rem Set the path to the built binary
set "buildBin=.\target\x86_64-pc-windows-msvc\release\acorn.exe"

rem Commented out due to trouble using dumpbin in GitHub Actions.
rem echo DLLs used by the acorn binary:
rem dumpbin /imports "%buildBin%" | findstr /i ".dll"

if not exist "files\release" mkdir "files\release"

set /p version=<VERSION
set "tag=v%version%"

if "%tag%" neq "%TAG%" (
    echo ERROR: the tag "%tag%" in the code does not match the tag "%TAG%" that triggered this build.
    exit /b 1
)

rem Set the destination path with the versioned name
set "releaseBin=files\release\acorn-%version%-win32-x64.exe"

copy "%buildBin%" "%releaseBin%"

echo Build for %tag% successful.

echo Creating release %tag% on GitHub
gh release create %tag% --notes "Automated release for version %tag%"
echo Uploading %releaseBin% to GitHub
gh release upload %tag% %releaseBin%
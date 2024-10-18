#!/bin/bash
# Build the language server across multiple platforms.

# Exit immediately if any command fails
set -ex

echo "Building for Linux x64..."
RUSTFLAGS="-C target-feature=+crt-static" \
    cargo build --release --bin acornserver --target x86_64-unknown-linux-gnu 

# Check it's statically linked
ldd target/x86_64-unknown-linux-gnu/release/acornserver 2>&1 | grep "statically linked" \
    || (echo "linking error" && exit 1)

echo "Building for Windows x64..."
cargo build --release --bin acornserver --target x86_64-pc-windows-msvc

# Check it's statically linked
ldd target/x86_64-pc-windows-msvc/release/acornserver.exe 2>&1 | grep "not a dynamic exe" \
    || (echo "linking error" && exit 1)

echo "Building for macOS..."
SDKROOT=~/macsdk \
    cargo zigbuild --release --bin acornserver --target aarch64-apple-darwin
echo "TODO: silence the warning that strip failed"

echo "Crossbuild successful."

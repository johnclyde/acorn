#!/bin/bash
# Build the language server across multiple platforms.

# Exit immediately if any command fails
set -ex

# Statically link for distribution
export RUSTFLAGS="-C target-feature=+crt-static"

echo "Building for Linux x64..."
cargo build --release --bin acornserver --target x86_64-unknown-linux-gnu 

# Double check it's statically linked
ldd target/x86_64-unknown-linux-gnu/release/acornserver 2>&1 | grep "statically linked" \
    || (echo "error, dynamically linked" && exit 1)

echo "Exiting early."
exit 0

echo "Building for Windows x64..."
cargo build --release --bin acornserver --target x86_64-pc-windows

echo "Building for macOS ARM..."
cargo build --release --bin acornserver --target aarch64-apple-darwin

echo "All builds completed successfully."
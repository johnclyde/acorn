#!/bin/bash
# Build the language server across multiple platforms.

# Exit immediately if any command fails
set -ex

echo "Building for Linux x64..."
RUSTFLAGS="-C target-feature=+crt-static" \
    cargo build --release --bin acorn --target x86_64-unknown-linux-gnu 

# Check it's statically linked
ldd target/x86_64-unknown-linux-gnu/release/acorn 2>&1 | grep "statically linked" \
    || (echo "linking error" && exit 1)

# Note: I had to link /home/username/macsdk/home/username/macsdk to /home/username/macsdk
# as a crazy workaround.
echo "Building for macOS..."
SDKROOT=$HOME/macsdk cargo zigbuild --release --bin acorn --target aarch64-apple-darwin

echo "Crossbuild successful."

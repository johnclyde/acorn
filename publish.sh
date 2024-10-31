#!/bin/bash
# Publish the language server binaries and extension to GitHub.

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
current_dir="$(pwd)"
[[ $script_dir == $current_dir ]] || { echo "Run this script from the repository root."; exit 1; }

# Exit immediately if any command fails
set -ex

# We always want an up-to-date build, and it's cached so it won't slow us down to redo this.
./crossbuild.sh

# Default value: empty
CLOBBER=""

# Parse CLI arguments
for arg in "$@"; do
  if [ "$arg" == "--clobber" ]; then
    echo "clobbering."
    CLOBBER="--clobber"
    break
  fi
done

VERSION=`cat VERSION`
[[ $VERSION =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]] || { echo "bad version"; exit 1; }
TAG="v$VERSION"

# Map between the Node and Rust ways of describing platforms
declare -A MAP=(
  ["linux-x64"]="x86_64-unknown-linux-gnu"
  ["darwin-arm64"]="aarch64-apple-darwin"
)

# Use files/release for renaming
[[ -d files ]] || { echo "missing files directory"; exit 1; }
mkdir -p files/release
rm -f files/release/*

for key in "${!MAP[@]}"; do
    if [[ $key == *"win32"* ]]; then
        suffix=".exe"
    fi
    node=$key
    remote_name="acornserver-$VERSION-$node$suffix"
    rust=${MAP[$node]}
    local_name="target/$rust/release/acornserver$suffix"
    [[ -f $local_name ]] || { echo "missing $local_name"; exit 1; }
    cp $local_name files/release/$remote_name
    gh release upload $TAG files/release/$remote_name $CLOBBER
done

# Be sure to rebuild the info view
cd vscode/info
npm run build
cd ../..

# Rebuild the extension and release the vsix
cd vscode/extension
npm run build
vsce package
gh release upload $TAG acorn-$VERSION.vsix $CLOBBER
cd ../..
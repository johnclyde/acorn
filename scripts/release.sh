#!/bin/bash
# Does the whole release process.

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
project_root="$(cd "$script_dir/.." && pwd)"
current_dir="$(pwd)"
[[ $current_dir == $project_root ]] || { echo "Run this script from the repository root."; exit 1; }

# Exit immediately if any command fails
set -ex

# Handle version update
if [ $# -eq 1 ]; then
    # Use provided version
    VERSION=$1
    ./python/version.py "$VERSION"
else
    # Bump version and capture the new version
    VERSION=$(./python/version.py bump | grep "version:" | awk '{print $2}')
fi

# Verify version format (number.number.number)
if ! [[ $VERSION =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
    echo "Error: Invalid version format: $VERSION"
    exit 1
fi

echo "Releasing version: $VERSION"
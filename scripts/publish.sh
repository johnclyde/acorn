#!/bin/bash
# Publish the VS Code extension

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
project_root="$(cd "$script_dir/.." && pwd)"
current_dir="$(pwd)"
[[ $current_dir == $project_root ]] || { echo "Run this script from the repository root."; exit 1; }

# Exit immediately if any command fails
set -ex

cd vscode/extension
# Delete all existing .vsix files before publishing
rm -f *.vsix
vsce publish
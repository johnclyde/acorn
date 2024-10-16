#!/usr/bin/env -S uv run

# Run version.py to show the current version.
# Run version.py <new_version> to change the version.

import os
import sys


def looks_like_version_string(s):
    return s.count(".") == 2 and all(x.isdigit() for x in s.split("."))


def main():
    # Find cargo.toml
    python_dir = os.path.dirname(os.path.abspath(__file__))
    acorn_dir = os.path.dirname(python_dir)
    cargo_toml_path = os.path.join(acorn_dir, "Cargo.toml")
    cargo_toml = open(cargo_toml_path).read()

    # Find package.json
    vscode_dir = os.path.join(acorn_dir, "vscode")
    extension_dir = os.path.join(vscode_dir, "extension")
    package_json_path = os.path.join(extension_dir, "package.json")
    package_json = open(package_json_path).read()

    # Check what the current versions are
    cargo_version = cargo_toml.split('version = "')[1].split('"')[0]
    package_version = package_json.split('"version": "')[1].split('"')[0]
    if not looks_like_version_string(cargo_version):
        raise Exception("can't find version in Cargo.toml")
    if not looks_like_version_string(package_version):
        raise Exception("can't find version in package.json")
    if cargo_version != package_version:
        raise Exception(
            f"Cargo.toml ({cargo_version}) and package.json ({package_version}) versions don't match"
        )
    old_version = cargo_version
    print("version:", old_version)

    if len(sys.argv) < 2:
        return

    new_version = sys.argv[1]
    if not looks_like_version_string(new_version):
        raise Exception(f"invalid version string: {new_version}")

    # Update Cargo.toml
    old_cargo_str = f'version = "{old_version}"'
    assert cargo_toml.count(old_cargo_str) == 1
    cargo_toml = cargo_toml.replace(old_cargo_str, f'version = "{new_version}"')
    with open(cargo_toml_path, "w") as f:
        f.write(cargo_toml)

    # Update package.json
    old_package_str = f'"version": "{old_version}"'
    assert package_json.count(old_package_str) == 1
    package_json = package_json.replace(old_package_str, f'"version": "{new_version}"')
    with open(package_json_path, "w") as f:
        f.write(package_json)

    print("changed to:", new_version)


if __name__ == "__main__":
    main()

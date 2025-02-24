# Acorn Development Guide

Note - this is AI-generated for the use of the Claude CLI tool. Humans should probably ignore it, in favor
of the other, more accurate documentation.

## Build/Test Commands

- Full test suite: `cargo test -q`
- Run single test: `cargo test -q test_name`
- Run specific test file: `cargo test -q --test environment_test`
- Build: `cargo build`
- Run: `cargo run` (or specific binary `cargo run --bin acornserver`)

## Code Style Guidelines

- Use Rust 2021 edition idioms
- Variable names: snake_case
- Type names: PascalCase
- Function params with explicit types: `param: Type`
- Axioms/theorems: use descriptive names that indicate what they prove
- Error handling: use Result<T, E> with proper error propagation
- Testing: each language feature needs both an environment test and a prover test
- When adding new features, follow existing patterns for similar constructs
- For language features, make sure to test both valid and invalid inputs

## Project Structure

- `/src` - Core Rust implementation
- `/tests` - Test files (environment_test.rs, prover_test.rs)
- `/vscode` - VS Code extension and assistant interface
- `/python` - Training scripts for the model

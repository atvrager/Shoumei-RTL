# Shoumei-RTL Bazel Migration

This document records the status and roadmap for building Shoumei-RTL with `rules_lean`.

## Status

- **Lean Toolchain**: Pinned to Lean `v4.34.1` via `lean-toolchain`.
- **Core Library (`//lean:shoumei`)**: All 285 Lean modules compile in parallel across individual sandboxed Bazel actions.
- **Code Generator (`//:generate_all`)**: Compiles to a 136 MB static ELF binary via `lean_binary`.
- **Co-enhancement**: Identified and fixed import parsing in `rules_lean` ([commit 2cf9d00](https://github.com/atvrager/rules_lean/commit/2cf9d00)), ignoring block comments (`/- ... -/`) and string literals.

## Commands

```bash
# Build the entire Lean library (285 modules in parallel)
bazel build //lean:shoumei

# Build the native code generation binary
bazel build //:generate_all

# Run code generator
./bazel-bin/generate_all
```

## Generated Artifacts

Executing `generate_all` emits hardware designs:

| Directory | File Count | Content |
| --- | --- | --- |
| `output/sv-from-lean/` | 237 `.sv` files | Hierarchical SystemVerilog modules |
| `output/sv-netlist/` | 237 `.sv` files | Flat gate-level netlists |
| `output/sv-asap7/` | 81 `.sv` files | ASAP7 cell library mappings |
| `output/sv-gf180/` | 81 `.sv` files | GF180MCU cell library mappings |
| `output/cpp_sim/` | 237 `.h` files | Cycle-accurate C++ simulation models |

## Open Work

1. **Hermetic RTL Generation**:
   - `generate_all` currently writes directly to in-tree `output/`.
   - Goal: Wrap code generation in a Bazel rule (or `genrule`) that emits declared output files into `bazel-out/`.
   - Prevent side effects in the source workspace.

2. **Simulation and Lint Targets**:
   - Slang lint: Declare a test target running `slang` on the emitted SystemVerilog.
   - Verilator: Declare `cc_test` or `sh_test` targets compiling and running emitted C++ simulation against testbench ELFs.
   - Arcilator / CIRCT flow: Package CIRCT/firtool dependencies into Bazel toolchains.

3. **Proof Audits**:
   - Add `lean_axiom_test` targets for key correctness theorems (e.g., `fullAdder_correct`, `alu_correct`, `shoumei_soc_correct`).
   - Gate builds on zero axioms (`allowed_axioms = ["propext", "Classical.choice", "Quot.sound"]`).

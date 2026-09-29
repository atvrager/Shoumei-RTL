# Shoumei-RTL Bazel Migration

This document records the status and roadmap for building Shoumei-RTL with `rules_lean`.

## Status

- **Lean Toolchain**: Pinned to Lean `v4.34.1` via `lean-toolchain`.
- **Core Library (`//lean:shoumei`)**: All 285 Lean modules compile in parallel across individual sandboxed Bazel actions.
- **Code Generator (`//:generate_all`)**: Compiles to a 136 MB static ELF binary via `lean_binary`.
- **Hermetic RTL Generation (`//:rtl`, `//:sv`)**: Sandboxed Bazel rule executes `generate_all` inside the build sandbox, emitting declared artifacts into `bazel-out/` without polluting the source workspace.
- **Structural Linter Test (`//:lint_structural_test`)**: Sandboxed test target validating all 238 emitted SystemVerilog modules against Synopsys DC NXT LINT-31/32 rules.
- **RISC-V Opcode Parsing (`//:instr_dict`)**: Hermetically built via Bazel from `third_party/riscv-opcodes` definitions.
- **Co-enhancement**: Identified and fixed import parsing in `rules_lean` ([commit 2cf9d00](https://github.com/atvrager/rules_lean/commit/2cf9d00)), ignoring block comments (`/- ... -/`) and string literals.

## Commands

```bash
# Build the entire Lean library (285 modules in parallel)
bazel build //lean:shoumei

# Generate primary SystemVerilog RTL (output lands in bazel-bin/rtl_raw_sv)
bazel build //:sv

# Generate all output formats (SV, netlist, techmaps, C++ sim, testbenches)
bazel build //:rtl

# Run native structural linting on generated SystemVerilog
bazel test //:lint_structural_test
```

## Generated Artifacts

Executing `bazel build //:rtl` emits hardware designs into `bazel-bin/`:

| Target | Output Artifact | Count | Description |
| --- | --- | --- | --- |
| `//:sv` | `bazel-bin/rtl_raw_sv/` | 239 files | Hierarchical SystemVerilog modules + `filelist.f` |
| `//:sv_netlist` | `bazel-bin/rtl_raw_netlist/` | 238 files | Flat gate-level netlists + `filelist.f` |
| `//:sv_asap7` | `bazel-bin/rtl_raw_asap7/` | 82 files | ASAP7 cell library mappings + `filelist.f` |
| `//:sv_gf180` | `bazel-bin/rtl_raw_gf180/` | 82 files | GF180MCU cell library mappings + `filelist.f` |
| `//:sv_sec` | `bazel-bin/rtl_raw_sec/` | 11 files | SEC miters and TCL scripts |
| `//:cpp_sim` | `bazel-bin/rtl_raw_cpp_sim/` | 477 files | Cycle-accurate C++ simulation models (`.h` / `.cpp`) |
| `//:testbench` | `bazel-bin/rtl_raw_testbench/` | 9 files | Emitted testbenches, drivers, and setups |

## Open Work

1. **Simulation and Synthesis Targets**:
   - Slang lint: Declare a test target running `slang` on the emitted SystemVerilog.
   - Verilator: Declare `cc_test` targets compiling and running emitted C++ simulation against testbench ELFs.
   - Yosys synthesis: Declare actions targeting GF180 and ASAP7 cell synthesis.

2. **Proof Audits**:
   - Add `lean_axiom_test` targets for key correctness theorems (e.g., `fullAdder_correct`, `alu_correct`, `shoumei_soc_correct`).
   - Gate builds on zero unapproved axioms (`allowed_axioms = ["propext", "Classical.choice", "Quot.sound"]`).

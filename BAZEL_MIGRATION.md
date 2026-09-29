# Shoumei-RTL Bazel Migration

This document records the status and roadmap for building Shoumei-RTL with `rules_lean`.

## Status

- **Lean Toolchain**: Pinned to Lean `v4.34.1` via `lean-toolchain`.
- **Core Library (`//lean:shoumei`)**: All 285 Lean modules compile in parallel across individual sandboxed Bazel actions.
- **Code Generator (`//:generate_all`)**: Compiles to a 136 MB static ELF binary via `lean_binary`.
- **Hermetic RTL Generation (`//:rtl`, `//:sv`)**: Sandboxed Bazel rule executes `generate_all` inside the build sandbox, emitting declared artifacts into `bazel-out/` without polluting the source workspace.
- **Structural Linter Test (`//:lint_structural_test`)**: Sandboxed test target validating all 238 emitted SystemVerilog modules against Synopsys DC NXT LINT-31/32 rules.
- **RISC-V Opcode Parsing (`//:instr_dict`)**: Hermetically built via Bazel from `third_party/riscv-opcodes` definitions.
- **Spike Simulator (`//third_party:spike_lib`)**: Hermetically compiled via `rules_foreign_cc`, emitting `libriscv.so`, `libfesvr.a`, `libdisasm.a`, and headers.
- **Support C++ Libraries**:
  - `//testbench:elf_loader`: ELF binary loader.
  - `//testbench:spike_oracle`: Spike ISA golden reference driver.
  - `//physical/sim-dpi:sram_dpi`: DPI-C backing store for SRAM models.
- **Verilator RTL Compilation (`//testbench:vtb_cpu`)**: Flat compilation of all 239 generated SystemVerilog modules and `tb_cpu.sv` via `rules_verilator`.
- **Cosimulation Executable (`//testbench:cosim_shoumei`)**: Full lockstep cosimulation binary comparing RTL vs Spike via RVVI-TRACE interface.
- **Direct Simulation Executable (`//testbench:sim_shoumei`)**: Standalone RTL Verilator simulation binary.
- **Automated RISC-V Test Suites (Phase 1 / Tier 2)**:
  - `//testbench/tests:riscv.bzl`: Starlark rules `riscv_elf`, `shoumei_sim_test`, and `shoumei_cosim_test`.
  - `//testbench/tests/...`: 38 hand-written tests (32 C integer, 1 C FP, 3 asm integer, 2 asm FP), generating 76 test targets.
  - `//testbench/tests/generated/...`: 53 generated tests (13 integer patterns, 8 FP patterns, 32 random instruction streams), generating 106 test targets.
  - `//testbench:all_tests`: 182 automated tests executing natively under `bazel test`.
  - `//testbench/coremark:coremark_sim`: CoreMark standalone simulation target.
- **Static Analysis & Linters (Phase 2 / Tier 3)**:
  - `//verification:slang.bzl`: Rule `slang_lint_test` for IEEE 1800-2017 SystemVerilog elaboration linting.
  - `//verification:slang_lint_test`: Validates 238 emitted RTL modules with pyslang.
  - `//verification:slang_sram_lint_test`: Validates `SHOUMEI_SRAM_MACROS` branch against behavioral macro stubs.
  - `//verification:slang_sec_lint_test`: Validates SEC miter modules against base RTL.
  - `//verification:shellcheck_test`: Shellcheck analysis across all repository shell scripts.
  - `//verification:py_compile_test`: Bytecode compiler analysis across all Python scripts.
  - `//verification:cppcheck_test`: Static code analysis across C and C++ testbench files.
  - `//verification:cell_tables_test`: PDK cell table function verification against Liberty models.
  - `//verification:linters`: Aggregates all 7 static analysis tests.
- **Lean Codebase & Project Audits (Phase 2 / Tier 1 Part 2)**:
  - `//lean:no_sorry_test`: Asserts zero incomplete `sorry` proofs across `lean/`.
  - `//lean:lean_root_test`: Asserts `lean/Shoumei/All.lean` is up to date with all source modules.
  - `//lean:project_map_test`: Asserts `docs/project-map.md` matches Lean circuit and proof declarations.
  - `//:shoumei_roundtrip_test`: Generates 124 `.shoumei` files, parses them back, and verifies SV emission round-trip.
  - `//:audits`: Aggregates all 4 integrity audit tests.

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

# Run all static analysis linters (pyslang, shellcheck, py_compile, cppcheck, cell tables)
bazel test //verification:linters

# Run all Lean integrity and project audits (no sorry, lean root, project map, roundtrip)
bazel test //:audits

# Build Spike simulator library
bazel build //third_party:spike_lib

# Build Verilator simulation binaries
bazel build //testbench:sim_shoumei //testbench:cosim_shoumei

# Run all 91 simulation tests in parallel
bazel test //testbench:sim_tests

# Run all 91 Spike lockstep cosimulation tests in parallel
bazel test //testbench:cosim_tests

# Run the complete test suite (182 tests)
bazel test //testbench:all_tests
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
| `//:tb_cpu_sv` | `bazel-bin/rtl_raw_tb_cpu.sv` | 1 file | Generated top-level testbench SystemVerilog |
| `//:cosim_main` | `bazel-bin/rtl_raw_cosim_main_tb_cpu.cpp` | 1 file | Generated cosimulation testbench driver |
| `//:sim_main` | `bazel-bin/rtl_raw_sim_main_tb_cpu.cpp` | 1 file | Generated direct simulation testbench driver |

## Open Work

1. **Synthesis Targets**:
   - Yosys synthesis: Declare actions targeting GF180 and ASAP7 cell synthesis.
   - Techmap LEC: Yosys logical equivalence miter check between gate-level and mapped netlists.

2. **Proof Audits**:
   - Add `lean_axiom_test` targets for key correctness theorems (e.g., `fullAdder_correct`, `alu_correct`, `shoumei_soc_correct`).
   - Gate builds on zero unapproved axioms (`allowed_axioms = ["propext", "Classical.choice", "Quot.sound"]`).

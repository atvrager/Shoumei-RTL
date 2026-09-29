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
- **Hardware Verification & Formal Gates (Phase 3 / Tier 4)**:
  - `//verification:yosys_validate_test`: Syntax and hierarchy verification of all 239 emitted SV modules via Yosys.
  - `//verification:yosys_dc_lint_test`: Synopsys DC-NXT style linting (comb loops, latch inference, width mismatch) using Yosys proxy.
  - `//verification:sec_yosys_test`: Sequential Equivalence Checking (SEC) between flat and hierarchical RTL via Yosys SAT miter.
  - `//verification:sva_verilator_test`: SystemVerilog Assertions (SVA) compilation and verification via Verilator (`--assert --lint-only`).
  - `//verification:check_sec_specs_test`: Dual-RTL specification coverage gate asserting 100% proof or co-simulation coverage.
  - `//verification:sec_manifest_test`: Export and validation of Dual-RTL SEC manifest.
  - `//verification:check_wiring_test`: Circuit input port wiring completeness gate across all 237 registered circuits.
  - `//verification:formal`: Aggregates all 7 formal and structural verification targets.
- **Extended Equivalence, Conformance & Smoke Gates (Tier 5)**:
  - `//verification:pdk_cells_model`: Hermetically generates behavioral PDK cells from Liberty files via Python genrule.
  - `//verification:techmap_equiv_test`: Yosys SAT miter logical equivalence checking (LEC) proving mapped cells in ASAP7 and GF180 match gold RTL.
  - `//testbench:cache_conformance_test`: Verilates L1DCache with C++ driver to verify replacement, refill, and dirty writeback protocols.
  - `//verification:spec_equiv_test`: Differential co-simulation of hand-written SystemVerilog specs against emitted netlists under LFSR stimulus.
  - `//verification:smoke_test`: Structural regression test validating outputs, port lists, instance bindings, cell tables, and proof integrity (74 checks).
  - `//verification:extended`: Aggregates all 4 Tier 5 verification targets.
- **Formal Proof Coverage, Mutation Testing, Dual-RTL Bridge & Axiom Gates (Tier 6)**:
  - `//verification:proof_coverage_test`: Comprehensive proof coverage analysis over 284 Lean files and 1,773 declarations (100% proof coverage, 0 sorry, 0 admit, 0 unproven axioms).
  - `//verification:mutation_test`: Hardware mutation testing suite systematically evaluating 18 gate, pin, and mux mutations; confirms 0% L0 structural kill rate and 100% L1-L3 semantic kill rate.
  - `//verification:sec_bridge_test`: Certified Dual-RTL bridge compiling Yosys SMT2 to pure Lean bitvector models and verifying equivalence via `bv_decide` with zero unapproved axioms.
  - `//lean:core_theorems_axiom_test`: `lean_axiom_test` verifying core gate commutativity and involution theorems depend only on `["propext", "Classical.choice", "Quot.sound"]`.
  - `//lean:logicunit_axiom_test`: `lean_axiom_test` verifying parametric LogicUnit gate, input, and output count theorems depend strictly on `["propext", "Quot.sound"]`.
  - `//lean:queue_invariants_axiom_test`: `lean_axiom_test` verifying inductive queue invariants (`never_exceeds_capacity`, `fifo_single`, etc.) depend strictly on `["propext", "Quot.sound"]`.
  - `//lean:axiom_gates`: Aggregates all theorem axiom gate tests.
  - `//verification:formal_proofs`: Aggregates mutation tests, proof coverage, certified SEC bridge tests, and Lean axiom gates.
- **Generator Optimization**:
  - `//:generate_all` configured with `extra_link_flags = ["-O3", "-DNDEBUG"]`, accelerating execution by ~8x (e.g. `check_wiring` from 619s to 78s).

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

# Run formal verification, equivalence, and wiring gates (Yosys, SVA, SEC, check_wiring)
bazel test //verification:formal

# Run extended equivalence, cache conformance, and smoke gates (Tier 5)
bazel test //verification:extended

# Run Tier 6 formal proofs, mutation tests, SEC bridge, and axiom gates
bazel test //verification:formal_proofs

# Run Tier 7 physical synthesis flow (GF180MCU & ASAP7) and stats
bazel test //verification:synthesis

# Run Tier 7 architecture visuals suite, spec shims, and C++ simulation tests
bazel test //verification:visuals_test //verification:spec_shims_test //cpp_sim:cpp_sim_compile_test

# Build Spike simulator library
bazel build //third_party:spike_lib

# Build Verilator simulation binaries
bazel build //testbench:sim_shoumei //testbench:cosim_shoumei

# Run all 91 simulation tests in parallel
bazel test //testbench:sim_tests

# Run all 91 Spike lockstep cosimulation tests in parallel
bazel test //testbench:cosim_tests

# Run Tier 8 spec-side simulation tests in parallel
bazel test //testbench:spec_tests

# Run Tier 8 native FST inspection tool test
bazel test //tools:fst_inspect_test

# Run Tier 8 instruction benchmark regression suite
bazel test //testbench/benchmarks:bench_regression_test

# Run Tier 9 hardware coverage verification test
bazel test //testbench:coverage_test

# Build Tier 9 GitHub Pages publication bundle
bazel build //viewer:pages_bundle

# Run Tier 9 viewer publication bundle verification test
bazel test //viewer:viewer_bundle_test

# Run the complete simulation test suite (273 tests across sim, cosim, spec)
bazel test //testbench:all_tests

# Run the complete top-level presubmit suite (311 tests across all tiers)
bazel test //:presubmit
```

## Generated Artifacts

Executing `bazel build //:rtl` emits hardware designs into `bazel-bin/`:

| Target | Output Artifact | Count | Description |
| --- | --- | --- | --- |
| `//:sv` | `bazel-bin/rtl_raw_sv/` | 239 files | Hierarchical SystemVerilog modules + `filelist.f` |
| `//verification:sv_spec` | `bazel-bin/verification/sv_spec/` | 239 files | Spec-backed SystemVerilog tree with contract shims |
| `//viewer:pages_bundle` | `bazel-bin/viewer/pages_bundle.tar.gz` | 1 file | Complete GitHub Pages publication distribution bundle |
| `//:sv_netlist` | `bazel-bin/rtl_raw_netlist/` | 238 files | Flat gate-level netlists + `filelist.f` |
| `//:sv_asap7` | `bazel-bin/rtl_raw_asap7/` | 82 files | ASAP7 cell library mappings + `filelist.f` |
| `//:sv_gf180` | `bazel-bin/rtl_raw_gf180/` | 82 files | GF180MCU cell library mappings + `filelist.f` |
| `//:sv_sec` | `bazel-bin/rtl_raw_sec/` | 11 files | SEC miters and TCL scripts |
| `//:cpp_sim` | `bazel-bin/rtl_raw_cpp_sim/` | 477 files | Cycle-accurate C++ simulation models (`.h` / `.cpp`) |
| `//:testbench` | `bazel-bin/rtl_raw_testbench/` | 9 files | Emitted testbenches, drivers, and setups |
| `//:tb_cpu_sv` | `bazel-bin/rtl_raw_tb_cpu.sv` | 1 file | Generated top-level testbench SystemVerilog |
| `//:cosim_main` | `bazel-bin/rtl_raw_cosim_main_tb_cpu.cpp` | 1 file | Generated cosimulation testbench driver |
| `//:sim_main` | `bazel-bin/rtl_raw_sim_main_tb_cpu.cpp` | 1 file | Generated direct simulation testbench driver |

## Migration Status

All 10 Tiers of Bazel migration are complete:
- **Tier 1**: Foundational toolchains, Lean compiler, code generator `//:generate_all`, RTL generator `//:rtl`.
- **Tier 2**: Direct Verilator C++ simulation harness and 91 assembly/baremetal tests (`//testbench:sim_tests`).
- **Tier 3**: Hermetic Spike C++ simulator build via `rules_foreign_cc` and lockstep cosimulation test suite (`//testbench:cosim_tests`).
- **Tier 4**: Code quality, linters (`slang`, `shellcheck`, `cppcheck`, `py_compile`), and Lean roundtrip audits (`//verification:linters`, `//:audits`).
- **Tier 5**: Formal verification and equivalence checking (`//verification:formal`, `//verification:extended`).
- **Tier 6**: Proof coverage, mutation testing, dual-RTL SEC SMT2 bridge (`smt2lean`/`sva2lean`/`bv_decide`), and Lean axiom gates (`//verification:formal_proofs`).
- **Tier 7**: Physical synthesis (GF180MCU & ASAP7), PPA stats, visuals suite, spec shims, C++ simulation library, and unified presubmit aggregator (`//:presubmit`).
- **Tier 8**: Spec-side hardware simulation (`//testbench:sim_spec_shoumei`, `//testbench:spec_tests`), native waveform inspection debugging tools (`//tools:fst_inspect`), instruction benchmarking regression gate (`//testbench/benchmarks:bench_regression_test`), and elimination of in-tree `output/` directory in favor of hermetic Bazel build outputs.
- **Tier 9**: Hardware simulation line coverage instrumentation (`//testbench:sim_shoumei_cov`, `//testbench:coverage_test`) and TypeScript web pipeline visualizer distribution bundle (`//viewer:pages_bundle`, `//viewer:viewer_bundle_test`).
- **Tier 10**: Modernized CI pipeline (`.github/workflows/ci.yml`, `.github/workflows/preview-pages.yml`) executing unified Bazel presubmit suite; complete retirement and removal of legacy `Makefile`, `testbench/Makefile`, `lakefile.lean`, and `lake-manifest.json`.

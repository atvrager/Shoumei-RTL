# Command reference guide

This guide lists commands and Bazel targets for Shoumei RTL.
All commands run from the project root directory.

---

## Quick start

```bash
# Verify prerequisites
python3 bootstrap.py --check-only

# Build Lean proofs and code generator
bazel build //lean:shoumei //:generate_all

# Generate RTL and all hardware artifacts
bazel build //:rtl

# Run the complete presubmit suite (311 tests)
bazel test //:presubmit
```

---

## Key Bazel targets

### Core build targets

| Target | Description | Output |
|--------|-------------|--------|
| `//lean:shoumei` | Lean 4 library (proofs and AST models) | `.olean` bytecode |
| `//:generate_all` | Native code generator binary | `bazel-bin/generate_all` |
| `//:rtl` | Generated SystemVerilog, netlists, and C++ sim | `bazel-bin/rtl_*` |
| `//:instr_dict` | RISC-V opcode definitions dictionary | `bazel-bin/instr_dict.json` |
| `//viewer:pages_bundle` | Web visualization bundle and SVGs | `bazel-bin/viewer/pages_bundle.tar.gz` |

### Test suites

| Target | Description | Size |
|--------|-------------|------|
| `//:presubmit` | Full test suite across all subsystems | 311 tests |
| `//testbench:all_tests` | Combined RTL sim, Spike cosim, and spec tests | 144 tests |
| `//testbench:sim_tests` | Standalone Verilator RTL simulations | 48 tests |
| `//testbench:cosim_tests` | Spike lockstep cosimulations | 48 tests |
| `//testbench:spec_tests` | Specification reference model tests | 48 tests |
| `//testbench:coverage_test` | Verilator hardware line coverage | 1 test |
| `//verification:linters` | Slang elaboration, shellcheck, python, cppcheck | 7 tests |
| `//verification:formal` | SVA formal, SEC miter, bridge validation | 5 tests |
| `//verification:formal_proofs` | Lean metaprogramming proof depth hierarchy | 2 tests |
| `//verification:synthesis` | Yosys ASAP7 and GF180MCU netlist synthesis | 4 tests |
| `//testbench/benchmarks` | Microarchitectural IPC regression benchmarks | 1 test |
| `//lean:integrity_tests` | Zero-sorry check, axiom gates, project map | 4 tests |

---

## Simulator execution

### Running standalone Verilator simulation

```bash
# Run a specific test ELF
bazel run //testbench:sim_shoumei -- +elf=path/to/test.elf +timeout=100000

# Run with waveform tracing enabled (emits sim.fst)
bazel run //testbench:sim_shoumei -- +elf=path/to/test.elf +trace
```

### Running Spike lock-step cosimulation

```bash
# Cosimulate RTL execution against Spike golden model
bazel run //testbench:cosim_shoumei -- +elf=path/to/test.elf +timeout=100000
```

---

## Generator subcommands

The native Lean generator supports targeted tasks through `bazel run`:

```bash
# Export the compositional certificate registry
bazel run //:generate_all -- --export-certs

# Export the refinement registry
bazel run //:generate_all -- --export-refinements

# Check module wiring integrity
bazel run //:generate_all -- --check-wiring

# Check SEC specifications evidence
bazel run //:generate_all -- --check-sec-specs

# Verify lean/Shoumei/All.lean is synchronized
bazel run //:generate_all -- --check-lean-root

# Regenerate docs/project-map.md
bazel run //:generate_all -- --project-map
```

---

## Git and repository maintenance

```bash
# Install Git hooks (fast pre-commit guards)
./scripts/install-githooks.sh

# Download prebuilt RISC-V cross-compilation toolchain
./scripts/setup-riscv-toolchain.sh
```

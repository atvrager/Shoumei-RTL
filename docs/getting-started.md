# Getting Started with Shoumei RTL

This guide walks through setting up the environment, compiling Lean proofs, generating synthesizable RTL, running simulations, and verifying tests through Bazel.

---

## Prerequisites & Environment Setup

### Prerequisites

All user workflows start through Bazel:
- **Bazel** (>= 8.x) or **Bazelisk**
- **Lean 4** (v4.34.1 as pinned in `lean-toolchain`)
- **Python 3.11+**
- **Yosys** (>= 0.66)
- **slang** (`pip install pyslang`)
- **Verilator** (`sudo apt install verilator`)
- **RISC-V GCC** (`riscv64-unknown-elf-gcc` or via `scripts/setup-riscv-toolchain.sh`)

### Verification of Prerequisites

```bash
python3 bootstrap.py --check-only
```

---

## Build & Verification Workflow

### 1. Build Lean Proofs

```bash
bazel build //lean:shoumei
```

Compiles all hardware modules, behavioral models, and formal correctness proofs with zero warnings and zero axioms.

### 2. Generate RTL, Netlists, and C++ Simulation

```bash
bazel build //:rtl
```

Emits all target artifacts from the proven Lean source:
- SystemVerilog (`output/sv-from-lean/*.sv`)
- Flat gate-level netlists (`output/sv-netlist/*.sv`)
- ASAP7 FinFET mapped netlists (`output/sv-asap7/*.sv`)
- GF180MCU mapped netlists (`output/sv-gf180/*.sv`)
- Cycle-accurate C++ simulation model (`output/cpp_sim/*`)
- Testbench scaffolding (`testbench/generated/*`)

### 3. Run Presubmit Test Suite

```bash
bazel test //:presubmit
```

Runs all 311 presubmit tests across proof validation, linting, formal verification, RTL simulation, Spike lockstep cosimulation, and packaging.

### 4. Run Targeted Test Suites

```bash
# Linting & elaboration
bazel test //verification:linters

# Standalone RTL simulation
bazel test //testbench:sim_tests

# Lock-step cosimulation against Spike reference
bazel test //testbench:cosim_tests

# Hardware coverage
bazel test //testbench:coverage_test

# Synthesis gates
bazel test //verification:synthesis

# Benchmark regressions
bazel test //testbench/benchmarks
```

---

## Repository Structure

```
Shoumei-RTL/
├── lean/Shoumei/           # Lean 4 source tree
│   ├── DSL.lean            # Hardware DSL (Wire, Gate, CircuitInstance, Circuit)
│   ├── Circuits/           # Combinational & Sequential circuit library
│   ├── RISCV/              # RV64G out-of-order CPU implementation & proofs
│   ├── Codegen/            # Multi-target code generators (SV, Netlist, ASAP7, C++)
│   └── Verification/       # Compositional certificate registry & proof manifests
├── physical/               # OpenROAD, ASAP7, GF180, and Synopsys DC synthesis scripts
├── testbench/              # Verilator and Spike cosimulation testbenches
├── verification/           # Verification rules, specifications, and linting
├── viewer/                 # Architecture diagram viewer & web packaging
└── docs/                   # Architecture, verification, and physical design guides
```

---

## Where to Go Next

- [project-map.md](project-map.md): Subsystem composition graph and proof coverage matrix.
- [commands.md](commands.md): Comprehensive Bazel command and target reference.
- [adding-a-module.md](adding-a-module.md): Step-by-step walkthrough for building a new verified circuit.
- [adding-an-extension.md](adding-an-extension.md): Adding an ISA extension (decode, classify, execute, verify).
- [verification-guide.md](verification-guide.md): Details on proofs, compositional certificates, and cosimulation.
- [physical-design.md](physical-design.md): ASIC synthesis targets and OpenROAD flow.

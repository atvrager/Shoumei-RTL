# Getting Started with Shoumei RTL

This guide walks through setting up the environment, compiling Lean proofs, generating synthesizable RTL, running simulations, and synthesizing ASIC targets.

---

## Prerequisites & Environment Setup

### Automatic Setup

```bash
make setup
```

This runs `python3 bootstrap.py` to install:
- `elan` (Lean toolchain manager) and Lean 4 (v4.27.0 as pinned in `lean-toolchain`).
- Python build dependencies (via `uv` or `pip`).

Ensure your shell has the tools in `PATH`:
```bash
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
```

### Optional Simulation & Synthesis Tools

To run the full verification and synthesis pipeline:
- **Verilator**: RTL simulation (`sudo apt install verilator`)
- **slang**: IEEE 1800-2017 linting (`pip install pyslang`)
- **Yosys**: Open-source synthesis (>= 0.66 recommended via `YosysHQ/setup-oss-cad-suite` or modern distribution package; avoid older releases like 0.33)
- **RISC-V GCC**: `riscv64-unknown-elf-gcc` for test compilation (`scripts/setup-riscv-toolchain.sh`)

---

## Build & Verification Workflow

### 1. Build Lean Proofs

```bash
lake --no-ansi build
# or: make lean
```

Compiles all 87 hardware modules, behavioral models, and formal correctness proofs with zero warnings and zero axioms.

### 2. Generate RTL, Netlists, and C++ Simulation

```bash
lake --no-ansi exe generate_all
# or: make codegen
```

Emits all target artifacts from the proven Lean source:
- `output/sv-from-lean/*.sv`: Hierarchical SystemVerilog.
- `output/sv-netlist/*.sv`: Flat gate-level netlists.
- `output/sv-asap7/*.sv`: ASAP7 7nm FinFET tech-mapped netlists.
- `output/cpp_sim/*`: Cycle-accurate C++ simulation model.
- `testbench/generated/*`: Testbench scaffolding.

### 3. Elaborate & Lint RTL

```bash
python3 verification/slang-lint.py output/sv-from-lean  # IEEE 1800-2017 elaboration
make systemverilog                                     # Yosys read/hierarchy validation
```

### 4. Run Simulation & Cosimulation

```bash
# Build & run Verilator simulation
make -C testbench sim
make -C testbench run-all-tests

# Build & run 2-way lock-step cosimulation (RTL vs Spike)
make -C testbench cosim
make -C testbench run-cosim
```

### 5. Run Open-Source ASIC Synthesis

```bash
make synth-gf180  # Synthesize RV64 core to GF180MCU at 64 MHz (15.625 ns)
make synth-asap7  # Synthesize RV64 core to ASAP7 7nm at 1.0 GHz (1.000 ns)
```

---

## Repository Structure

```
Shoumei-RTL/
├── lean/Shoumei/           # Lean 4 source tree
│   ├── DSL.lean            # Hardware DSL (Wire, Gate, CircuitInstance, Circuit)
│   ├── Circuits/           # Combinational & Sequential circuit library
│   ├── RISCV/              # RV64G Tomasulo CPU implementation & proofs
│   ├── Codegen/            # Multi-target code generators (SV, Netlist, ASAP7, C++)
│   └── Verification/       # Compositional certificate registry & proof manifests
├── output/                 # Emitted RTL and C++ simulation artifacts
├── physical/               # OpenROAD, ASAP7, GF180, and Synopsys DC synthesis scripts
├── testbench/              # Verilator and cosimulation harnesses
├── verification/           # Verification scripts (slang, proof coverage, mutation testing)
└── docs/                   # Architecture, verification, and physical design guides
```

---

## Where to Go Next

- [project-map.md](project-map.md): Subsystem composition graph and proof coverage matrix.
- [adding-a-module.md](adding-a-module.md): Step-by-step walkthrough for building a new verified circuit.
- [adding-an-extension.md](adding-an-extension.md): Adding an ISA extension (decode, classify, execute, verify).
- [verification-guide.md](verification-guide.md): Details on proofs, compositional certificates, and cosimulation.
- [physical-design.md](physical-design.md): ASIC synthesis targets and OpenROAD flow.

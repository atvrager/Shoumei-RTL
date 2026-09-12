# Shoumei RTL

[![CI](https://github.com/atvrager/Shoumei-RTL/actions/workflows/ci.yml/badge.svg)](https://github.com/atvrager/Shoumei-RTL/actions/workflows/ci.yml)

**Formally verified hardware design with Lean 4 theorem proving.**

> Shoumei (証明, Japanese: proof) -- a hardware design framework where circuits are defined in Lean 4, properties are proven with dependent types, and code generators emit SystemVerilog, a flat netlist, ASAP7 gates and a cycle-accurate C++ model from the same proven source.

## What This Is

A complete pipeline from formal specification to verified, simulated RTL:

1. **Define** circuits in a Lean 4 embedded DSL (gates, wires, instances)
2. **Prove** properties using Lean's type system (`native_decide`, structural induction)
3. **Generate** SystemVerilog, a flat netlist, ASAP7-mapped gates and C++ simulation from the same proven source
4. **Check** the emitted SystemVerilog elaborates (slang, plus a Yosys read/hierarchy pass)
5. **Simulate** with Verilator and C++ sim, validated against Spike ISA reference

```
                    Lean 4 DSL
              (theorems + proofs)
                       |
        +--------------+--------------+
        |              |              |
        v              v              v
   SystemVerilog    SV Netlist     C++ Sim
   (hierarchical)     (flat)     (cycle-accurate)
        |              |              |
        +------+-------+              |
               |                      |
               v                      v
      slang elaboration      Spike (libriscv)
      Verilator simulation            |
               |                      |
               +----------+-----------+
                          |
                          v
              Cosimulation (RVVI lock-step)
```

## Current Status

**Complete `RV32IMAF_Zicsr_Zifencei` out-of-order Tomasulo CPU.**
- Supported extensions: I, M (multiply/divide), A (LR/SC/AMO), F (single-precision floating point), Zicsr, Zifencei.
- Verified with 112/112 tests passing in Verilator simulation and lock-step Spike cosimulation (including `fp_memory` and full RV32IMF suites).

| Category | Modules | Examples |
|----------|---------|---------|
| Arithmetic | 15 | FullAdder, RCA, Subtractor, ALU32 |
| Comparison | 5 | Comparator (4/6/8/32-bit) |
| Logic/Shift | 5 | LogicUnit, Barrel Shifter |
| Mux/Decoder | 14 | Decoder (1-6 bit), Mux (2:1 to 64:1) |
| Arbitration | 3 | PriorityArbiter (2/4/8-input) |
| Sequential | 16 | DFF, Register (1-91 bit), Queue |
| RISC-V Pipeline | 31 | Decoder, RAT, FreeList, PhysRegFile, RS4, ROB, LSU, CPU top |

**Verification:**
- Lean proofs (structural + behavioural) checked by `lake build`; coverage reported by `verification/proof-coverage.sh`
- Modules that cannot be discharged in one step are justified compositionally from their sub-modules (`CompositionalCert`; dependencies derived from the circuit's instances)
- Emitted SV elaborated by slang, simulated under Verilator, cosimulated lock-step against Spike

### Implementation Progress

| Phase | Description | Status |
|-------|-------------|--------|
| 0 | Sequential DSL (DFF, Queue, Register) | Complete |
| 1 | Arithmetic (Adder, Subtractor, Comparator, ALU32) | Complete |
| 2 | RV32I Decoder (all formats) | Complete |
| 3 | Register Renaming (RAT, FreeList, PhysRegFile) | Complete |
| 4 | Reservation Stations (RS4, Decoupled interfaces) | Complete |
| 5 | Execution Units (ALU, Multiplier, Divider, Memory, FPU) | Complete |
| 6 | ROB & Retirement (16-entry, in-order commit) | Complete |
| 7 | Memory System (LSU, StoreBuffer, TSO ordering) | Complete |
| 8 | CPU Integration (RV32IMAF_Zicsr_Zifencei Tomasulo CPU) | Complete |
| 9 | RV32G / RV64G Roadmap (D-extension, XLEN parameterization) | In Progress |

See [docs/roadmap-rv32g-rv64g.md](docs/roadmap-rv32g-rv64g.md) and [docs/rv32g-d-extension-plan.md](docs/rv32g-d-extension-plan.md) for roadmap and D-extension details.

## Quick Start

```bash
# Clone and setup
git clone --recurse-submodules https://github.com/atvrager/Shoumei-RTL.git
cd Shoumei-RTL
make setup          # installs elan, lean, and the build dependencies

# Build
make all            # lean -> codegen -> SV check -> cppsim

# Simulate
export PATH="$HOME/.local/riscv32-elf/bin:$PATH"
make -C testbench/tests             # compile test ELFs
make -C testbench sim               # build Verilator simulation
make -C testbench run-all-tests     # run all 8 ELF tests
make -C testbench cosim             # build cosimulation (auto-builds Spike)
make -C testbench run-cosim         # RTL vs Spike lock-step cosim
```

Or step by step:

```bash
lake build                              # build Lean proofs + code generators
lake exe generate_all                   # generate SV + netlist + ASAP7 + C++ Sim + testbenches
make systemverilog                      # Yosys read/hierarchy check of the emitted SV
python3 verification/slang-lint.py output/sv-from-lean   # slang elaboration
```

### Prerequisites

- **Lean 4** (v4.27.0) -- installed via elan by `make setup`
- **Yosys** -- SystemVerilog read/hierarchy checks (`apt install yosys`)
- **slang** (`pyslang`) -- IEEE 1800-2017 elaboration of the emitted SV (`pip install pyslang`)
- **Verilator** -- for RTL simulation (`apt install verilator`)
- **RISC-V GCC** -- for test compilation (`./scripts/setup-riscv-toolchain.sh`)

## How It Works

### The DSL

Circuits are defined as Lean 4 structures with gates and submodule instances:

```lean
-- A 1-bit full adder
def fullAdderCircuit : Circuit :=
  { name := "FullAdder"
    inputs := [a, b, cin]
    outputs := [sum, cout]
    gates := [
      Gate.mkXOR a b ab_xor,
      Gate.mkXOR ab_xor cin sum,
      Gate.mkAND a b ab_and,
      Gate.mkAND cin ab_xor cin_ab,
      Gate.mkOR ab_and cin_ab cout
    ]
    instances := [] }
```

Larger circuits compose verified building blocks via `CircuitInstance`:

```lean
-- ReservationStation4 uses verified Register, Comparator, Mux, Arbiter instances
def mkReservationStation4 : Circuit :=
  { name := "ReservationStation4"
    instances := [
      { moduleName := "Register91", instName := "u_entry0", portMap := ... },
      { moduleName := "Comparator6", instName := "u_cdb_match0", portMap := ... },
      { moduleName := "PriorityArbiter4", instName := "u_ready_arb", portMap := ... },
      ...
    ]
    ... }
```

### Proofs

```lean
-- Structural: full adder has exactly 5 gates
theorem fullAdder_gate_count : fullAdderCircuit.gates.length = 5 := by native_decide

-- Behavioral: register file write-then-read returns written value
theorem physregfile_read_after_write (prf : PhysRegFileState n) (tag : Fin n) (val : UInt32) :
    (prf.write tag val).read tag = val := by simp [PhysRegFileState.write, PhysRegFileState.read]
```

### Verification

Correctness is established in Lean; the emitted RTL is then checked by elaborating
and running it.

```bash
./verification/proof-coverage.sh                          # Lean proof coverage
python3 verification/slang-lint.py output/sv-from-lean    # slang elaboration
make systemverilog                                        # Yosys read/hierarchy check
make -C testbench sim && make -C testbench run-all-tests  # Verilator simulation
make -C testbench cosim && make -C testbench run-cosim    # RTL vs Spike lock-step
```

Large sequential modules are justified compositionally: a `CompositionalCert`
names the module and its composition proof, and `lake exe generate_all --export-certs`
(run by `make codegen`) derives its dependencies from the circuit's instances and
fails if the certificate names a module the generator does not emit.

## Documentation

| Document | Description |
|----------|-------------|
| [docs/FEATURES.md](docs/FEATURES.md) | What's built -- complete feature list |
| [docs/ROADMAP.md](docs/ROADMAP.md) | What's planned -- near/medium/long-term |
| [CLAUDE.md](CLAUDE.md) | Development guide -- procedures, workflows, conventions |
| [RISCV_TOMASULO_PLAN.md](RISCV_TOMASULO_PLAN.md) | Detailed implementation roadmap |
| [RISCV_TOMASULO_DESIGN.md](RISCV_TOMASULO_DESIGN.md) | Microarchitecture specification |
| [docs/adding-a-module.md](docs/adding-a-module.md) | Step-by-step guide for new modules |
| [docs/verification-guide.md](docs/verification-guide.md) | Proofs, certificates, elaboration, sim and cosim |
| [docs/proof-strategies.md](docs/proof-strategies.md) | Parameterized circuit proof techniques |
| [docs/lean-lsp-guide.md](docs/lean-lsp-guide.md) | Interactive proof development |

## Technology Stack

| Component | Tool | Version |
|-----------|------|---------|
| Theorem prover + DSL | Lean 4 | v4.27.0 |
| SV elaboration | Yosys + slang | system package / pip |
| RTL simulation | Verilator | system package |
| ISA reference | Spike (riscv-isa-sim) | built from source |
| Arcilator backend | CIRCT/firtool | 1.140.0 |
| CI | GitHub Actions | -- |

## License

TBD

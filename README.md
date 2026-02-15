# Shoumei RTL

[![CI](https://github.com/atvrager/Shoumei-RTL/actions/workflows/ci.yml/badge.svg)](https://github.com/atvrager/Shoumei-RTL/actions/workflows/ci.yml)

**Formally verified hardware design with Lean 4 theorem proving.**

> Shoumei (証明, Japanese: proof) -- a hardware design framework where circuits are defined in Lean 4, properties are proven with dependent types, and multiple code generators produce equivalent RTL verified by LEC.

## What This Is

A complete pipeline from formal specification to verified, simulated RTL:

1. **Define** circuits in a Lean 4 embedded DSL (gates, wires, instances)
2. **Prove** properties using Lean's type system (`native_decide`, structural induction)
3. **Generate** SystemVerilog, Chisel/Scala, and C++ simulation from the same proven source
4. **Verify** Lean SV and Chisel SV are logically equivalent (Yosys LEC)
5. **Simulate** with Verilator and C++ sim, validated against Spike ISA reference

```
                    Lean 4 DSL
              (theorems + proofs)
                       |
              +--------+--------+--------+
              |        |        |        |
              v        v        v        v
         SystemVerilog  Chisel  C++ Sim  SV Netlist
          (hierarchical)  |    (cycle-   (flat)
              |           v    accurate)
              |     FIRRTL/CIRCT
              |        |
              v        v
         SV (Lean)  SV (Chisel)
              |        |
              +---+----+         Spike (libriscv)
                  |                    |
                  v                    v
           LEC (Yosys)     Cosimulation (RVVI lock-step)
```

## Current Status

**89 modules** -- 100% LEC coverage. Complete RV32IM out-of-order Tomasulo CPU.

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
- 49 modules via direct LEC (Yosys SAT / sequential induction)
- 9 modules via compositional proofs (Lean theorems + dependency verification)
- 31 modules verified through hierarchy

### Implementation Progress

| Phase | Description | Status |
|-------|-------------|--------|
| 0 | Sequential DSL (DFF, Queue, Register) | Complete |
| 1 | Arithmetic (Adder, Subtractor, Comparator, ALU32) | Complete |
| 2 | RV32IM Decoder (48 instructions, all formats) | Complete |
| 3 | Register Renaming (RAT, FreeList, PhysRegFile) | Complete |
| 4 | Reservation Stations (RS4, Decoupled interfaces) | Complete |
| 5 | Execution Units (ALU, Multiplier, Divider, Memory) | Complete |
| 6 | ROB & Retirement (16-entry, in-order commit) | Complete |
| 7 | Memory System (LSU, StoreBuffer, TSO ordering) | Complete |
| 8 | CPU Integration (behavioral + structural, 89 modules) | Complete |
| 9 | Compliance Testing | Planned |

See [docs/FEATURES.md](docs/FEATURES.md) for details on what's built, and [docs/ROADMAP.md](docs/ROADMAP.md) for what's next.

## Quick Start

```bash
# Clone and setup
git clone --recurse-submodules https://github.com/atvrager/Shoumei-RTL.git
cd Shoumei-RTL
make setup          # installs elan, lean, coursier, sbt

# Build and verify
make all            # lean -> codegen -> chisel -> lec

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
lake exe generate_all                   # generate SV + Chisel + C++ Sim for all modules
cd chisel && sbt run && cd ..           # compile Chisel -> SV via CIRCT
./verification/run-lec.sh              # verify Lean SV == Chisel SV (Yosys)
```

### Prerequisites

- **Lean 4** (v4.27.0) -- installed via elan by `make setup`
- **sbt** + **Scala 2.13** -- installed via coursier by `make setup`
- **Chisel 7.7.0** -- pulled by sbt, auto-manages firtool binary
- **Yosys** -- for LEC verification (`apt install yosys`)
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

```
$ ./verification/run-lec.sh
Loading compositional verification certificates from Lean...
Sorting modules in topological order...

  Verifying: FullAdder         -> EQUIVALENT (SAT)
  Verifying: DFlipFlop         -> EQUIVALENT (induction)
  Verifying: Register91        -> COMPOSITIONALLY VERIFIED (Lean proof)
  ...
Total modules: 89
  Total verified: 89 (100% coverage)
```

## Documentation

| Document | Description |
|----------|-------------|
| [docs/FEATURES.md](docs/FEATURES.md) | What's built -- complete feature list |
| [docs/ROADMAP.md](docs/ROADMAP.md) | What's planned -- near/medium/long-term |
| [CLAUDE.md](CLAUDE.md) | Development guide -- procedures, workflows, conventions |
| [RISCV_TOMASULO_PLAN.md](RISCV_TOMASULO_PLAN.md) | Detailed implementation roadmap |
| [RISCV_TOMASULO_DESIGN.md](RISCV_TOMASULO_DESIGN.md) | Microarchitecture specification |
| [docs/adding-a-module.md](docs/adding-a-module.md) | Step-by-step guide for new modules |
| [docs/verification-guide.md](docs/verification-guide.md) | LEC and compositional proofs |
| [docs/proof-strategies.md](docs/proof-strategies.md) | Parameterized circuit proof techniques |
| [docs/lean-lsp-guide.md](docs/lean-lsp-guide.md) | Interactive proof development |

## Technology Stack

| Component | Tool | Version |
|-----------|------|---------|
| Theorem prover | Lean 4 | v4.27.0 |
| Hardware DSL | Chisel | 7.7.0 |
| Scala | Scala | 2.13.18 |
| RTL compiler | CIRCT/firtool | (managed by Chisel) |
| Equivalence checking | Yosys | system package |
| RTL simulation | Verilator | system package |
| ISA reference | Spike (riscv-isa-sim) | built from source |
| CI | GitHub Actions | 11 checks |

## License

TBD

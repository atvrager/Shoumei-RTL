# Shoumei RTL

[![CI](https://github.com/atvrager/Shoumei-RTL/actions/workflows/ci.yml/badge.svg)](https://github.com/atvrager/Shoumei-RTL/actions/workflows/ci.yml) [![Full Verification](https://github.com/atvrager/Shoumei-RTL/actions/workflows/verify.yml/badge.svg)](https://github.com/atvrager/Shoumei-RTL/actions/workflows/verify.yml) [![Smoke Tests](https://github.com/atvrager/Shoumei-RTL/actions/workflows/smoke-test.yml/badge.svg)](https://github.com/atvrager/Shoumei-RTL/actions/workflows/smoke-test.yml) [![LEC](https://github.com/atvrager/Shoumei-RTL/actions/workflows/lec.yml/badge.svg)](https://github.com/atvrager/Shoumei-RTL/actions/workflows/lec.yml)

**Formally verified hardware design with Lean 4 theorem proving.**

> Shoumei (Japanese: proof) -- a hardware design framework where circuits are defined in Lean 4, properties are proven with dependent types, and dual code generators produce SystemVerilog and Chisel that are verified equivalent by LEC.

## What This Is

A complete pipeline from formal specification to verified RTL:

1. **Define** circuits in a Lean 4 embedded DSL (gates, wires, instances)
2. **Prove** properties using Lean's type system (`native_decide`, structural induction)
3. **Generate** both SystemVerilog and Chisel/Scala from the same proven source
4. **Compile** Chisel to SystemVerilog via FIRRTL/CIRCT (firtool)
5. **Verify** both SystemVerilog outputs are logically equivalent (Yosys LEC)

```
                    Lean 4 DSL
              (theorems + proofs)
                       |
              +--------+--------+
              |                 |
              v                 v
        SystemVerilog       Chisel/Scala
         Generator           Generator
              |                 |
              |                 v
              |          FIRRTL + CIRCT
              |            (firtool)
              |                 |
              v                 v
        SystemVerilog     SystemVerilog
        (from Lean)      (from Chisel)
              |                 |
              +--------+--------+
                       |
                       v
              Equivalence Checking
             (Yosys SAT/induction)
```

## Current Status

**63 modules verified** -- 100% LEC coverage across all generated circuits.

| Category | Modules | Examples |
|----------|---------|---------|
| Arithmetic | 15 | FullAdder, RCA (4/8/32), Subtractor (4/8/32), ALU32 |
| Comparison | 5 | Comparator (4/6/8/32-bit), 5-output (eq/lt/ltu/gt/gtu) |
| Logic/Shift | 5 | LogicUnit (4/8/32), Shifter (4/32) barrel shifters |
| Mux/Decoder | 12 | Decoder (1-6 bit), Mux (2:1 to 64:1, 6-32 bit wide) |
| Arbitration | 3 | PriorityArbiter (2/4/8-input) |
| Sequential | 14 | DFF, Register (1-91 bit), Queue (1-deep, N-deep) |
| RISC-V | 9 | RV32I decoder, RAT, FreeList, PhysRegFile, RS4, exec units |

**Verification method:**
- 54 modules via direct LEC (Yosys SAT solver / sequential induction)
- 9 modules via compositional proofs (Lean theorem proving + dependency verification)

### Implementation Progress

Building toward a formally verified RV32IM out-of-order (Tomasulo) CPU. See [RISCV_TOMASULO_PLAN.md](RISCV_TOMASULO_PLAN.md) for the full roadmap.

| Phase | Description | Status |
|-------|-------------|--------|
| 0 | Sequential DSL (DFF, Queue, Register) | Complete |
| 1 | Arithmetic (Adder, Subtractor, Comparator, ALU32) | Complete |
| 2 | RV32I Decoder (40 instructions, all formats) | Complete |
| 3 | Register Renaming (RAT, FreeList, PhysRegFile) | Complete |
| 4 | Reservation Stations (RS4 + Decoupled interfaces) | In Progress |
| 5-9 | Execution, ROB, Memory, Integration, Verification | Planned |

## Quick Start

No system packages or sudo required. Everything installs to `~/.elan` and `~/.local`.

```bash
# Clone and setup
git clone https://github.com/atvrager/Shoumei-RTL.git
cd Shoumei-RTL
make setup          # installs elan, lean, coursier, sbt

# Build and verify
make all            # lean -> codegen -> chisel -> lec
```

Or step by step:

```bash
lake build                              # build Lean proofs + code generators
lake exe generate_all                   # generate SV + Chisel + SystemC for all modules
cd chisel && sbt run && cd ..           # compile Chisel -> SV via CIRCT
./verification/run-lec.sh              # verify Lean SV == Chisel SV (Yosys)
```

### Prerequisites

- **Lean 4** (v4.27.0) -- installed via elan by `make setup`
- **sbt** + **Scala 2.13** -- installed via coursier by `make setup`
- **Chisel 7.7.0** -- pulled by sbt, auto-manages firtool binary
- **Yosys** -- for LEC verification (`pacman -S yosys` / `apt install yosys`)

## Project Structure

```
Shoumei-RTL/
├── lean/Shoumei/                  # Lean 4 source (83 files, ~5200 lines)
│   ├── DSL.lean                   #   Core types: Wire, Gate, Circuit, CircuitInstance
│   ├── Semantics.lean             #   Operational semantics (eval, state transitions)
│   ├── Codegen/                   #   Code generators (SV, Chisel, SystemC)
│   ├── Circuits/                  #   Circuit library
│   │   ├── Combinational/         #     Adder, ALU, Comparator, Decoder, Mux, Shifter, ...
│   │   └── Sequential/            #     DFF, Register, Queue, QueueN components
│   ├── RISCV/                     #   RISC-V specific circuits
│   │   ├── Decoder.lean           #     RV32I instruction decoder (40 instructions)
│   │   ├── Execution/             #     Integer/Branch/Memory exec units, RS4
│   │   └── Renaming/              #     RAT, FreeList, PhysRegFile, RenameStage
│   └── Verification/              #   Compositional verification certificates
├── chisel/                        # Chisel/Scala project
│   ├── src/main/scala/generated/  #   Generated Chisel modules (auto-discovered)
│   └── build.sbt                  #   Scala 2.13 + Chisel 7.7.0
├── output/                        # Generated artifacts
│   ├── sv-from-lean/              #   SystemVerilog from Lean (63 modules)
│   ├── sv-from-chisel/            #   SystemVerilog from Chisel via CIRCT (65 modules)
│   └── systemc/                   #   SystemC backend (.h + .cpp)
├── verification/                  # Verification scripts
│   ├── run-lec.sh                 #   Yosys LEC with topological sort + compositional certs
│   └── smoke-test.sh              #   Full CI pipeline test
├── docs/                          # Detailed documentation
├── lakefile.lean                  # Lake build config (14 executable targets)
├── Makefile                       # Top-level orchestration
└── RISCV_TOMASULO_PLAN.md         # Implementation roadmap
```

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

Properties are proven using Lean's type system. Structural proofs use `native_decide` for concrete circuits; behavioral proofs use `simp` and manual tactics:

```lean
-- Proven: full adder has exactly 5 gates
theorem fullAdder_gate_count : fullAdderCircuit.gates.length = 5 := by native_decide

-- Proven: register file write-then-read returns written value
theorem physregfile_read_after_write (prf : PhysRegFileState n) (tag : Fin n) (val : UInt32) :
    (prf.write tag val).read tag = val := by simp [PhysRegFileState.write, PhysRegFileState.read]
```

### Verification

LEC runs in topological order, loading compositional certificates from Lean:

```
$ ./verification/run-lec.sh
Loading compositional verification certificates from Lean...
Loaded 9 compositional certificate(s)
Sorting modules in topological order...

  Verifying: FullAdder         -> EQUIVALENT (SAT)
  Verifying: DFlipFlop         -> EQUIVALENT (induction)
  Verifying: Register91        -> COMPOSITIONALLY VERIFIED (Lean proof)
  ...
Total modules: 63
  LEC verified: 54
  Compositionally verified (Lean): 9
  Total verified: 63 (100% coverage)
```

## Documentation

| Document | Description |
|----------|-------------|
| [CLAUDE.md](CLAUDE.md) | Development guide -- procedures, workflows, conventions |
| [RISCV_TOMASULO_PLAN.md](RISCV_TOMASULO_PLAN.md) | Implementation roadmap for the Tomasulo CPU |
| [RISCV_TOMASULO_DESIGN.md](RISCV_TOMASULO_DESIGN.md) | Architecture specification |
| [docs/adding-a-module.md](docs/adding-a-module.md) | Step-by-step guide for building new modules |
| [docs/verification-guide.md](docs/verification-guide.md) | LEC, compositional proofs, troubleshooting |
| [docs/proof-strategies.md](docs/proof-strategies.md) | Parameterized circuit proof techniques |
| [GETTING_STARTED.md](GETTING_STARTED.md) | Installation and environment setup |
| [COMMANDS.md](COMMANDS.md) | Build command reference |

## Technology Stack

| Component | Tool | Version |
|-----------|------|---------|
| Theorem prover | Lean 4 | v4.27.0 |
| Lean build system | Lake | (bundled with Lean) |
| Hardware DSL | Chisel | 7.7.0 |
| Scala | Scala | 2.13.18 |
| Scala build | sbt | 1.10+ |
| RTL compiler | CIRCT/firtool | (managed by Chisel) |
| Equivalence checking | Yosys | open-source |
| CI | GitHub Actions | 4 workflows |

## License

TBD

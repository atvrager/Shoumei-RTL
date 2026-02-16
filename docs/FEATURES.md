# Features

What Shoumei RTL can do today.

## Formally Verified RV32IM Out-of-Order CPU

Complete Tomasulo-style out-of-order processor defined in Lean 4, with dependent-type proofs of correctness. 89 modules, 100% LEC coverage.

### Pipeline Stages

- **Fetch**: PC generation, instruction memory interface
- **Decode**: Full RV32IM decoder (all 48 instruction types), immediate generation
- **Rename**: 32-entry RAT, 64-entry free list, 64x32 physical register file, checkpoint/restore for flush recovery
- **Issue/Dispatch**: 4-entry reservation stations with CDB snooping and operand capture, round-robin allocation, priority-based ready selection
- **Execute**:
  - Integer ALU (add/sub/logic/shift/compare)
  - 3-stage pipelined multiplier with metadata passthrough
  - 32-cycle iterative divider
  - Memory execution unit (AGU + load/store)
- **Memory**: 8-entry store buffer with TSO ordering, store-to-load forwarding (youngest-match), sign extension for byte/halfword loads
- **Retire**: 16-entry reorder buffer, in-order commit, flush on exception/misprediction
- **CDB Arbitration**: Priority-based broadcast from execution units

### Decoupled Interfaces

Formal ready/valid handshaking abstraction (`DecoupledSource`/`DecoupledSink`) used throughout the pipeline for clean inter-stage communication.

## Dual Code Generation

Every circuit generates four outputs from a single Lean definition:

| Output | Purpose |
|--------|---------|
| SystemVerilog (hierarchical) | Primary RTL for synthesis and simulation |
| SystemVerilog (flat netlist) | Gate-level for analysis |
| Chisel/FIRRTL | Leverages CIRCT optimizer, second SV output for LEC |
| C++ Sim | Cycle-accurate C++ simulation model |

Bus reconstruction groups indexed wires into arrays (`wire [31:0] data` instead of 32 individual wires), giving 60-75% fewer wire declarations.

## 100% LEC Verification

Yosys-based logical equivalence checking between Lean-generated SV and Chisel-generated SV:

- **Combinational modules**: SAT-based miter circuit
- **Sequential modules**: Induction-based equivalence
- **Large hierarchical modules**: Compositional verification (LEC submodules, prove composition in Lean)
- Topologically sorted dependency processing
- 89/89 modules verified (49 direct LEC + 9 compositional + 31 inherited)

## Lean Proofs

- Structural proofs (`native_decide`): port counts, gate counts, instance counts
- Behavioral proofs: state machine correctness via concrete tests and `native_decide`
- 110+ memory system tests (StoreBuffer, MemoryExecUnit, LSU)
- 11 reservation station tests (issue, CDB broadcast, ready selection, round-robin)
- TSO memory ordering correctness (store-to-load forwarding, youngest-match priority)

## Simulation & Testing

### Verilator Simulation
- Full RTL simulation of all 8 ELF test programs
- X-prop simulation mode for detecting uninitialized signal issues
- FST trace support for waveform debugging

### C++ Simulation
- Cycle-accurate simulation from Lean-generated C++ simulation
- Same 8 ELF tests pass identically

### 2-Way Lock-Step Cosimulation (RTL vs Spike)
- RVVI-TRACE output ports on CPU report every instruction retirement
- Spike ISA reference oracle via `libriscv` (custom `flat_simif_t` for flat memory at 0x0)
- Per-retirement comparison of PC, instruction word, and destination register
- Automatic fault isolation: catches Lean circuit bugs vs SV codegen bugs
- 8/8 ELF tests pass in cosim mode

### Test Programs
- 8 bare-metal RV32IM ELF tests compiled with `riscv32-unknown-elf-gcc`
- Tests cover: basic ALU, branches, memory load/store, M-extension multiply/divide

## Physical Design

OpenROAD Flow Scripts integration with ASAP7 7nm PDK for synthesis exploration.

## CI Pipeline

11 automated checks on every PR:
- Lint (shellcheck, cppcheck, Python syntax, trailing whitespace)
- Lean build + sorry check
- Proof coverage analysis
- Scala build + format check
- Code generation (SV + Chisel + C++ Sim)
- LEC verification
- Slang IEEE 1800-2017 lint
- Verilator simulation (standard + X-prop)
- C++ simulation
- Smoke tests
- 2-way cosimulation (RTL vs Spike)

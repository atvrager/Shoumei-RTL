# Features

What Shoumei RTL can do today.

## Formally Verified RV32IM Out-of-Order CPU

Complete Tomasulo-style out-of-order processor defined in Lean 4, with dependent-type proofs of correctness. 89 modules, with structural and behavioural Lean theorems checked by `lake build` and emitted RTL validated by slang elaboration, Verilator simulation, and Spike cosimulation.

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

## Code Generation

Every circuit generates its outputs from a single Lean definition:

| Output | Purpose |
|--------|---------|
| SystemVerilog (hierarchical) | Primary RTL for synthesis and simulation |
| SystemVerilog (flat netlist) | Gate-level for analysis |
| SystemVerilog (ASAP7) | Tech-mapped gates for the physical-design flow |
| C++ Sim | Cycle-accurate C++ simulation model |
| Testbenches | Generated testbench scaffolding |

Bus reconstruction groups indexed wires into arrays (`wire [31:0] data` instead of 32 individual wires), giving 60-75% fewer wire declarations.

## Verification

Correctness rests on Lean proofs checked by `lake build`, on the compositional certificate registry, and on running the emitted RTL:

- **Lean proofs**: modules carry structural facts (port, gate, and instance counts) and behavioural properties stated as Lean theorems checked by the kernel; `verification/proof-coverage.sh` reports coverage
- **Compositional certificates**: a `CompositionalCert` names a module and its proof reference; `lake exe generate_all --export-certs` (run by `make codegen`) derives each certificate's dependencies from the circuit's instances and validates the registry against the emitted circuits, exiting non-zero on any inconsistency
- **slang elaboration**: `python3 verification/slang-lint.py output/sv-from-lean` parses and elaborates every emitted SystemVerilog file
- **Yosys read/hierarchy check**: `make systemverilog` runs `verification/validate-sv.sh output/sv-from-lean`
- **Verilator simulation**: `make -C testbench sim` + `make -C testbench run-all-tests`
- **Spike cosimulation**: `make -C testbench cosim` + `make -C testbench run-cosim`

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

CI runs the following checks on every PR:
- Lint (shellcheck, cppcheck, Python syntax, trailing whitespace)
- Proof coverage analysis
- Lean build + sorry check
- Shoumei round-trip
- Code generation (hierarchical SV + flat netlist + ASAP7 + C++ Sim + testbenches)
- Slang IEEE 1800-2017 lint
- Verilator simulation (standard + X-prop)
- C++ simulation
- Smoke tests
- 2-way cosimulation (RTL vs Spike)

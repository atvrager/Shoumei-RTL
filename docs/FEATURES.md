# Features

What Shoumei RTL provides today.

## "Formally Verified" RV64G Out-of-Order CPU

Complete out-of-order processor defined in Lean 4, with dependent-type proofs of correctness. 87 modules, with structural and behavioural Lean theorems checked by `lake build` and emitted RTL validated by slang elaboration, Verilator simulation, Spike lock-step cosimulation, and architectural compliance testing.

### Supported ISA: `RV64IMAFD_Zicsr_Zifencei` (RV64G)

- **RV64I**: 64-bit base integer instruction set (including 32-bit `*W` word instructions).
- **M Extension**: 64-bit integer multiplication and division (`MUL`, `MULH`, `MULHSU`, `MULHU`, `DIV`, `DIVU`, `REM`, `REMU`, plus `*W` variants).
- **A Extension**: Atomic memory operations (`LR.W`/`SC.W`, `LR.D`/`SC.D`, and `AMO*.W`/`AMO*.D` swap, add, xor, and, or, min, max).
- **F & D Extensions**: Single- and double-precision IEEE 754 floating-point execution, fused multiply-add, and FP-integer conversions.
- **Zicsr**: Full CSR access (`CSRRW`, `CSRRS`, `CSRRC`, immediate forms) and machine-mode status registers.
- **Zifencei**: Instruction fetch barrier with pipeline serialization.

### Microarchitecture Pipeline Stages

- **Fetch**: 64-bit PC generation, direct instruction memory bus, and cache-integrated wrapper (`CachedCPU_RV64...`).
- **Decode**: Full RV64G instruction decoder and immediate generator.
- **Rename**: Dual 32-entry RATs (Integer and Floating-Point), 64-entry free list, 64x64-bit physical register file, and single-cycle checkpoint/restore for branch misprediction and exception flush recovery.
- **Issue/Dispatch**: 4-entry reservation stations across execution units with Common Data Bus (CDB) snooping, operand capture, round-robin allocation, and priority-based ready selection.
- **Execute**:
  - **Integer ALU**: 64-bit arithmetic, logic, shift, and compare; dedicated 32-bit W-subtraction/shift logic.
  - **Multiplier**: 3-stage pipelined 64-bit multiplier (`PipelinedMultiplier64`) with metadata passthrough.
  - **Divider**: Iterative 64-bit divider (`Divider64`) with signed/unsigned support.
  - **Floating-Point Unit (`FPExecUnit_D`)**: Multi-stage pipelined FP adder, multiplier, iterative divider, square root unit, and FP-to-integer converters.
  - **Memory Execution Unit**: AGU address calculation and load/store formatting.
  - **Microcoded Trap Sequencer (`TrapSequencer`)**: Multi-cycle sequencer managing CSR operations, exceptions, traps, `MRET`, and pipeline draining for `FENCE.I`.
- **Memory**: decoupled two-stage LSU (`lsu_stage1` AGU → `lsu_stage2` forwarding/CDB), 2-entry MSHR with hit-under-miss, 8-entry circular store queue (`StoreBuffer8`) with explicit age-ordered `older(i,j)` forwarding, `replay_needed` on partial overlaps, and a 128-bit length-agnostic data path (two 64-bit ops per execution slot).
- **Retire**: 16-entry 2-wide reorder buffer (`ROB16_W2`), in-order commit, and precise exception flush.
- **CDB Arbitration**: Multi-port priority arbitration across integer, memory, and floating-point execution units.

### Decoupled Interfaces

Formal ready/valid handshaking abstraction (`DecoupledSource`/`DecoupledSink`) used throughout the pipeline for clean inter-stage communication.

## Code Generation

Every circuit generates all its implementation targets from a single Lean definition:

| Output | Path | Purpose |
|--------|------|---------|
| SystemVerilog (hierarchical) | `output/sv-from-lean/` | Primary synthesizable RTL |
| SystemVerilog (flat netlist) | `output/sv-netlist/` | Gate-level netlist for equivalence checking |
| ASAP7 Tech-Mapped SV | `output/sv-asap7/` | Technology-mapped netlist for 7nm FinFET |
| C++ Sim | `output/cpp_sim/` | Cycle-accurate C++ simulation model |
| Testbenches | `testbench/generated/` | Emitted testbench harnesses |

Bus reconstruction groups indexed scalar wires into clean vector ports (`logic [63:0] data`), reducing signal count and declarations by 60–75%.

## Formal Verification

- **Lean Proofs**: Structural proofs (`native_decide` for ports, gates, instances) and behavioral theorems (state transitions, order preservation, arithmetic equivalence) checked by `lake build`.
- **Zero Axioms**: Production circuits contain 0 unproven axioms or `sorry` statements.
- **Mutation Testing**: `verification/mutation-test.sh` validates that proof suites detect intentional circuit regressions.
- **Compositional Certificates**: Large sequential modules carry a `CompositionalCert` validated at codegen time against emitted module instances.

## Simulation & Testing

### 1. Architectural Compliance
- Passes **107/107** tests in the official RISC-V Architectural Compliance Test Suite (`riscv-arch-test`) for RV64I, RV64M, RV64A, RV64F, RV64D, and Privileged specifications.

### 2. Lock-Step Cosimulation (RTL vs Spike)
- CPU exposes `rvviTrace` output ports on instruction retirement.
- Testbench compares retired PC, instruction word, and destination register state against Spike (`libriscv`) cycle-by-cycle.

### 3. RTL Simulation
- Verilator testbench suite with full X-prop (unknown value propagation) and FST waveform tracing.
- C++ simulation backend for high-speed cycle-accurate execution.

## Physical Design & ASIC Flows

- **GF180MCU**: Canonical target of 64 MHz (15.625 ns period) using open-source Yosys + ABC.
- **ASAP7 7nm FinFET**: Canonical target of 1.0 GHz (1.000 ns period) with multi-corner cell mapping.
- **Synopsys Design Compiler**: Production ASIC synthesis scripts (`physical/run-dc.tcl`).

# RV64G Out-of-Order CPU - Implementation Phase Ledger

**Project:** 証明 Shoumei RTL - "Formally Verified" Out-of-Order Processor  
**Current Milestone:** All 12 Phases (0 through 11) COMPLETE. 87 modules verified, 0 axioms, 107/107 architectural compliance suite passed, and ASIC flows established.

---

## Implementation Phases Overview

| Phase | Title | Scope | Deliverables & Verification |
|:---:|:---|:---|:---|
| **0** | **Sequential DSL & Foundations** | DFF, Register, Queue, QueueN | Structural DFF gates, queue state models, inductive FIFO invariants. |
| **1** | **Arithmetic Units** | Adder, Subtractor, Comparator, ALU | RCA, Kogge-Stone, Subtractor, ALU64 with BitVec semantic bridge proofs. |
| **2** | **Instruction Decoding** | Opcode decode & immediate generation | Full RV64G decoder from spec; bijectivity & soundness proven. |
| **3** | **Register Renaming** | RAT, Free List, Physical Register File | Dual INT/FP RATs, bitmap free list, 64x64 PRF, single-cycle checkpoint/restore. |
| **4** | **Reservation Stations** | RS4 & Decoupled handshaking | 4-entry RS with CDB snooping, operand capture, ready selection arbitration. |
| **5** | **Execution Units** | Integer, Multiplier, Divider, FPU | ALU64, PipelinedMultiplier64 (3-stage), Divider64 (iterative), FPExecUnit_D. |
| **6** | **Reorder Buffer & Retirement** | In-order commit & flush | ROB16_W2 circular buffer, 2-wide commit, precise exception recovery. |
| **7** | **Memory Subsystem** | LSU & Store Buffer | StoreBuffer8, TSO memory consistency, youngest-match store-to-load forwarding. |
| **8** | **Core CPU Integration** | Out-of-Order Pipeline | Full CPU integration, RVVI retirement trace, Verilator & C++ simulation. |
| **9** | **Privileged & Microcode** | Zicsr, Zifencei, Trap Handling | Microcoded TrapSequencer, CSRFile, MRET, machine status CSRs, pipeline flush. |
| **10** | **RV64G Expansion** | 64-Bit Datapath & Compliance | 64-bit integer datapath, D extension, 107/107 riscv-arch-test compliance suite pass. |
| **11** | **Production Hardening & ASIC** | 0 Axioms, Mutation, ASIC flows | Zero axioms, mutation testing, ASAP7 1.0 GHz & GF180MCU 64 MHz open-source synthesis. |

---

## Key Milestone History

### Phase 0–2: Foundations, Arithmetic & Decoding
- Extended hardware DSL to support sequential state (`DFF`, `Register`, `Queue`).
- Proved FIFO ordering invariants without axioms.
- Implemented and "formally verified" 64-bit arithmetic units (Kogge-Stone, Ripple-Carry, Subtractor, Comparators).
- Connected Lean arithmetic implementations to `BitVec` semantics via `bv_decide`.
- Implemented full RV64G instruction decoder and immediate extraction logic.

### Phase 3–5: Renaming, Scheduling & Execution Units
- Designed dual Register Alias Tables (RATs) for 32 integer and 32 floating-point architectural registers mapping to 64 physical registers.
- Built bitmap allocator free list with single-cycle checkpoint restore for branch misprediction recovery.
- Implemented 4-entry reservation stations with Common Data Bus (CDB) snooping and operand latching.
- Built 64-bit execution units: 1-cycle ALU64, 3-stage pipelined multiplier (`PipelinedMultiplier64`), 64-cycle iterative divider (`Divider64`), and double-precision IEEE 754 FPU (`FPExecUnit_D`).

### Phase 6–8: Retirement, Memory & Top-Level Integration
- Implemented 16-entry 2-wide Reorder Buffer (`ROB16_W2`) ensuring in-order retirement and precise exceptions.
- Implemented 8-entry TSO Store Buffer (`StoreBuffer8`) with youngest-match store-to-load forwarding.
- Integrated full out-of-order pipeline with multi-port priority CDB arbitration.
- Built cycle-accurate C++ simulation backend and RVVI lock-step cosimulation against Spike reference model.

### Phase 9–11: Privileged ISA, RV64G Compliance & ASIC Synthesis
- Implemented microcoded `TrapSequencer` and `CSRFile` supporting `Zicsr`, `Zifencei`, and machine-mode trap handling.
- Migrated datapath to 64-bit (`RV64IMAFD_Zicsr_Zifencei`) and achieved 100% pass rate (107/107) on the official RISC-V architectural compliance suite (`riscv-arch-test`).
- Eliminated all unproven axioms from production circuits; validated proof suite sensitivity using mutation testing (`verification/mutation-test.sh`).
- Implemented open-source ASIC synthesis flows: GF180MCU at 64 MHz (15.625 ns) and ASAP7 at 1.0 GHz (1.000 ns), resolving legacy Yosys logic loop issues.

# RV64G Tomasulo CPU Microarchitecture Specification
## 証明 Shoumei RTL - Formally Verified Out-of-Order Processor

**Architecture**: Formally verified, out-of-order 64-bit RISC-V CPU (`RV64IMAFD_Zicsr_Zifencei`) implementing Tomasulo's dynamic scheduling algorithm with precise exceptions, proven in Lean 4.

---

## 1. Architectural Overview

### Pipeline Organization

```
┌─────────────────────────────────────────────────────────────────┐
│                       FETCH & PRE-DECODE                        │
│  ┌──────────┐      ┌─────────────┐      ┌────────────────────┐  │
│  │ 64-bit PC│─────>│ Direct / L1 │─────>│ Instruction Buffer │  │
│  │ Gen/Mux  │      │ I-Cache Bus │      │ & Align            │  │
│  └──────────┘      └─────────────┘      └────────────────────┘  │
└─────────────────────────────────┬───────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────┐
│                     DECODE & CLASSIFICATION                     │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │ Full RV64G Decoder: RV64I, M, A (LR/SC/AMO), F, D, CSR    │  │
│  └───────────────────────────────────────────────────────────┘  │
└─────────────────────────────────┬───────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────┐
│                    REGISTER RENAMING & DISPATCH                 │
│  ┌──────────────┐   ┌──────────────┐   ┌──────────────────────┐ │
│  │ Integer RAT  │   │ FP RAT       │   │ 64-Entry Free List   │ │
│  │ (32 arch→64) │   │ (32 arch→64) │   │ (Bitmap + Checkpoint)│ │
│  └──────────────┘   └──────────────┘   └──────────────────────┘ │
│  ┌─────────────────────────────────┐   ┌──────────────────────┐ │
│  │ Reorder Buffer (ROB16_W2 Alloc) │   │ Busy Bit Table       │ │
│  └─────────────────────────────────┘   └──────────────────────┘ │
└─────────────────────────────────┬───────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────┐
│                      RESERVATION STATIONS                       │
│  ┌───────────┐  ┌───────────┐  ┌───────────┐  ┌──────────────┐  │
│  │ Integer RS│  │ Mul/Div RS│  │ Memory RS │  │ FP RS        │  │
│  │ (4 entry) │  │ (4 entry) │  │ (4 entry) │  │ (4 entry)    │  │
│  └─────┬─────┘  └─────┬─────┘  └─────┬─────┘  └──────┬───────┘  │
└────────┼──────────────┼──────────────┼───────────────┼──────────┘
         │              │              │               │
         ▼              ▼              ▼               ▼
┌─────────────────────────────────────────────────────────────────┐
│                         EXECUTION UNITS                         │
│  ┌───────────┐  ┌───────────┐  ┌───────────┐  ┌──────────────┐  │
│  │ ALU64     │  │ Mul64 (3c)│  │ Memory EU │  │ FPExecUnit_D │  │
│  │ (1 cycle) │  │ Div64(iter│  │ (AGU+mask)│  │ (Add/Mul/Div)│  │
│  └─────┬─────┘  └─────┬─────┘  └─────┬─────┘  └──────┬───────┘  │
│        │              │              │               │          │
│        │        ┌─────┴──────────────┴──────┐        │          │
│        │        │ Microcoded TrapSequencer  │        │          │
│        │        │ (CSRs, Traps, FENCE.I)    │        │          │
│        │        └────────────┬──────────────┘        │          │
└────────┼─────────────────────┼───────────────────────┼──────────┘
         │                     │                       │
         └─────────────────────┼───────────────────────┘
                               │
                               ▼
┌─────────────────────────────────────────────────────────────────┐
│                    COMMON DATA BUS (CDB)                        │
│  Priority Arbitration, Broadcast Tags + Data to RS / ROB / PRF  │
└──────────────────────────────┬──────────────────────────────────┘
                               │
                               ▼
┌─────────────────────────────────────────────────────────────────┐
│                      RETIREMENT & COMMIT                        │
│  ┌─────────────────────────────────┐   ┌──────────────────────┐ │
│  │ ROB16_W2 In-Order Commit        │──>│ StoreBuffer8 Commit  │ │
│  │ (2-wide, precise exceptions)    │   │ to Data Memory (TSO) │ │
│  └─────────────────────────────────┘   └──────────────────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. Pipeline Subsystems

### 2.1 Fetch Stage
- **64-bit Program Counter**: Drives sequential execution (`PC+4`), branch targets, jump addresses (`JAL`, `JALR`), and trap vector offsets.
- **Cache Integration**: Interfaces directly to unified memory or through the direct-mapped instruction cache wrapper (`CachedCPU_RV64...`).
- **Flush & Redirect**: Single-cycle PC redirect on branch misprediction or microcoded trap handling.

### 2.2 Decode & Instruction Classification
Decodes all 32-bit instructions into microarchitectural control fields:
- **RV64I**: Full 64-bit integer instructions (`LD`, `SD`, `ADDI`, etc.) and 32-bit word arithmetic (`ADDW`, `SUBW`, `SLLW`, `SRLW`, `SRAW`).
- **M Extension**: 64-bit integer multiply (`MUL`, `MULH`, `MULHSU`, `MULHU`, `MULW`) and divide/remainder (`DIV`, `DIVU`, `REM`, `REMU`, `DIVW`, etc.).
- **A Extension**: Atomic memory operations (`LR.W`/`SC.W`, `LR.D`/`SC.D`, `AMO*.W`, `AMO*.D`).
- **F & D Extensions**: Single- and double-precision floating-point instructions (arithmetic, comparisons, conversions, and sign injection).
- **Zicsr / Zifencei**: CSR manipulation (`CSRRW`, `CSRRS`, `CSRRC`) and instruction memory barrier synchronization.

### 2.3 Register Renaming
Eliminates WAR and WAW hazards dynamically:
- **Dual Register Alias Tables (RATs)**:
  - Integer RAT: Maps 32 architectural integer registers (`x0`–`x31`) to 64 physical registers (`p0`–`p63`). `x0` is permanently mapped to `p0` (hardwired zero).
  - Floating-Point RAT: Maps 32 architectural FP registers (`f0`–`f31`) to 64 physical FP registers.
- **Physical Register File (`PhysRegFile64`)**: 64 entries of 64-bit registers with multi-port write snooping from the CDB.
- **Free List**: 64-entry bitmap allocator tracking unallocated physical registers.
- **Checkpoint & Restore**: Single-cycle snapshot restore of RAT mappings and free-list state on branch mispredictions and exception flushes.

### 2.4 Reservation Stations (`RS4`)
- 4 entries per execution unit family (Integer, Multiply/Divide, Memory, Floating-Point).
- Each entry tracks:
  - Instruction opcode, immediate value, and assigned ROB tag.
  - Operand 1 / Operand 2: Ready bit, physical tag (if waiting), and captured 64-bit value.
- **CDB Snooping**: Automatically snoops CDB broadcasts; if a broadcast tag matches a waiting operand, captures the value and marks the operand ready.
- **Decoupled Handshake**: Operates via `DecoupledSource` / `DecoupledSink` ready/valid interfaces.

### 2.5 Execution Units
1. **ALU64**: Single-cycle 64-bit arithmetic, logic, shift, compare, and branch condition evaluation.
2. **PipelinedMultiplier64**: 3-stage pipelined 64-bit multiplier with metadata passthrough.
3. **Divider64**: Iterative multi-cycle 64-bit integer divider supporting signed/unsigned division and remainder.
4. **FPExecUnit_D**: IEEE 754-compliant double-precision execution unit incorporating:
   - `FPAdderD`: Multi-stage pipelined FP adder/subtractor.
   - `FPMultiplierD`: Pipelined double-precision multiplier.
   - `FPDivider`: Iterative floating-point divider.
   - `FPSqrt`: Iterative square root unit.
   - `FPToInt64` / `Int64ToFP`: 64-bit integer/FP conversion units.
5. **Memory Execution Unit**: Address Generation Unit (AGU) computing effective addresses (`base + offset`) and generating byte masks.
6. **TrapSequencer**: Microcoded multi-cycle sequencer that serializes the pipeline, accesses `CSRFile`, updates machine status registers (`mstatus`, `mepc`, `mcause`), and handles `MRET` / `FENCE.I`.

### 2.6 Memory Subsystem & TSO Store Buffer
- **StoreBuffer8**: 8-entry FIFO store buffer decoupling store execution from memory write completion.
- **Total Store Order (TSO)**: Stores commit strictly in program order from the ROB head.
- **Store-to-Load Forwarding**: Younger loads match their address against uncommitted store buffer entries; youngest matching store forwards its data with byte-mask merging.

### 2.7 Reorder Buffer (`ROB16_W2`) & Retirement
- 16-entry circular buffer supporting up to 2-wide retirement per cycle.
- Maintains speculative state and guarantees in-order commit.
- On branch misprediction or exception: flushes younger instructions, restores checkpointed RAT/free-list state, and redirects the fetch PC.

---

## 3. Common Data Bus (CDB) & Arbitration

The CDB broadcasts completed results across the core:
- **Payload**: `(valid, tag, value, exception)`.
- **Arbitration**: Priority arbiter grants CDB broadcast slots to execution units (Memory > Floating-Point > Integer).
- **Receivers**: Physical Register File (writes value), Reservation Stations (operand capture), and Reorder Buffer (marks entry complete).

---

## 4. Formal Verification & Correctness

Correctness is established directly in Lean 4:
1. **Structural Theorems**: Port counts, gate counts, and submodule instance counts verified via `native_decide`.
2. **Behavioral Theorems**: State machine transitions, order preservation, and queue invariants proven using dependent types.
3. **Zero Axioms**: All production modules contain zero unproven axioms and zero `sorry` statements.
4. **Compositional Certificates**: Verified sequential subcircuits carry `CompositionalCert` declarations validated by `lake exe generate_all --export-certs`.
5. **Mutation Testing**: Proof robustness verified via `verification/mutation-test.sh`.

---

## 5. Physical Design & ASIC Realization

The microarchitecture is synthesized to both open-source and commercial ASIC targets:
- **GF180MCU**: Canonical target of 64 MHz (15.625 ns period), 6.4 mm² core area via open-source Yosys + ABC.
- **ASAP7 7nm FinFET**: Canonical target of 1.0 GHz (1.000 ns period), 0.0248 mm² core area via open-source Yosys + ABC.
- **Synopsys Design Compiler**: Target synthesis flow configured in `physical/run-dc.tcl`.

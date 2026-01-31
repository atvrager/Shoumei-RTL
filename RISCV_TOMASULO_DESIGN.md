# RV32IM Tomasulo CPU Design Document
## 証明 Shoumei RTL - Formally Verified Out-of-Order Processor

**Project Goal**: Build a formally verified, out-of-order RISC-V CPU using Tomasulo's algorithm, with all components proven correct in LEAN4.

---

## Table of Contents

1. [Overview](#overview)
2. [Architecture](#architecture)
3. [Microarchitecture Details](#microarchitecture-details)
4. [Building Blocks (Bottom-Up)](#building-blocks-bottom-up)
5. [Implementation Phases](#implementation-phases)
6. [RISC-V Opcodes Integration](#risc-v-opcodes-integration)
7. [Proof Strategy](#proof-strategy)
8. [Verification Plan](#verification-plan)
9. [Performance Targets](#performance-targets)
10. [Future Enhancements](#future-enhancements)

---

## Overview

### What is RV32IM?

**RV32I** - Base Integer Instruction Set (32-bit)
- 32 integer registers (x0-x31, where x0 is hardwired to zero)
- Load/Store architecture
- 47 instructions: arithmetic, logical, branches, jumps, loads, stores, system

**RV32M** - Integer Multiplication and Division Extension
- MUL, MULH, MULHSU, MULHU (multiply variants)
- DIV, DIVU, REM, REMU (division and remainder)

### What is Tomasulo's Algorithm?

Dynamic instruction scheduling algorithm that:
- **Eliminates false dependencies** (WAR, WAW) through register renaming
- **Enables out-of-order execution** while maintaining precise exceptions
- **Uses reservation stations** instead of centralized scoreboard
- **Broadcasts results** on Common Data Bus (CDB) to waiting instructions

**Key advantages:**
- Higher instruction-level parallelism (ILP)
- Better utilization of functional units
- Proven algorithm (invented for IBM System/360 Model 91 in 1967)

### Why Tomasulo for Shoumei RTL?

1. **Well-defined semantics** - Tomasulo has clear operational semantics
2. **Modular structure** - Clean separation of concerns (decode, rename, execute, retire)
3. **Interesting proofs** - Register renaming, memory ordering, speculative execution
4. **Real-world relevance** - Modern CPUs (Intel, AMD) use Tomasulo-like schemes
5. **Scalable complexity** - Start simple, add features incrementally

---

## Architecture

### High-Level Block Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                       FETCH & DECODE                             │
│  ┌──────┐    ┌──────┐    ┌──────────┐    ┌────────────────┐   │
│  │  PC  │───>│ IMem │───>│ Decoder  │───>│ Dispatch Queue │   │
│  └──────┘    └──────┘    └──────────┘    └────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────┐
│                    REGISTER RENAMING                             │
│  ┌─────────────┐   ┌──────────────┐   ┌────────────────┐       │
│  │ RAT (32→N)  │   │ Free List    │   │ Reorder Buffer │       │
│  │ (Rename)    │   │ (Phys Regs)  │   │ (ROB)          │       │
│  └─────────────┘   └──────────────┘   └────────────────┘       │
└─────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────┐
│                  RESERVATION STATIONS                            │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐           │
│  │ ALU RS  │  │ MUL RS  │  │ DIV RS  │  │ LD/ST RS│           │
│  │ (4 ent) │  │ (2 ent) │  │ (1 ent) │  │ (4 ent) │           │
│  └─────────┘  └─────────┘  └─────────┘  └─────────┘           │
└─────────────────────────────────────────────────────────────────┘
           │           │           │           │
           ▼           ▼           ▼           ▼
┌─────────────────────────────────────────────────────────────────┐
│                   EXECUTION UNITS                                │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐           │
│  │  ALU    │  │ Mult    │  │  Div    │  │ LSU     │           │
│  │ (1 cyc) │  │ (3 cyc) │  │ (32 cyc)│  │ (2 cyc) │           │
│  └─────────┘  └─────────┘  └─────────┘  └─────────┘           │
└─────────────────────────────────────────────────────────────────┘
           │           │           │           │
           └───────────┴───────────┴───────────┘
                        │
                        ▼
              ┌──────────────────┐
              │ Common Data Bus  │
              │ (CDB - 2 wide)   │
              └──────────────────┘
                        │
                        ▼
              ┌──────────────────┐
              │  RETIRE STAGE    │
              │  (ROB Commit)    │
              └──────────────────┘
```

### Pipeline Overview

**5 Conceptual Stages** (but out-of-order execution within):

1. **Fetch** - Read instruction from memory
2. **Decode/Rename** - Decode instruction, allocate ROB entry, rename registers
3. **Issue** - Wait for operands, issue to reservation station
4. **Execute** - Perform operation when ready
5. **Retire** - Commit results in program order, update architectural state

---

## Microarchitecture Details

### 1. Instruction Fetch Unit

**Components:**
- **PC Register** (32-bit)
- **Instruction Memory** (simplified: single-cycle read)
- **Branch Predictor** (optional v1: always not-taken)

**Operation:**
- PC increments by 4 each cycle (unless branch/jump)
- Fetches 32-bit instruction
- Sends to decode stage

**Proof obligations:**
- PC only takes valid addresses (aligned to 4 bytes)
- Fetch never stalls (or has well-defined stall semantics)

### 2. Instruction Decoder

**Input:** 32-bit instruction word
**Output:** Decoded fields + control signals

**Generated from riscv-opcodes:**
- Opcode (7 bits)
- rd, rs1, rs2 (register specifiers)
- Immediate values (I-type, S-type, B-type, U-type, J-type)
- Function codes (funct3, funct7)

**Decoder outputs:**
- `opType`: ALU | MUL | DIV | LOAD | STORE | BRANCH | JAL | JALR | LUI | AUIPC | SYSTEM
- `aluOp`: ADD | SUB | AND | OR | XOR | SLT | SLTU | SLL | SRL | SRA
- `immType`: I | S | B | U | J
- Register specifiers: rd, rs1, rs2
- Immediate value (sign-extended to 32 bits)

**Proof obligations:**
- All valid instruction encodings map to exactly one operation
- All operations have valid encodings (bijection)
- Immediate extraction matches RISC-V spec

### 3. Register Renaming (RAT + Free List)

**Register Alias Table (RAT)**
- 32 entries (one per architectural register)
- Each entry contains physical register tag
- Updated on dispatch
- Read during decode to find source operands

**Physical Register File**
- 64 physical registers (configurable)
- Accessed by physical tag, not architectural name
- Holds speculative and committed values

**Free List**
- Queue of available physical register tags
- Pop on allocation (dispatch)
- Push on deallocation (commit, when old mapping no longer needed)

**Proof obligations:**
- No two architectural registers map to same physical register (unless x0)
- Free list never underflows (stall on empty)
- Physical register deallocated only when safe (no pending reads)

### 4. Reorder Buffer (ROB)

**Purpose:** Maintain program order for in-order retirement

**Structure:** Circular buffer with head and tail pointers

**Entry contents:**
- PC (for exceptions)
- Opcode
- Destination physical register
- Old destination physical register (for deallocation)
- Value (when complete)
- Ready bit
- Exception status

**Operations:**
- **Allocate** (dispatch): Add entry at tail, increment tail
- **Complete** (CDB write): Mark ready, store value
- **Commit** (retire): Remove entry at head, update architectural state, increment head

**Size:** 16 entries (configurable)

**Proof obligations:**
- ROB preserves program order
- Commits happen in order
- Speculative state discarded correctly on branch mispredict

### 5. Reservation Stations

**Purpose:** Hold decoded instructions waiting for operands

**Types:**
- **ALU RS** (4 entries): ADD, SUB, AND, OR, XOR, SLT, shifts, etc.
- **MUL RS** (2 entries): MUL, MULH, MULHSU, MULHU
- **DIV RS** (1 entry): DIV, DIVU, REM, REMU
- **LD/ST RS** (4 entries): LW, LH, LB, SW, SH, SB (and unsigned variants)

**Entry structure:**
```lean
structure ReservationStationEntry where
  valid : Bool
  opcode : OpType
  op1_ready : Bool
  op1_tag : PhysReg      -- if not ready, tag to watch
  op1_value : UInt32     -- if ready, actual value
  op2_ready : Bool
  op2_tag : PhysReg
  op2_value : UInt32
  dest_tag : PhysReg     -- where to write result
  rob_index : ROBIndex   -- corresponding ROB entry
  imm : UInt32           -- for immediates
```

**Operation:**
- **Issue**: Allocate entry, capture operands (value if ready, tag if not)
- **Snoop CDB**: If waiting tag appears on CDB, capture value and mark ready
- **Dispatch to EU**: When both operands ready, send to execution unit
- **Deallocate**: When issued to EU, mark invalid

**Proof obligations:**
- Operand capture is correct (matches register renaming)
- No hazards (operands captured before overwritten)
- Fair scheduling (oldest ready instruction issues first)

### 6. Execution Units

**ALU (1-cycle latency)**
- Operations: ADD, SUB, AND, OR, XOR, SLT, SLTU, SLL, SRL, SRA
- Also handles branches: BEQ, BNE, BLT, BGE, BLTU, BGEU
- Combinational logic

**Multiplier (3-cycle latency, pipelined)**
- Booth's algorithm or Wallace tree
- Handles MUL (lower 32 bits), MULH (upper 32 bits)

**Divider (32-cycle latency, non-pipelined)**
- Restoring or non-restoring division
- Handles DIV, DIVU (quotient), REM, REMU (remainder)

**Load-Store Unit (LSU, 2-cycle latency)**
- Address generation: base + offset
- Data memory access
- Store buffer for memory ordering

**Proof obligations:**
- Each functional unit implements correct operation
- Timing is deterministic
- Pipelined units handle back-pressure correctly

### 7. Common Data Bus (CDB)

**Purpose:** Broadcast execution results to reservation stations and ROB

**Structure:**
- 2-way CDB (two results per cycle)
- Each entry: (tag, value, valid)

**Operation:**
- Execution units arbitrate for CDB access
- Selected results broadcast to all reservation stations and ROB
- Reservation stations snoop bus, capture matching tags

**Proof obligations:**
- CDB arbitration is fair
- No tag conflicts (two units don't produce same tag simultaneously)
- All waiting instructions eventually receive operands

### 8. Memory System (Simplified)

**Data Memory**
- Single-cycle read/write (unrealistic but simplifies initial design)
- Future: Add cache model

**Store Buffer**
- Stores held until commit (for precise exceptions)
- Forwarding: Younger loads check store buffer for address matches

**Memory Ordering**
- Loads can execute speculatively
- Stores only commit in program order

**Proof obligations:**
- Load-store hazards detected correctly
- Store-to-load forwarding is correct
- Memory state consistent with program order

---

## Building Blocks (Bottom-Up)

### Level 1: Basic Combinational Components

**Already implemented:**
- ✅ Gate (AND, OR, NOT, XOR)
- ✅ FullAdder

**Need to implement:**

**1.1 Comparator**
```lean
-- Compare two n-bit values
def Comparator (n : Nat) : Circuit
  inputs: a[n], b[n]
  outputs: eq, lt, gt
  -- Proof: eq ↔ (a = b), lt ↔ (a < b), gt ↔ (a > b)
```

**1.2 Multiplexer**
```lean
-- 2:1 mux (select between two inputs)
def Mux2 : Circuit
  inputs: a, b, sel
  outputs: out
  -- out = sel ? b : a

-- N-way mux (one-hot select)
def MuxN (n : Nat) : Circuit
  inputs: data[n], sel[n]  -- sel is one-hot
  outputs: out
```

**1.3 Decoder**
```lean
-- Binary to one-hot decoder
def Decoder (n : Nat) : Circuit
  inputs: binary[n]
  outputs: onehot[2^n]
  -- Proof: exactly one output is high
```

**1.4 Encoder**
```lean
-- One-hot to binary encoder (priority encoder)
def PriorityEncoder (n : Nat) : Circuit
  inputs: onehot[n]
  outputs: binary[log2(n)], valid
  -- Proof: encodes position of first high bit
```

### Level 2: Arithmetic Units

**2.1 Ripple-Carry Adder**
```lean
-- Chain of full adders
def RippleCarryAdder (n : Nat) : Circuit
  inputs: a[n], b[n], cin
  outputs: sum[n], cout
  -- Proof: sum = a + b + cin (modulo 2^n)
```

**2.2 Subtractor**
```lean
-- Adder with complement for subtraction
def Subtractor (n : Nat) : Circuit
  inputs: a[n], b[n]
  outputs: diff[n], borrow
  -- Proof: diff = a - b (two's complement)
```

**2.3 Multiplier (Array Multiplier)**
```lean
-- Simple array multiplier (n×n → 2n bits)
def ArrayMultiplier (n : Nat) : Circuit
  inputs: a[n], b[n]
  outputs: product[2*n]
  -- Proof: product = a * b
```

**2.4 Divider (Restoring Division)**
```lean
-- Sequential restoring divider
def RestoringDivider (n : Nat) : StatefulCircuit
  inputs: dividend[n], divisor[n], start
  outputs: quotient[n], remainder[n], done
  -- Proof: dividend = quotient * divisor + remainder
```

**2.5 ALU**
```lean
-- Combined arithmetic and logic unit
def ALU32 : Circuit
  inputs: a[32], b[32], op[4]
  outputs: result[32], zero, overflow
  -- Supports: ADD, SUB, AND, OR, XOR, SLT, SLL, SRL, SRA
```

### Level 3: Sequential Elements (NEW DSL EXTENSION)

**3.1 D Flip-Flop**
```lean
-- Basic storage element
structure DFF where
  inputs: d, clk, reset
  outputs: q, qn
  -- Proof: q(t+1) = d(t) on rising edge of clk
```

**3.2 Register**
```lean
-- N-bit register with enable
def Register (n : Nat) : StatefulCircuit
  inputs: d[n], clk, enable, reset
  outputs: q[n]
  -- Proof: if enable then q(t+1) = d(t) else q(t+1) = q(t)
```

**3.3 Queue/FIFO (MOST IMPORTANT!)**
```lean
-- Single-entry queue (simplest case)
def Queue1 (width : Nat) : StatefulCircuit
  inputs: enq_data[width], enq_valid, deq_ready, clk, reset
  outputs: enq_ready, deq_data[width], deq_valid
  -- Proof: FIFO ordering, no data loss

-- Multi-entry FIFO with circular buffer
def QueueN (depth width : Nat) : StatefulCircuit
  inputs: enq_data[width], enq_valid, deq_ready, clk, reset
  outputs: enq_ready, deq_data[width], deq_valid, count[log2(depth+1)]
  -- Proof:
  --   - FIFO ordering maintained
  --   - No overflow (enq_ready deasserts when full)
  --   - No underflow (deq_valid deasserts when empty)
  --   - Count always accurate
```

**WHY QUEUE FIRST:**
- Foundation for ROB (Reorder Buffer)
- Foundation for store buffer
- Foundation for dispatch queue
- Foundation for free list
- Tests all sequential semantics: read, write, state management
- Simple enough to prove thoroughly
- Complex enough to be useful

**3.4 Register File**
```lean
-- Multi-ported register file
def RegisterFile (nRegs nPorts : Nat) : StatefulCircuit
  inputs:
    -- Read ports
    readAddr[nPorts][log2(nRegs)]
    -- Write port
    writeAddr[log2(nRegs)]
    writeData[32]
    writeEnable
    clk, reset
  outputs:
    readData[nPorts][32]
  -- Proof: Read-after-write bypassing, x0 always zero
```

### Level 4: Complex Structures

**4.1 Content-Addressable Memory (CAM)**
```lean
-- For tag matching in reservation stations
def CAM (nEntries dataWidth : Nat) : Circuit
  inputs: searchKey[dataWidth], data[nEntries][dataWidth]
  outputs: match[nEntries]  -- one-hot match vector
  -- Proof: match[i] ↔ (data[i] = searchKey)
```

**4.2 Circular Buffer (for ROB)**
```lean
-- FIFO with head/tail pointers
def CircularBuffer (depth width : Nat) : StatefulCircuit
  inputs:
    enq_data[width], enq_valid
    deq_ready
    clk, reset
  outputs:
    enq_ready
    deq_data[width], deq_valid
    count[log2(depth)]
  -- Proof: FIFO ordering, no overflow/underflow
```

**4.3 Arbiter**
```lean
-- Round-robin arbiter for CDB access
def RoundRobinArbiter (n : Nat) : StatefulCircuit
  inputs: req[n]
  outputs: grant[n]  -- one-hot grant
  -- Proof: fairness, mutual exclusion
```

---

## Implementation Phases

### Phase 0: DSL Extension for Sequential Circuits (CRITICAL) - ✅ 100% COMPLETE

**Goal:** Extend Shoumei DSL to support stateful elements, with Queue as the proving ground

**Tasks:**
1. ✅ Add `StatefulCircuit` type to DSL.lean - *Sequential circuits fully supported*
2. ✅ Define clock and reset semantics in Semantics.lean
   - State type, evalCycleSequential, evalSequential
3. ✅ Add register primitives (DFF, Register)
   - DFF with DFFProofs.lean (8 theorems)
   - N-bit Register with RegisterProofs.lean (concrete + inductive framework)
4. ✅ **Implement Queue/FIFO (single-entry, 1-deep)**
   - QueueState with .enqueue/.dequeue/.peek methods
   - QueueCircuit for code generation (widths: 8-bit, 32-bit)
   - Ready/valid handshake protocol
5. ✅ Update code generators for sequential SystemVerilog/Chisel
   - ✅ DFF/Register generation working
   - ✅ Queue generation complete (Queue1_8, Queue1_32)
   - ✅ Codegen/Queue.lean with toSystemVerilog and toChisel
6. ✅ Prove Queue properties (FIFO ordering, no overflow/underflow)
   - QueueProofs.lean with 20+ theorems
   - FIFO ordering (single, dual, triple element sequences)
   - Overflow/underflow protection, count accuracy, peek correctness
   - 32-bit wide data support verified
7. ✅ Test Queue with LEC verification
   - ✅ SEC (Sequential Equivalence Checking) working for DFF
   - ✅ Queue LEC passing for both Queue1_8 and Queue1_32
   - ✅ Integrated into smoke test with full verification pipeline

**Why Queue First:**
- Exercises ALL sequential features: state, control flow, ready/valid handshake
- Simple enough to prove completely
- Immediately useful for later phases (ROB, dispatch queue, etc.)
- Tests SystemVerilog/Chisel generator quality for stateful circuits

**Completed:** 2026-01-31
**Deliverable:** Verified Queue with 1-entry depth, 8-bit and 32-bit widths
**Status:** ✅ COMPLETE - All proofs verified, code generation working, LEC passing

**Success Criteria:**
- ✅ Queue behavioral model (QueueState) with .enqueue/.dequeue/.peek
- ✅ Queue structural model (QueueCircuit) for code generation
- ✅ 20+ formal proofs in QueueProofs.lean (all verified with native_decide)
- ✅ SystemVerilog generation from LEAN (Queue1_8.sv, Queue1_32.sv)
- ✅ Chisel generation from LEAN (Queue1_8.scala, Queue1_32.scala)
- ✅ Chisel compilation to SystemVerilog via CIRCT
- ✅ LEC verification (LEAN SV ≡ Chisel SV) using Yosys SEC
- ✅ Smoke test integration with all 4 modules passing

**Note:** Multi-entry queues (depth > 1) require circular buffer implementation with head/tail pointers. This is deferred to Phase 1+ as needed for specific components (ROB, RS).

### Phase 1: Arithmetic Building Blocks - 🔄 IN PROGRESS (17% complete)

**Goal:** Implement and verify all arithmetic units needed for RV32IM

**Tasks:**
1. ✅ FullAdder (already done - Phase 0)
2. ✅ **Ripple-Carry Adder (32-bit)** - COMPLETE
   - RippleCarryAdder32: 160 gates (32 FullAdders chained)
   - Hierarchical composition via `Circuit.inline`
   - 3 structural proofs verified
   - Variants: RCA4, RCA8, RCA32
3. Subtractor32 (RCA + 2's complement) - NEXT
4. Comparator32 (3-output: eq, lt, gt)
5. LogicUnit32 (AND/OR/XOR parallel)
6. Shifter32 (5-stage barrel shifter)
7. Complete ALU with all RV32I operations
8. Array Multiplier (32×32→64) - OPTIONAL/DEFERRED
9. Restoring Divider (32-bit) - OPTIONAL/DEFERRED

**Timeline:** 3-4 weeks (started 2026-01-31)
**Deliverable:** Verified ALU core (items 1-7), optionally multiplier/divider

**Key Achievement:** DSL enhanced with hierarchical circuit composition!
- Added `Circuit.inline` for compositional proofs
- RippleCarryAdder now reuses proven `fullAdderCircuit` instances
- Foundation for scalable verification

### Phase 2: RISC-V Decoder Integration

**Goal:** Parse riscv-opcodes and generate verified decoder

**Tasks:**
1. Add riscv-opcodes as git submodule
2. Write LEAN parser for opcodes format
3. Generate decoder circuit from opcode definitions
4. Prove decoder completeness and correctness
5. Generate instruction semantic functions

**Timeline:** 2-3 weeks
**Deliverable:** Verified instruction decoder with full RV32IM coverage

### Phase 3: Register Renaming Infrastructure

**Goal:** Implement RAT, physical register file, free list

**Tasks:**
1. Register file with parameterized ports
2. Register Alias Table (32→N mapping)
3. Free list (priority queue)
4. Physical register allocation/deallocation logic
5. Prove renaming preserves semantics

**Timeline:** 3-4 weeks
**Deliverable:** Verified register renaming unit

### Phase 4: Reservation Stations

**Goal:** Implement dynamic scheduling infrastructure

**Tasks:**
1. Reservation station entry structure
2. Issue logic (operand capture)
3. CDB snooping and wakeup
4. Arbitration for execution units
5. Prove operand forwarding correctness

**Timeline:** 4-5 weeks
**Deliverable:** Verified reservation station array

### Phase 5: Execution Units

**Goal:** Integrate arithmetic units with RS/CDB interface

**Tasks:**
1. ALU wrapper with RS interface
2. Multiplier pipeline (3 stages)
3. Divider state machine (32 cycles)
4. Load-Store Unit with address generation
5. Prove each unit implements correct operation

**Timeline:** 3-4 weeks
**Deliverable:** Verified execution units

### Phase 6: Reorder Buffer & Retirement

**Goal:** In-order commit with precise exceptions

**Tasks:**
1. ROB circular buffer
2. Commit logic (head pointer management)
3. Exception handling
4. Architectural state update
5. Prove ROB maintains program order

**Timeline:** 3-4 weeks
**Deliverable:** Verified ROB with commit logic

### Phase 7: Memory System

**Goal:** Load-store unit with ordering

**Tasks:**
1. Simple data memory model
2. Store buffer
3. Load-store forwarding
4. Memory ordering checks
5. Prove memory consistency

**Timeline:** 2-3 weeks
**Deliverable:** Verified LSU with store buffer

### Phase 8: Top-Level Integration

**Goal:** Connect all components into complete CPU

**Tasks:**
1. Top-level module instantiation
2. Control logic (stalls, flushes)
3. Branch misprediction recovery
4. Exception pipeline flush
5. End-to-end instruction execution proof

**Timeline:** 4-6 weeks
**Deliverable:** Complete RV32IM Tomasulo CPU

### Phase 9: Verification & Testing

**Goal:** Comprehensive validation

**Tasks:**
1. RISC-V compliance tests (riscv-tests suite)
2. Random instruction stream testing
3. LEC verification of all modules
4. Performance analysis (IPC measurement)
5. Formal correctness proof (instruction semantics preserved)

**Timeline:** 3-4 weeks
**Deliverable:** Verified CPU passing all compliance tests

---

## RISC-V Opcodes Integration

### Repository: https://github.com/riscv/riscv-opcodes

**Purpose:** Machine-readable RISC-V instruction database

**Format:** Python pseudo-tables with instruction fields

**Example entry:**
```python
add     rd rs1 rs2 31..25=0  24..20=rs2 19..15=rs1 14..12=0 11..7=rd 6..0=0x33
sub     rd rs1 rs2 31..25=32 24..20=rs2 19..15=rs1 14..12=0 11..7=rd 6..0=0x33
mul     rd rs1 rs2 31..25=1  24..20=rs2 19..15=rs1 14..12=0 11..7=rd 6..0=0x33
```

### Integration Strategy

**Step 1: Add as dependency**
```bash
git submodule add https://github.com/riscv/riscv-opcodes external/riscv-opcodes
git submodule update --init --recursive
```

**Step 2: Write LEAN parser**
```lean
-- File: lean/Shoumei/RISCV/OpcodeParser.lean

-- Parse single opcode line
def parseOpcodeLine (line : String) : Option InstructionDef

-- Parse entire opcodes file
def parseOpcodesFile (path : FilePath) : IO (List InstructionDef)

-- Generate decoder circuit
def generateDecoder (insns : List InstructionDef) : Circuit
```

**Step 3: Prove decoder properties**
```lean
-- Every valid 32-bit instruction decodes to exactly one operation
theorem decoder_complete : ∀ (insn : UInt32),
  (∃! op : Operation, decodes insn op) ∨ illegalInstruction insn

-- Decoder is injective (no overlap)
theorem decoder_unique : ∀ (insn : UInt32) (op1 op2 : Operation),
  decodes insn op1 → decodes insn op2 → op1 = op2
```

**Step 4: Generate instruction semantics**
```lean
-- Define semantic function for each instruction
def executeInstruction (op : Operation) (rs1 rs2 : UInt32) : UInt32 :=
  match op with
  | .ADD => rs1 + rs2
  | .SUB => rs1 - rs2
  | .MUL => (rs1 * rs2).truncate 32
  | ...
```

### Files in riscv-opcodes to use:

- `opcodes` - RV32I base instruction set
- `opcodes-rv32m` - Multiply/divide extension
- `opcodes-pseudo` - Pseudo-instructions (optional)

### Code generation options:

The riscv-opcodes repo can generate:
- C headers
- Verilog/SystemVerilog decoders
- LaTeX documentation
- Rust bindings

**We will:** Write our own LEAN generator to create proven decoder circuits

---

## Proof Strategy

### Proof Hierarchy

**Level 0: Gate-level proofs**
- ✅ Boolean algebra identities
- ✅ Gate semantics (AND, OR, NOT, XOR)

**Level 1: Combinational circuit proofs**
- ✅ FullAdder correctness
- RippleCarryAdder = sum of inputs
- Multiplier = product of inputs
- ALU operation correctness

**Level 2: Sequential circuit proofs**
- Register read-after-write semantics
- Register file port independence
- Memory read-after-write

**Level 3: Module-level proofs**
- Decoder: All instructions decode correctly
- Reservation station: Operand capture correctness
- ROB: Program order preservation
- CDB: Fair arbitration, no conflicts

**Level 4: Subsystem proofs**
- Register renaming preserves program semantics
- Execution units produce correct results
- Memory ordering maintained

**Level 5: End-to-end proof**
- **Main theorem**: For any program P, the Tomasulo CPU produces the same architectural state as the sequential RISC-V ISA specification

### Proof Techniques

**1. Refinement proofs**
- Show that out-of-order implementation refines sequential specification
- Use simulation relation between states

**2. Invariant maintenance**
- RAT invariant: Mapping is injective (except x0)
- ROB invariant: Entries are program-ordered
- Free list invariant: No duplicates

**3. Inductive proofs**
- Prove property holds initially
- Prove property preserved by all state transitions

**4. Equivalence checking**
- Use LEC to verify code generation
- Symbolic simulation for pipeline stages

### Key Theorems to Prove

**Theorem 1: Register renaming correctness**
```lean
theorem rename_preserves_semantics :
  ∀ (prog : Program) (state_arch : ArchState) (state_phys : PhysState),
    relate state_arch state_phys →
    ⟦ prog ⟧_sequential state_arch = ⟦ prog ⟧_renamed state_phys
```

**Theorem 2: ROB maintains program order**
```lean
theorem rob_program_order :
  ∀ (rob : ROB) (i j : ROBIndex),
    older i j →
    commits rob i →
    commits rob j →
    commit_time rob i < commit_time rob j
```

**Theorem 3: Memory consistency**
```lean
theorem memory_ordering :
  ∀ (trace : ExecutionTrace),
    validTrace trace →
    sequentiallyConsistent (memoryOps trace)
```

**Theorem 4: Precise exceptions**
```lean
theorem precise_exceptions :
  ∀ (prog : Program) (state : CPUState),
    exception state →
    committed_state state = ⟦ prog_up_to_exception ⟧ initial_state
```

**Theorem 5: Top-level correctness**
```lean
theorem tomasulo_correct :
  ∀ (prog : Program),
    ⟦ prog ⟧_tomasulo ≈ ⟦ prog ⟧_riscv_spec
  where
    ≈ means "produces same final architectural state"
```

---

## Verification Plan

### Unit Tests (Component-level)

**Arithmetic units:**
- Test all ALU operations with random inputs
- Test multiplier with corner cases (0, -1, max values)
- Test divider with division by zero handling

**Sequential units:**
- Test register file read/write with various access patterns
- Test RAT allocation/deallocation
- Test ROB wrap-around at buffer boundaries

**Decoder:**
- Ensure all RV32IM instructions decode correctly
- Ensure illegal instructions are detected
- Test corner cases (reserved opcodes)

### Integration Tests (Subsystem-level)

**Reservation station + Execution unit:**
- Issue instructions with ready operands
- Issue instructions with pending operands (test CDB wakeup)
- Test back-pressure when RS full

**Rename + ROB + RS:**
- Test instruction dispatch pipeline
- Test register renaming with dependencies
- Test ROB commit with in-order retirement

**Memory subsystem:**
- Test load-store forwarding
- Test memory ordering violations
- Test store buffer operation

### System Tests (Full CPU)

**RISC-V compliance tests:**
Use official riscv-tests suite:
```bash
git clone https://github.com/riscv/riscv-tests
cd riscv-tests
./configure --prefix=/path/to/install
make
make install
```

Tests include:
- rv32ui-p-* (user-level integer tests, physical memory)
- rv32um-p-* (multiply/divide tests)
- rv32mi-p-* (machine-level tests, exceptions)

**Custom test programs:**
- Fibonacci (test basic arithmetic and branches)
- Matrix multiply (test memory and multiply)
- Quicksort (test complex control flow)
- Dhrystone benchmark (standard integer benchmark)

### Formal Verification

**Property checking:**
- Use bounded model checking (BMC) for finite traces
- Prove safety properties (no illegal states)
- Prove liveness properties (instructions eventually commit)

**Equivalence checking:**
- LEC between LEAN-generated and Chisel-generated RTL
- Compare against RISC-V golden model (Spike simulator)

### Performance Verification

**Metrics to measure:**
- **IPC (Instructions Per Cycle)** - Target: 1.5-2.0 for in-order-retire out-of-order-execute
- **Execution unit utilization** - Should be >70% for compute-heavy code
- **ROB occupancy** - Should be near-full for ILP-rich code
- **CDB contention** - Measure arbitration stalls

**Benchmarks:**
- Dhrystone
- Coremark
- Custom microbenchmarks (ALU-heavy, MEM-heavy, MUL-heavy)

---

## Performance Targets

### Cycle Time
- **Target:** 10 FO4 (fan-out-of-4 delays) for critical path
- **Critical paths:**
  - CDB broadcast → RS wakeup → execution
  - Execution → CDB arbitration → broadcast
  - Load address generation → cache access → forwarding

### IPC (Instructions Per Cycle)
- **Integer-heavy code:** 1.8-2.0 IPC
- **Memory-heavy code:** 0.8-1.2 IPC
- **Multiply-heavy code:** 1.0-1.5 IPC
- **Divide-heavy code:** 0.1-0.3 IPC (divider is non-pipelined)

### Scalability Parameters

| Parameter | Initial | Optimized |
|-----------|---------|-----------|
| Physical Registers | 64 | 96 |
| ROB Entries | 16 | 32 |
| ALU RS Entries | 4 | 8 |
| MUL RS Entries | 2 | 4 |
| DIV RS Entries | 1 | 2 |
| LD/ST RS Entries | 4 | 8 |
| CDB Width | 2 | 4 |

### Area Estimates (Technology-agnostic)

Measured in gate equivalents (GEs):

| Component | Estimated GEs |
|-----------|---------------|
| ALU | 5,000 |
| Multiplier | 15,000 |
| Divider | 8,000 |
| Register File (64×32-bit) | 20,000 |
| ROB (16 entries) | 10,000 |
| Reservation Stations | 15,000 |
| Decoder | 3,000 |
| Control Logic | 5,000 |
| **Total** | **~80,000 GEs** |

---

## Future Enhancements

### Phase 10: Caching & Memory Hierarchy

**Components to add:**
- L1 Instruction Cache (I$)
- L1 Data Cache (D$)
- TLB (Translation Lookaside Buffer)
- Cache coherence protocol (MESI/MOESI)

**Proofs needed:**
- Cache behavior refines main memory
- Coherence protocol maintains consistency

### Phase 11: Superscalar Features

**Enhancements:**
- Multiple issue (2-4 instructions per cycle)
- Multiple execution units (2 ALUs, 2 LSUs)
- Wider CDB (4-way broadcast)

**Challenges:**
- Increased arbitration complexity
- More complex dependency checking

### Phase 12: Branch Prediction

**Predictors to implement:**
- Bimodal predictor (2-bit saturating counters)
- Gshare (global history XOR PC)
- Tournament predictor (meta-predictor)
- Return address stack (RAS) for function returns

**Proofs needed:**
- Misprediction recovery is correct
- Speculative state discarded properly

### Phase 13: Speculative Execution Beyond Branches

**Features:**
- Load speculation (past unresolved stores)
- Memory disambiguation
- Speculative issue of dependent instructions

**Proofs needed:**
- Misspeculation recovery
- Replay mechanisms

### Phase 14: Privileged ISA (RV32I Privileged Spec)

**Add support for:**
- Machine mode (M-mode)
- User mode (U-mode)
- Supervisor mode (S-mode) - optional
- CSRs (Control and Status Registers)
- Traps and interrupts
- Virtual memory (Sv32 paging)

### Phase 15: Multicore & Coherence

**Extensions:**
- Multi-core configuration
- Cache coherence snooping
- Atomic operations (LR/SC, AMO)
- Interconnect (crossbar or NoC)

**Proofs needed:**
- Sequential consistency or relaxed memory model
- Atomic operation atomicity

### Phase 16: FPGA Prototype

**Targets:**
- Xilinx FPGA (Zynq UltraScale+)
- Intel FPGA (Stratix 10)

**Validation:**
- Run Linux on FPGA
- Boot real-world programs
- Compare performance to simulation

---

## Project Structure

```
Shoumei-RTL/
├── lean/
│   └── Shoumei/
│       ├── DSL.lean                    # Core DSL (extend with stateful)
│       ├── Semantics.lean              # Add sequential semantics
│       ├── Theorems.lean               # General theorems
│       ├── Codegen/
│       │   ├── Common.lean
│       │   ├── SystemVerilog.lean      # Extend for sequential
│       │   └── Chisel.lean             # Extend for sequential
│       ├── Circuits/
│       │   ├── Combinational/
│       │   │   ├── Adder.lean          # FullAdder, RippleCarry
│       │   │   ├── Multiplier.lean     # Array, Booth, Wallace
│       │   │   ├── Divider.lean        # Restoring, Non-restoring
│       │   │   ├── ALU.lean            # Complete ALU
│       │   │   ├── Comparator.lean
│       │   │   ├── Mux.lean
│       │   │   ├── Decoder.lean
│       │   │   └── Encoder.lean
│       │   ├── Sequential/
│       │   │   ├── DFF.lean            # D Flip-Flop
│       │   │   ├── Register.lean       # N-bit register
│       │   │   ├── RegisterFile.lean   # Multi-ported register file
│       │   │   ├── CAM.lean            # Content-addressable memory
│       │   │   ├── CircularBuffer.lean # FIFO for ROB
│       │   │   └── Arbiter.lean        # Round-robin, priority
│       │   └── Examples/
│       │       ├── Adder.lean          # Already exists
│       │       └── Counter.lean        # Simple sequential example
│       └── RISCV/
│           ├── ISA.lean                # RISC-V semantic spec
│           ├── OpcodeParser.lean       # Parse riscv-opcodes
│           ├── Decoder.lean            # Generated decoder
│           ├── RegisterFile.lean       # 32 architectural registers
│           ├── ALU.lean                # RV32I ALU operations
│           ├── Multiplier.lean         # RV32M multiply
│           ├── Divider.lean            # RV32M divide
│           ├── ReservationStation.lean # RS structure and logic
│           ├── ROB.lean                # Reorder buffer
│           ├── RAT.lean                # Register alias table
│           ├── FreeList.lean           # Physical register allocation
│           ├── CDB.lean                # Common data bus
│           ├── LSU.lean                # Load-store unit
│           ├── Memory.lean             # Data memory model
│           ├── Fetch.lean              # Instruction fetch unit
│           ├── Tomasulo.lean           # Top-level CPU
│           ├── Theorems/
│           │   ├── Renaming.lean       # Register renaming correctness
│           │   ├── ROB.lean            # Program order preservation
│           │   ├── Memory.lean         # Memory consistency
│           │   └── Correctness.lean    # End-to-end correctness
│           └── Tests/
│               ├── Compliance.lean     # RISC-V compliance tests
│               └── Benchmarks.lean     # Performance tests
├── chisel/
│   ├── src/main/scala/
│   │   ├── generated/              # LEAN-generated Chisel
│   │   │   ├── FullAdder.scala
│   │   │   ├── ALU.scala
│   │   │   ├── Multiplier.scala
│   │   │   ├── RegisterFile.scala
│   │   │   └── TomasuloCore.scala
│   │   └── runtime/                # Chisel support code
│   │       └── TopLevel.scala      # Testbench wrapper
│   └── build.sbt
├── verification/
│   ├── run-lec.sh                  # Yosys LEC
│   ├── smoke-test.sh               # Quick sanity checks
│   ├── FullAdder.eqy               # EQY config
│   ├── ALU.eqy
│   ├── Multiplier.eqy
│   ├── RegisterFile.eqy
│   ├── TomasuloCore.eqy
│   └── compliance/                 # RISC-V compliance tests
│       ├── run-tests.sh
│       └── results/
├── external/
│   └── riscv-opcodes/              # Git submodule
│       ├── opcodes
│       ├── opcodes-rv32m
│       └── parse.py
├── output/
│   ├── sv-from-lean/
│   └── sv-from-chisel/
├── docs/
│   ├── ARCHITECTURE.md             # High-level architecture
│   ├── ISA.md                      # RISC-V ISA summary
│   ├── MICROARCHITECTURE.md        # Detailed micro-arch
│   ├── PROOFS.md                   # Proof strategy and theorems
│   └── PERFORMANCE.md              # Performance analysis
├── Makefile
├── lakefile.lean
├── lean-toolchain
├── RISCV_TOMASULO_DESIGN.md        # This document
└── README.md
```

---

## Development Workflow

### Daily Development Loop

1. **Write LEAN definition** for new component
2. **Prove properties** about component behavior
3. **Generate SystemVerilog + Chisel** via code generators
4. **Run LEC** to verify both outputs match
5. **Integrate** with existing modules
6. **Run tests** (unit, integration, compliance)
7. **Commit** if all tests pass

### Continuous Integration

**GitHub Actions workflow:**
```yaml
- Build LEAN code
- Run code generators
- Compile Chisel
- Run LEC on all modules
- Run RISC-V compliance tests (when CPU complete)
- Performance benchmarks (optional, long-running)
```

### Code Review Checklist

- [ ] All proofs compile without `sorry`
- [ ] LEC passes for generated RTL
- [ ] Unit tests pass
- [ ] Code follows style guide (LEAN and Scala)
- [ ] Documentation updated (if architectural change)
- [ ] Performance impact measured (if applicable)

---

## Success Criteria

**Phase 0 Complete:** ✅ 100% DONE (2026-01-31)
- [x] Sequential circuit DSL working (State, evalCycleSequential)
- [x] DFF implemented and proven (8 theorems)
- [x] N-bit Register implemented and proven (concrete + inductive)
- [x] Queue/FIFO implemented with formal semantics (20+ theorems)
- [x] Queue properties proven (FIFO ordering, overflow/underflow)
- [x] DFF verified with LEC (SEC working)
- [x] Queue code generation (SystemVerilog/Chisel)
- [x] Queue verified with LEC (Queue1_8, Queue1_32 passing)

**Phase 1 In Progress:** 🔄 17% DONE
- [x] DSL enhanced with hierarchical circuit composition (`Circuit.inline`)
- [x] RippleCarryAdder32 implemented (160 gates, 32 FullAdders)
- [x] RCA structural proofs (3 theorems verified)
- [x] RCA builds successfully with `lake build`
- [ ] RCA code generation (SystemVerilog/Chisel)
- [ ] RCA verified with LEC
- [ ] Subtractor32 and Comparator32 implemented
- [ ] LogicUnit32 (AND/OR/XOR) implemented
- [ ] Shifter32 (barrel shifter) implemented
- [ ] ALU32 core complete (all RV32I operations)
- [ ] 50+ RV32I compliance tests
- [ ] All Phase 1 components verified with LEC

**Phase 2 Complete:**
- [ ] RISC-V decoder generated from riscv-opcodes
- [ ] Decoder completeness proved
- [ ] All RV32IM instructions decode correctly

**Phase 3-7 Complete:**
- [ ] All Tomasulo components implemented
- [ ] All components verified with LEC
- [ ] Integration tests pass

**Phase 8 Complete:**
- [ ] Full CPU integrated
- [ ] Simple programs run correctly (manually verified)

**Phase 9 Complete:**
- [ ] RISC-V compliance tests pass (rv32ui, rv32um)
- [ ] End-to-end correctness theorem proved
- [ ] Performance targets met (IPC > 1.5)

**Final Milestone:**
- [ ] Boots Linux on FPGA (future)

---

## Timeline Estimate

**Conservative estimate (assuming 20 hours/week):**

| Phase | Duration | Cumulative |
|-------|----------|------------|
| Phase 0: Sequential DSL | 3 weeks | 3 weeks |
| Phase 1: Arithmetic units | 4 weeks | 7 weeks |
| Phase 2: Decoder | 3 weeks | 10 weeks |
| Phase 3: Renaming | 4 weeks | 14 weeks |
| Phase 4: Reservation stations | 5 weeks | 19 weeks |
| Phase 5: Execution units | 4 weeks | 23 weeks |
| Phase 6: ROB | 4 weeks | 27 weeks |
| Phase 7: Memory | 3 weeks | 30 weeks |
| Phase 8: Integration | 6 weeks | 36 weeks |
| Phase 9: Verification | 4 weeks | 40 weeks |

**Total: ~40 weeks (~10 months) for complete verified RV32IM Tomasulo CPU**

This is an ambitious timeline for a single developer. With a team of 2-3, could be reduced to 6 months.

---

## Open Questions

1. **Memory model complexity:** Do we start with idealized single-cycle memory, or model realistic SRAM timing from the start?
   - **Recommendation:** Start simple (single-cycle), add realistic timing later

2. **Branch predictor:** Include in initial design, or add later?
   - **Recommendation:** Start with always-not-taken, add predictor in Phase 10+

3. **Exception handling:** Full support for traps/interrupts, or simplified?
   - **Recommendation:** Simplified initially (just illegal instruction), full support in Phase 14

4. **Cache coherence:** Single-core only, or plan for multi-core from the start?
   - **Recommendation:** Single-core initially, multi-core in Phase 15

5. **FPGA target:** Should we keep FPGA constraints in mind during design?
   - **Recommendation:** Yes, but don't over-optimize early. Target Xilinx UltraScale+ later.

6. **Toolchain:** Stick with open-source tools (Yosys, Verilator) or use commercial (Synopsys, Cadence)?
   - **Recommendation:** Open-source for development, commercial for final verification

---

## References

### Tomasulo's Algorithm
- Original paper: R. M. Tomasulo, "An Efficient Algorithm for Exploiting Multiple Arithmetic Units," IBM Journal of Research and Development, 1967
- Computer Architecture textbooks: Hennessy & Patterson, "Computer Architecture: A Quantitative Approach"

### RISC-V
- RISC-V ISA Specification: https://riscv.org/technical/specifications/
- riscv-opcodes repository: https://github.com/riscv/riscv-opcodes
- riscv-tests (compliance tests): https://github.com/riscv/riscv-tests
- Spike (ISA simulator): https://github.com/riscv/riscv-isa-sim

### Formal Verification of CPUs
- "Formal Verification of a Pipelined Microprocessor" (Burch & Dill, 1994)
- "Verifying a Synthesizable HOL Processor" (Fox, 2003)
- "End-to-End Verification of ARM Processors with ISA-Formal" (Reid et al., 2016)

### LEAN4 Resources
- Lean 4 Manual: https://lean-lang.org/lean4/doc/
- Theorem Proving in Lean 4: https://leanprover.github.io/theorem_proving_in_lean4/
- Functional Programming in Lean: https://leanprover.github.io/functional_programming_in_lean/

### Hardware Verification
- "Hardware Verification with SystemVerilog Assertions" (Vijayaraghavan & Ramanathan)
- "Formal Verification: An Essential Toolkit for Modern VLSI Design" (Mehler et al.)
- ABC system: https://people.eecs.berkeley.edu/~alanmi/abc/

---

## Conclusion

This design document outlines an ambitious but achievable path to building a **formally verified, out-of-order RISC-V CPU** using the Shoumei RTL framework.

**Key innovations:**
1. **Formally proven correctness** - All components verified in LEAN4
2. **Dual code generation** - Both SystemVerilog and Chisel from single source
3. **LEC validation** - Formal equivalence checking at every level
4. **Bottom-up verification** - Small proven components compose into larger proven systems

**Next steps:**
1. ✅ ~~Phase 0: Extend DSL for sequential circuits~~ - COMPLETE
2. ✅ ~~Start implementing arithmetic building blocks~~ - IN PROGRESS
3. **Current:** Complete Phase 1 MVP (Subtractor, Comparator, LogicUnit, Shifter, ALU32)
4. **Next:** Set up riscv-opcodes integration (Phase 2)
5. **Future:** Register renaming infrastructure (Phase 3)

The journey from FullAdder to Tomasulo CPU will push the boundaries of proven hardware design. Let's build something remarkable! 🚀

---

**Document Status:** Active Development - Phase 1 (17% Complete)
**Last Updated:** 2026-01-31 (Phase 1: RippleCarryAdder32 + DSL hierarchical composition)
**Author:** Claude Code (with human guidance)
**Project:** 証明 Shoumei RTL - Formally Verified Hardware Design

**Recent Milestones:**
- ✅ Phase 0 Complete (2026-01-31): Queue/FIFO with full verification pipeline
- 🔄 Phase 1 Started (2026-01-31): RippleCarryAdder32 with hierarchical composition

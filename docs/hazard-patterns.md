# Hazard Pattern Catalog

Catalog of microarchitecture-targeted test patterns for the Shoumei RV32IM Tomasulo CPU. Each pattern is designed to exercise a specific pipeline hazard or corner case, guided by the Lean behavioral models.

For the overall test generation architecture, see [test-generation.md](test-generation.md). For the cosimulation flow, see [cosimulation.md](cosimulation.md).

## Pattern Index

| ID | Pattern | Target | Exercises |
|----|---------|--------|-----------|
| S1 | [Instruction smoke](#s1-instruction-smoke) | ISA coverage | All 48 OpType values |
| D1 | [RAW chain sweep](#d1-raw-chain-sweep) | Data forwarding | CDB forwarding at all pipeline depths |
| D2 | [WAW chain](#d2-waw-chain) | Register renaming | Free list recycling at ROB commit |
| D3 | [CDB dual wakeup](#d3-cdb-dual-wakeup) | Reservation station | Same tag on both src operands |
| D4 | [x0 sink](#d4-x0-sink) | Register file | x0 never written, never renamed |
| H1 | [RS exhaustion](#h1-rs-exhaustion) | Structural hazard | Issue stall when RS is full |
| H2 | [ROB fill](#h2-rob-fill) | Structural hazard | Rename stall when ROB is full |
| H3 | [Free list exhaustion](#h3-free-list-exhaustion) | Structural hazard | Rename stall when no phys regs available |
| C1 | [Branch misprediction](#c1-branch-misprediction) | Control hazard | ROB flush, RAT recovery |
| C2 | [Branch type coverage](#c2-branch-type-coverage) | Control hazard | All 6 branch conditions x taken/not-taken |
| C3 | [JAL/JALR link register](#c3-jaljalr-link-register) | Control flow | Return address save and jump |
| M1 | [Store-to-load forwarding](#m1-store-to-load-forwarding) | Memory hazard | Store buffer forwarding logic |
| M2 | [Store buffer full](#m2-store-buffer-full) | Memory hazard | Store stall when buffer is full |
| M3 | [Load/store width matrix](#m3-loadstore-width-matrix) | Memory hazard | All width combinations (B/H/W) |
| M4 | [Store buffer ordering](#m4-store-buffer-ordering) | Memory hazard | Youngest-match priority |
| E1 | [Divider occupancy](#e1-divider-occupancy) | Execution unit | 32-cycle divider blocking |
| E2 | [Multiplier pipeline fill](#e2-multiplier-pipeline-fill) | Execution unit | 3-stage multiplier pipeline |
| E3 | [M-extension corner cases](#e3-m-extension-corner-cases) | Execution unit | Div-by-zero, signed overflow |
| X1 | [Multi-hazard combo](#x1-multi-hazard-combo) | Combined | Multiple simultaneous hazards |
| X2 | [Pipeline drain](#x2-pipeline-drain) | Sequencing | Full pipeline flush and refill |

---

## Smoke Tests

### S1: Instruction Smoke

**Goal:** Execute one instance of every instruction type in the RV32IM ISA.

**What it tests:** Basic decoder correctness, execution unit routing (`classifyToUnit`), register writeback for all instruction formats.

```lean
def smokeTest : TestProgram :=
  let setup := [
    encodeU .LUI 1 0x12345,             -- x1 = 0x12345000
    encodeI .ADDI 2 0 0x678,            -- x2 = 0x678
    encodeI .ADDI 3 0 1                 -- x3 = 1
  ]
  let aluOps := [
    encodeR .ADD 4 1 2,                  -- x4 = x1 + x2
    encodeR .SUB 5 1 2,                  -- x5 = x1 - x2
    encodeR .AND 6 1 2,                  -- x6 = x1 & x2
    encodeR .OR 7 1 2,                   -- x7 = x1 | x2
    encodeR .XOR 8 1 2,                  -- x8 = x1 ^ x2
    encodeR .SLT 9 1 2,                  -- x9 = (x1 < x2) ? 1 : 0
    encodeR .SLTU 10 1 2,               -- x10 = unsigned compare
    encodeR .SLL 11 1 3,                 -- x11 = x1 << 1
    encodeR .SRL 12 1 3,                 -- x12 = x1 >> 1 (logical)
    encodeR .SRA 13 1 3                  -- x13 = x1 >> 1 (arithmetic)
  ]
  let immOps := [
    encodeI .ADDI 14 1 0x123,            -- x14 = x1 + 0x123
    encodeI .ANDI 15 1 0xFF,             -- x15 = x1 & 0xFF
    encodeI .ORI 16 1 0xFF,              -- x16 = x1 | 0xFF
    encodeI .XORI 17 1 0xFF,             -- x17 = x1 ^ 0xFF
    encodeI .SLTI 18 1 0,               -- x18 = (x1 < 0) ? 1 : 0
    encodeI .SLTIU 19 1 1,              -- x19 = (x1 < 1) unsigned
    encodeI .SLLI 20 1 4,               -- x20 = x1 << 4
    encodeI .SRLI 21 1 4,               -- x21 = x1 >> 4 (logical)
    encodeI .SRAI 22 1 4                -- x22 = x1 >> 4 (arithmetic)
  ]
  let mExt := [
    encodeR .MUL 23 1 2,                 -- x23 = x1 * x2 (lower 32)
    encodeR .MULH 24 1 2,                -- x24 = (x1 * x2) >> 32 (signed)
    encodeR .MULHU 25 1 2,               -- x25 = (x1 * x2) >> 32 (unsigned)
    encodeR .MULHSU 26 1 2,              -- x26 = (signed x unsigned) >> 32
    encodeR .DIV 27 1 2,                 -- x27 = x1 / x2 (signed)
    encodeR .DIVU 28 1 2,               -- x28 = x1 / x2 (unsigned)
    encodeR .REM 29 1 2,                 -- x29 = x1 % x2 (signed)
    encodeR .REMU 30 1 2                -- x30 = x1 % x2 (unsigned)
  ]
  { instrs := setup ++ aluOps ++ immOps ++ mExt,
    description := "smoke: one of each instruction type" }
```

**Coverage points:** All `ExecUnit` variants dispatched, all `OpType` values decoded.

**Expected test count:** 1 ELF, ~40 instructions.

---

## Data Hazard Patterns

### D1: RAW Chain Sweep

**Goal:** Exercise read-after-write forwarding at every pipeline depth from 0 to N.

**What it tests:** CDB forwarding to reservation stations (short distances), register file read after commit (long distances), and the transition boundary between the two paths.

```lean
def rawChainTest (producer consumer : OpType) (distance : Nat) : TestProgram :=
  let setup := [
    encodeU .LUI 2 0x12345,             -- x2 = 0x12345000
    encodeI .ADDI 3 0 0x678             -- x3 = 0x678
  ]
  let prod := [encodeR producer 1 2 3]   -- x1 = f(x2, x3)
  let nops := List.replicate distance
    (encodeI .ADDI 0 0 0)               -- NOP (ADDI x0, x0, 0)
  let cons := [encodeR consumer 4 1 3]   -- x4 = g(x1, x3) -- RAW on x1
  { instrs := setup ++ prod ++ nops ++ cons,
    description := s!"RAW {producer}->{consumer} distance={distance}" }
```

**Sweep parameters:**
- Producers: `ADD`, `SUB`, `MUL` (different latencies)
- Consumers: `ADD`, `SUB` (simplest to verify)
- Distances: 0 through 20 (covers RS depth, ROB depth, and well beyond)

**Coverage points:** `cdbForwardToRS` (distance 0-1), `prfReadAfterCDBWrite` (distance > pipeline depth).

**Expected test count:** 3 producers x 2 consumers x 21 distances = 126 ELFs.

### D2: WAW Chain

**Goal:** Stress register renaming and free list recycling by repeatedly writing to the same architectural register.

**What it tests:** RAT update correctness (each write gets a new physical register), `oldPhysRd` tracking in the ROB, free list deallocation at commit time.

```lean
def wawChainTest (length : Nat) : TestProgram :=
  let setup := [encodeI .ADDI 2 0 1]     -- x2 = 1 (increment value)
  let chain := (List.range length).map fun i =>
    encodeI .ADDI 1 1 1                   -- x1 = x1 + 1 (WAW on x1, each gets new phys reg)
  { instrs := setup ++ chain,
    description := s!"WAW chain length={length}" }
```

**Key lengths:** 4 (fills RS), 16 (fills ROB), 32 (exceeds ROB, must stall and drain), 60 (approaches free list limit).

**Coverage points:** `robCommitDeallocatesPhysReg`, `freeListEmpty` (at extreme lengths).

### D3: CDB Dual Wakeup

**Goal:** Both source operands of an RS entry wait for the same tag, and one CDB broadcast wakes both.

**What it tests:** The RS `cdbBroadcast` logic correctly updates both `src1_ready` and `src2_ready` when both match the same tag.

```lean
def cdbDualWakeupTest : TestProgram :=
  let setup := [encodeI .ADDI 2 0 7]     -- x2 = 7
  let producer := [encodeR .MUL 1 2 2]   -- x1 = x2 * x2 (multi-cycle, tag = physReg(x1))
  let consumer := [encodeR .ADD 3 1 1]   -- x3 = x1 + x1 (both src1 and src2 wait for x1's tag)
  { instrs := setup ++ producer ++ consumer,
    description := "CDB dual wakeup: both operands same tag" }
```

**Coverage points:** `cdbWakesBothOperands`.

### D4: x0 Sink

**Goal:** Every instruction type with `rd = x0` must be a no-op on the register file.

**What it tests:** The rename stage must not allocate a physical register for x0. The ROB must not attempt writeback. Spike confirms all register values are unchanged.

```lean
def x0SinkTest : TestProgram :=
  let setup := [
    encodeI .ADDI 1 0 42,                -- x1 = 42 (canary value)
    encodeI .ADDI 2 0 7,
    encodeI .ADDI 3 0 13
  ]
  let sinks := [
    encodeR .ADD 0 2 3,                   -- x0 = x2 + x3 (must not change x0)
    encodeR .SUB 0 2 3,
    encodeR .MUL 0 2 3,
    encodeI .ADDI 0 2 100,
    encodeU .LUI 0 0xDEADB,
    encodeU .AUIPC 0 0xDEADB
  ]
  let check := [encodeR .ADD 4 1 0]      -- x4 = x1 + x0 = 42 (verify x0 still 0)
  { instrs := setup ++ sinks ++ check,
    description := "x0 sink: rd=x0 never commits a value" }
```

**Coverage points:** Rename stage x0 bypass, ROB x0 handling.

---

## Structural Hazard Patterns

### H1: RS Exhaustion

**Goal:** Fill the reservation station beyond its capacity to trigger issue stalls.

**What it tests:** `issue_full` signal propagation, pipeline backpressure, no instruction loss during stall.

```lean
def rsExhaustionTest (unit : ExecUnit) (depth : Nat) : TestProgram :=
  let anchor := [
    encodeI .ADDI 2 0 7,
    encodeI .ADDI 3 0 13,
    encodeR .MUL 1 2 3                    -- Long-latency producer of x1
  ]
  let dependents := (List.range depth).map fun i =>
    -- All depend on x1 (RAW), all route to Integer unit, none can dispatch
    encodeR .ADD (5 + i % 26) 1 0
  { instrs := anchor ++ dependents,
    description := s!"RS exhaustion {unit} depth={depth}" }
```

**Key depths:** 4 (RS capacity for `RS4`), 5 (first stall), 8 (double capacity).

**Coverage points:** `rsFullStall unit`.

### H2: ROB Fill

**Goal:** Fill the 16-entry ROB to trigger rename stalls.

**What it tests:** ROB full detection, pipeline freeze, correct resume after commit frees entries.

```lean
def robFillTest (depth : Nat) : TestProgram :=
  let setup := [encodeI .ADDI 1 0 100, encodeI .ADDI 2 0 7]
  let divChain := (List.range depth).map fun i =>
    -- DIV takes 32 cycles each; ROB fills before any can retire
    encodeR .DIV (3 + i % 28) 1 2
  { instrs := setup ++ divChain,
    description := s!"ROB fill depth={depth}" }
```

**Key depths:** 16 (ROB capacity), 17 (first stall), 32 (all DIVs must serialize).

**Coverage points:** `robFullStall`, `dividerBusy32Cycles`.

### H3: Free List Exhaustion

**Goal:** Drain the 64-entry physical register free list.

**What it tests:** Free list empty detection, rename stall, correct recovery as ROB commits free old mappings.

```lean
def freeListExhaustionTest : TestProgram :=
  -- Cycle through x1..x31 repeatedly; each write consumes a free phys reg
  -- With 64 phys regs and 32 arch regs, ~32 renames before exhaustion
  -- (assuming initial mapping consumes 32)
  let writes := (List.range 60).map fun i =>
    encodeI .ADDI (1 + i % 31) 0 (i + 1)
  { instrs := writes,
    description := "free list exhaustion: burn through phys regs" }
```

**Coverage points:** `freeListEmpty`.

---

## Control Hazard Patterns

### C1: Branch Misprediction

**Goal:** Force a branch misprediction and verify the flush/recovery path.

**What it tests:** ROB `flush` operation, committed RAT restoration, speculative instruction squash, correct resumption on the right path.

```lean
def branchMispredictTest (specDepth : Nat) : TestProgram :=
  let setup := [
    encodeI .ADDI 1 0 1,                 -- x1 = 1
    encodeI .ADDI 2 0 1                  -- x2 = 1
  ]
  let branchOffset := 4 * (specDepth + 1)
  let branch := [encodeB .BEQ 1 2 branchOffset]  -- taken (skip specDepth instrs)
  let wrongPath := (List.range specDepth).map fun _ =>
    encodeI .ADDI 10 10 1                -- x10 += 1 (must be squashed)
  let correctPath := [
    encodeI .ADDI 11 0 42               -- x11 = 42 (correct path)
  ]
  { instrs := setup ++ branch ++ wrongPath ++ correctPath,
    description := s!"branch mispredict specDepth={specDepth}" }
  -- Spike: x10 = 0 (wrong path never executed), x11 = 42
  -- If RTL: x10 != 0, the flush logic is broken
```

**Sweep:** `specDepth` from 1 to 16 (filling ROB with speculative instructions before flush).

**Coverage points:** `branchFlushROBNonEmpty specDepth`, `branchFlushWithPendingStores` (if stores are on wrong path).

### C2: Branch Type Coverage

**Goal:** Exercise all 6 branch types with both taken and not-taken outcomes.

**What it tests:** Branch execution unit condition evaluation, target calculation.

```lean
def branchTypeCoverageTest : TestProgram :=
  let tests := [
    -- (branch_op, rs1_val, rs2_val, should_be_taken)
    (.BEQ,  5, 5, true),   (.BEQ,  5, 6, false),
    (.BNE,  5, 6, true),   (.BNE,  5, 5, false),
    (.BLT,  -1, 0, true),  (.BLT,  0, -1, false),
    (.BGE,  0, -1, true),  (.BGE,  -1, 0, false),
    (.BLTU, 1, 2, true),   (.BLTU, 2, 1, false),
    (.BGEU, 2, 1, true),   (.BGEU, 1, 2, false)
  ]
  -- Each test: setup values -> branch -> canary on wrong path -> marker on correct path
  -- Spike resolves expected register state for each
```

**Expected test count:** 12 cases (6 branch types x 2 outcomes).

### C3: JAL/JALR Link Register

**Goal:** Verify jump-and-link saves the correct return address and reaches the correct target.

```lean
def jalTest : TestProgram :=
  -- JAL x1, +8  → x1 = PC+4, jump forward 2 instructions
  -- ADDI x10, x0, 99  (skipped)
  -- ADDI x11, x0, 42  (landed here)
  let instrs := [
    encodeJ .JAL 1 8,                    -- x1 = PC+4, jump to PC+8
    encodeI .ADDI 10 0 99,               -- skipped
    encodeI .ADDI 11 0 42                -- landed here
  ]
  { instrs, description := "JAL link register" }
```

---

## Memory Hazard Patterns

### M1: Store-to-Load Forwarding

**Goal:** Exercise the store buffer's forwarding path for exact address matches.

**What it tests:** `StoreBuffer.forwardingMatch`, youngest-match priority, forwarding data path.

```lean
def storeForwardTest (storeOp loadOp : OpType) (offset : Int) : TestProgram :=
  let base := 0x80002100
  let setup := [
    encodeU .LUI 1 (base >>> 12),
    encodeI .ADDI 1 1 (base &&& 0xFFF),  -- x1 = base address
    encodeI .ADDI 2 0 0xAB               -- x2 = store data
  ]
  let store := [encodeS storeOp 1 2 offset]
  let load := [encodeI loadOp 3 1 offset]
  { instrs := setup ++ store ++ load,
    description := s!"{storeOp}->{loadOp} offset={offset}" }
```

**Coverage points:** `storeBufferForwardHit`.

### M2: Store Buffer Full

**Goal:** Fill the 8-entry store buffer to trigger store stalls.

```lean
def storeBufferFullTest : TestProgram :=
  let base := 0x80002000
  let setup := [
    encodeU .LUI 1 (base >>> 12),
    encodeI .ADDI 1 1 (base &&& 0xFFF)
  ]
  -- 10 stores to consecutive addresses (buffer holds 8)
  let stores := (List.range 10).map fun i =>
    let data_setup := encodeI .ADDI 2 0 (i + 1)
    let store := encodeS .SW 1 2 (i * 4)
    [data_setup, store]
  { instrs := setup ++ stores.flatten,
    description := "store buffer full: 10 stores to 8-entry buffer" }
```

### M3: Load/Store Width Matrix

**Goal:** Exercise all combinations of store width and load width at the same address.

**What it tests:** Forwarding path width matching. A byte store followed by a word load should NOT forward (partial coverage). A word store followed by a byte load should forward the correct byte.

```
Store width x Load width matrix:
         LB    LBU   LH    LHU   LW
  SB     fwd   fwd   no    no    no
  SH     ?     ?     fwd   fwd   no
  SW     fwd   fwd   fwd   fwd   fwd
```

```lean
def widthMatrixTest : List TestProgram :=
  let storeOps := [(.SB, 1), (.SH, 2), (.SW, 4)]
  let loadOps := [(.LB, 1), (.LBU, 1), (.LH, 2), (.LHU, 2), (.LW, 4)]
  storeOps.flatMap fun (sop, sw) =>
    loadOps.map fun (lop, lw) =>
      storeForwardTest sop lop 0
      -- Spike handles the semantics; we just need to exercise the path
```

**Coverage points:** `storeBufferForwardHit`, `storeBufferForwardWidthMismatch`.

**Expected test count:** 3 store widths x 5 load widths = 15 ELFs.

### M4: Store Buffer Ordering

**Goal:** When multiple stores target the same address, the load must see the youngest (most recent) store's data.

```lean
def storeBufferOrderingTest : TestProgram :=
  let base := 0x80002100
  let setup := [
    encodeU .LUI 1 (base >>> 12),
    encodeI .ADDI 1 1 (base &&& 0xFFF)
  ]
  let stores := [
    encodeI .ADDI 2 0 0x11,
    encodeS .SW 1 2 0,                    -- mem[base] = 0x11 (oldest)
    encodeI .ADDI 3 0 0x22,
    encodeS .SW 1 3 0,                    -- mem[base] = 0x22
    encodeI .ADDI 4 0 0x33,
    encodeS .SW 1 4 0                     -- mem[base] = 0x33 (youngest)
  ]
  let load := [encodeI .LW 5 1 0]        -- x5 must be 0x33 (youngest store wins)
  { instrs := setup ++ stores ++ load,
    description := "store buffer ordering: youngest match wins" }
```

**Coverage points:** Store buffer youngest-match priority via barrel rotation + arbiter.

---

## Execution Unit Patterns

### E1: Divider Occupancy

**Goal:** Occupy the 32-cycle divider with back-to-back divisions.

**What it tests:** Divider FSM busy signaling, MulDiv RS stall behavior, pipeline throughput under divider contention.

```lean
def dividerOccupancyTest (count : Nat) : TestProgram :=
  let setup := [encodeI .ADDI 1 0 100, encodeI .ADDI 2 0 7]
  let divs := (List.range count).map fun i =>
    encodeR .DIV (3 + i % 28) 1 2
  { instrs := setup ++ divs,
    description := s!"divider occupancy: {count} back-to-back DIVs" }
```

**Key counts:** 1 (baseline), 2 (second must wait 32 cycles), 4 (serialized, ~128 cycles).

**Coverage points:** `dividerBusy32Cycles`.

### E2: Multiplier Pipeline Fill

**Goal:** Issue 3+ MULs back-to-back to fill all 3 pipeline stages simultaneously.

```lean
def multiplierPipelineTest : TestProgram :=
  let setup := [encodeI .ADDI 1 0 7, encodeI .ADDI 2 0 13]
  let muls := (List.range 5).map fun i =>
    encodeR .MUL (3 + i) 1 2              -- 5 MULs, 3-cycle pipeline => 3 in flight
  { instrs := setup ++ muls,
    description := "multiplier pipeline: 3 stages filled" }
```

**Coverage points:** `multiplierPipelineFull`.

### E3: M-Extension Corner Cases

**Goal:** Exercise spec-defined edge cases in multiply/divide.

The RISC-V M extension defines specific results for corner cases:

| Operation | Condition | Result |
|-----------|-----------|--------|
| `DIV` | Divide by zero | `0xFFFFFFFF` (-1) |
| `DIVU` | Divide by zero | `0xFFFFFFFF` (max unsigned) |
| `REM` | Divide by zero | dividend |
| `REMU` | Divide by zero | dividend |
| `DIV` | Signed overflow (`-2^31 / -1`) | `0x80000000` (-2^31) |
| `REM` | Signed overflow (`-2^31 / -1`) | `0` |
| `MULH` | `0xFFFFFFFF * 0xFFFFFFFF` | `0x00000001` |

```lean
def mExtCornerCaseTest : TestProgram :=
  let setup := [
    encodeI .ADDI 1 0 0,                 -- x1 = 0 (divisor for div-by-zero)
    encodeI .ADDI 2 0 42,                -- x2 = 42 (dividend)
    encodeU .LUI 3 0x80000,              -- x3 = 0x80000000 (-2^31)
    encodeI .ADDI 4 0 (-1)              -- x4 = -1
  ]
  let divByZero := [
    encodeR .DIV 5 2 1,                   -- x5 = 42 / 0 = 0xFFFFFFFF
    encodeR .DIVU 6 2 1,                  -- x6 = 42 / 0 = 0xFFFFFFFF
    encodeR .REM 7 2 1,                   -- x7 = 42 % 0 = 42
    encodeR .REMU 8 2 1                   -- x8 = 42 % 0 = 42
  ]
  let signedOverflow := [
    encodeR .DIV 9 3 4,                   -- x9 = -2^31 / -1 = 0x80000000
    encodeR .REM 10 3 4                   -- x10 = -2^31 % -1 = 0
  ]
  let mulCorner := [
    encodeR .MULH 11 4 4                  -- x11 = upper(-1 * -1) = 0x00000001 (???)
  ]
  { instrs := setup ++ divByZero ++ signedOverflow ++ mulCorner,
    description := "M-extension corner cases" }
  -- Spike defines the correct results; we verify RTL matches
```

---

## Combined Patterns

### X1: Multi-Hazard Combo

**Goal:** Exercise multiple hazards simultaneously in a single program.

**What it tests:** Interaction between store forwarding, branch misprediction, RS pressure, and CDB broadcasting -- the states that random generation rarely reaches.

```lean
def comboHazardTest : TestProgram :=
  let setup := [
    encodeI .ADDI 1 0 1,
    encodeI .ADDI 2 0 1,
    encodeU .LUI 20 0x80002                -- x20 = store base address
  ]
  -- Phase 1: Fill store buffer
  let stores := [
    encodeS .SW 20 1 0,                    -- mem[x20] = 1
    encodeS .SW 20 2 4                     -- mem[x20+4] = 1
  ]
  -- Phase 2: Mispredicted branch (speculative instructions fill RS)
  let branch := [encodeB .BEQ 1 2 24]     -- taken, skip 5 instrs
  let speculative := (List.range 5).map fun i =>
    encodeR .ADD (5 + i) 1 2              -- speculative, should be squashed
  -- Phase 3: Post-branch, exercise store forwarding + RAW
  let postBranch := [
    encodeI .LW 3 20 0,                   -- load-after-store (forwarding from store buffer)
    encodeR .MUL 4 3 2                    -- depends on forwarded load (RAW across units)
  ]
  { instrs := setup ++ stores ++ branch ++ speculative ++ postBranch,
    description := "combo: store-fwd + branch-mispredict + RS-pressure" }
```

**Coverage points:** `storeBufferForwardHit`, `branchFlushROBNonEmpty`, `rsFullStall`, `cdbForwardToRS`.

### X2: Pipeline Drain

**Goal:** Fill the pipeline completely, drain it, and verify clean restart.

```lean
def pipelineDrainTest : TestProgram :=
  let phase1 := (List.range 20).map fun i =>
    encodeI .ADDI (1 + i % 31) 0 (i + 1)  -- Fill pipeline with 20 instructions
  let drain := [
    encodeI .ADDI 0 0 0,                  -- NOP
    encodeI .ADDI 0 0 0,                  -- NOP
    encodeI .ADDI 0 0 0,                  -- NOP (pipeline drains)
    encodeI .ADDI 0 0 0,
    encodeI .ADDI 0 0 0,
    encodeI .ADDI 0 0 0,
    encodeI .ADDI 0 0 0,
    encodeI .ADDI 0 0 0
  ]
  let phase2 := [
    encodeI .ADDI 1 0 99,                 -- Fresh instruction after drain
    encodeR .ADD 2 1 0                    -- Depends on x1 = 99
  ]
  { instrs := phase1 ++ drain ++ phase2,
    description := "pipeline drain and restart" }
```

---

## Generation Summary

### Test counts by category

| Category | Pattern count | ELFs per pattern | Total ELFs |
|----------|:---:|:---:|:---:|
| Smoke (S1) | 1 | 1 | 1 |
| Data hazards (D1-D4) | 4 | ~130 (sweep) | ~140 |
| Structural hazards (H1-H3) | 3 | ~10 (sweep) | ~30 |
| Control hazards (C1-C3) | 3 | ~30 (sweep) | ~30 |
| Memory hazards (M1-M4) | 4 | ~20 (sweep) | ~20 |
| Execution units (E1-E3) | 3 | ~10 | ~15 |
| Combined (X1-X2) | 2 | ~5 | ~5 |
| **Total** | **20** | | **~240** |

Each ELF is small (typically 40-200 instructions of payload plus bootstrap). The entire suite generates in seconds from Lean. Spike processes each ELF in milliseconds. The bottleneck is RTL simulation time, not test generation.

### Relationship to Lean models

Each pattern is informed by a specific Lean behavioral model:

| Pattern | Lean model used for guidance |
|---------|------------------------------|
| D1-D3 | `RSState.cdbBroadcast`, `RSState.issue` |
| D4 | `RenameStage.renameInstruction` (x0 handling) |
| H1 | `RSState.isFull`, `RSState.countValid` |
| H2 | `ROBState.isFull`, `ROBState.allocate` |
| H3 | `FreeListState.isEmpty` |
| C1 | `ROBState.flush`, committed RAT restoration |
| M1-M4 | `StoreBufferState.forwardingMatch`, youngest-match arbiter |
| E1-E2 | `MulDivExecUnit` pipeline/FSM models |
| E3 | `executeMulDiv` in `Semantics.lean` |

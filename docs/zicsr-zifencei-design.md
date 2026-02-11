# Zicsr + Zifencei Design Document

Design options for adding CSR access (Zicsr) and instruction-fence (Zifencei) to the Shoumei RV32IMF Tomasulo CPU. Two approaches: a short-term serialize strategy (Option A) and a long-term microcode strategy (Option C) that scales to the full privileged ISA.

For pipeline architecture context, see the top-level comment in `lean/Shoumei/RISCV/CPU.lean`. For verification approach, see [verification-guide.md](verification-guide.md).

---

## ISA Summary

### Zicsr (6 instructions)

All six are read-modify-write on a CSR:

| Instruction | Semantics |
|---|---|
| `CSRRW  rd, csr, rs1` | `t = CSR[csr]; CSR[csr] = rs1; rd = t` |
| `CSRRS  rd, csr, rs1` | `t = CSR[csr]; CSR[csr] = t \| rs1; rd = t` |
| `CSRRC  rd, csr, rs1` | `t = CSR[csr]; CSR[csr] = t & ~rs1; rd = t` |
| `CSRRWI rd, csr, zimm` | `t = CSR[csr]; CSR[csr] = zimm; rd = t` |
| `CSRRSI rd, csr, zimm` | `t = CSR[csr]; CSR[csr] = t \| zimm; rd = t` |
| `CSRRCI rd, csr, zimm` | `t = CSR[csr]; CSR[csr] = t & ~zimm; rd = t` |

Special cases per the spec:
- `rs1 = x0` (or `zimm = 0`) on CSRRS/CSRRC variants: **no write** to CSR. This matters because some CSRs have read side-effects that differ from read-write side-effects.
- `rd = x0` on CSRRW: **no read** from CSR (write-only). Avoids read side-effects.

### Zifencei (1 instruction)

| Instruction | Semantics |
|---|---|
| `FENCE.I` | Synchronize instruction and data streams |

After `FENCE.I`, all subsequent instruction fetches see all prior stores from this hart. In a core with an icache, this means: drain the store buffer, then invalidate (or flush) the icache.

Our current pipeline has no icache (direct `imem` function), but we still need the **pipeline drain** semantics. Software that uses `FENCE.I` expects all prior instructions to have completed and all subsequent fetches to reflect prior memory writes.

---

## Why These Are Hard in an OoO Pipeline

The Tomasulo pipeline tracks dependencies through integer register renaming (RAT → PRF → CDB). CSRs break this model:

1. **CSRs are a second register file with implicit ordering.** Two CSR instructions targeting the same CSR have a RAW dependency through the CSR, not through the integer register file. The Tomasulo rename/RS/CDB machinery doesn't track CSR dependencies.

2. **CSR writes have global side effects.** Writing `mstatus` changes interrupt enables. Writing `frm` changes FP rounding mode for subsequent instructions. These side effects must be **precise** — they take effect at exactly the program-order commit point, not at speculative execution time.

3. **Some CSRs are live counters.** `cycle` and `instret` change every cycle. A speculative read from an RS that dispatched N cycles ago gives a stale value.

4. **FENCE.I requires icache coherence.** Even without an icache today, the instruction implies all prior stores are visible to subsequent fetches. In our pipeline, this means draining the store buffer and flushing the fetch/decode stages so they re-fetch from coherent memory.

These properties mean CSR and fence instructions cannot simply flow through the OoO pipeline like arithmetic. They require some form of serialization.

---

## Current State of the Codebase

What already exists (stubs and infrastructure we can build on):

| Component | File | Status |
|---|---|---|
| `OpType.CSRRW/S/C/WI/SI/CI` | `ISA.lean:157-163` | Defined, in decoder |
| `OpType.FENCE` | `ISA.lean:117` | Defined, treated as no-op in semantics |
| `classifyToUnit .CSRRW/...` → `.Integer` | `Dispatch.lean:76` | Routed to integer unit |
| `classifyToUnit .FENCE` → `.System` | `Dispatch.lean:78` | Routed to System (no-op) |
| Integer exec returns 0 for CSR ops | `IntegerExecUnit.lean:86` | Stub |
| `enableZicsr : Bool := false` | `Config.lean:24` | Config flag, unused |
| `globalStall` mechanism | `CPU.lean:501` | Working, used by flush logic |
| `fflags` / `frm` fields | `CPU.lean:488-491` | Exist as separate fields, not in a CSR file |
| ROB `exception` field | `ROB.lean:59` | Working, propagates through CDB |
| ROB `fullFlush` | `ROB.lean:267` | Working, clears all entries |
| `FetchState` with `branchRedirect` | `Fetch.lean:71-76` | Redirect support exists |

Key observation: `globalStall` already freezes fetch, and `fullFlush` already clears the pipeline. These are the two primitives we need for Option A.

---

## Option A: Full Serialize (Short-Term)

### Concept

When decode sees a CSR or FENCE.I instruction, stall fetch/decode and drain the pipeline. Once the ROB is empty, execute the operation in isolation, then resume.

```
cycle 1..N:   stall fetch, wait for ROB to empty
cycle N+1:    execute CSR read-modify-write (or FENCE.I flush)
cycle N+2:    write results, resume fetch
```

No new functional unit. No new RS. No CDB broadcast. The CSR operation happens in the commit stage when no other instructions are in flight.

### Pipeline Modifications

#### New State

```lean
-- In CPUState:
/-- CSR register file (M-mode minimal set) -/
csrFile : CSRFile
/-- CSR serialization FSM -/
csrState : CSRSerializeState

inductive CSRSerializeState where
  | idle                     -- normal operation
  | draining (op : OpType)   -- waiting for ROB to empty
      (csrAddr : UInt12)
      (rs1Val : UInt32)      -- rs1 value (or zimm, zero-extended)
      (rdTag : Fin 64)       -- physical dest register for old CSR value
      (hasRd : Bool)         -- rd != x0
  | fenceIDraining           -- FENCE.I: waiting for ROB + store buffer to empty
```

#### CSR Register File

Minimum M-mode set plus F extension support:

| CSR | Addr | Notes |
|---|---|---|
| `fflags` | 0x001 | FP exception flags (5 bits, rest WARL zero) |
| `frm` | 0x002 | FP rounding mode (3 bits, rest WARL zero) |
| `fcsr` | 0x003 | Combined `frm[7:5] ++ fflags[4:0]` (alias) |
| `mstatus` | 0x300 | MIE, MPIE, MPP fields; rest WARL |
| `misa` | 0x301 | Read-only (hardwired to RV32IMF) |
| `mie` | 0x304 | Interrupt enable bits |
| `mtvec` | 0x305 | Trap vector base + mode |
| `mscratch` | 0x340 | Scratch register for trap handlers |
| `mepc` | 0x341 | Exception PC (WARL, bit 0 always 0) |
| `mcause` | 0x342 | Trap cause |
| `mtval` | 0x343 | Trap value |
| `mip` | 0x344 | Interrupt pending (partially read-only) |
| `mcycle` | 0xB00 | Cycle counter low |
| `minstret` | 0xB02 | Retired instruction counter low |
| `mcycleh` | 0xB80 | Cycle counter high |
| `minstreth` | 0xB82 | Retired instruction counter high |

This is 16 CSRs x 32 bits. The structural circuit is a 16-entry register file: Decoder4 for write select, Mux16x32 for read, plus per-field write masks for WARL behavior.

The existing `fflags`/`frm` fields in `CPUState` get replaced by reads from the CSR file. The FP exec unit reads `frm` from the CSR file instead of the standalone field.

#### Counter CSR Semantics (mcycle, minstret)

These four CSRs are special: they're not just storage, they're live counters with auto-increment behavior. Getting them right requires careful attention to *when* the read and write take effect relative to the counter's own ticking.

**mcycle / mcycleh (cycle counter)**

`mcycle` increments every clock cycle, unconditionally. It counts wall-clock time, not retired instructions or pipeline events. The full counter is 64 bits wide, split across `mcycle` (low 32) and `mcycleh` (high 32).

Key design points:
- The counter increments **during the drain**. If the serialize FSM takes 12 cycles to drain, the value read by the CSR instruction is 12 higher than when it entered decode. This is correct — the spec says the read occurs at retirement, not at dispatch.
- A **write** sets the counter to the written value. On the next cycle, it increments to written_value + 1. The write and the auto-increment must not collide: on the write cycle, the explicit write wins and the auto-increment is suppressed.
- Reading `mcycleh` while `mcycle` is near overflow is a known RISC-V pitfall. Software is expected to use the standard read-high/read-low/read-high-again loop. We don't need to handle this in hardware — it's a software pattern.

In the structural circuit, `mcycle` is a 32-bit register with an adder (KoggeStone or ripple — it's not timing-critical) and a write-vs-increment mux:

```
mcycle_next = if csr_write_en && csr_addr == MCYCLE then
               csr_write_data          -- explicit write wins
             else
               mcycle + 1              -- auto-increment
```

`mcycleh` is the same but increments only when `mcycle` wraps (carry out from mcycle's adder).

**minstret / minstreth (retired instruction counter)**

`minstret` counts instructions that retire from the ROB. This interacts with serialization in a subtle way.

The spec (Volume II, 3.1.11) says the counter increments "for each instruction that retires." But what value does a `csrr x5, minstret` instruction itself see? There are two valid readings:

1. The count *before* this instruction retires (i.e., the instruction doesn't count itself)
2. The count *after* this instruction retires (i.e., it does count itself)

Spike uses interpretation (1): the read sees the count of all *previously* retired instructions, not including the `csrr` itself. Most hardware implementations agree. We follow Spike for cosim compatibility.

In Option A this falls out naturally from the ordering:

```
1. Pipeline drains (all prior instructions retire, incrementing minstret)
2. CSR read happens (sees count including all prior retirements)
3. CSR instruction itself retires (minstret increments again)
```

The read at step 2 does not include step 3's increment. The `csrr` sees N, and after it retires, `minstret` becomes N+1.

For **writes** to `minstret`: the written value takes effect immediately. The CSR instruction's own retirement then increments it by 1. So `csrw minstret, x0` (write zero) results in `minstret = 1` after the `csrw` retires — the counter resumes from the written value.

Wait — should the `csrw` itself increment the counter after writing? This depends on whether the increment happens *at* retirement or *after* the CSR write. The clean answer: the auto-increment for the retiring instruction happens **after** the CSR write within the same cycle, as a separate step. This means:

```
csrw minstret, 0     -- writes 0, then retires, minstret becomes 0 + 1 = 1
csrr x5, minstret    -- reads 1, then retires, minstret becomes 2
```

This matches Spike's behavior and avoids a special case where CSR writes to `minstret` suppress the retirement increment.

In the structural circuit, `minstret` has the same write-vs-increment structure as `mcycle`, but the increment is gated by `rob_commit_en` (an instruction actually retiring) rather than being unconditional:

```
minstret_next = if csr_write_en && csr_addr == MINSTRET then
                  csr_write_data + (if rob_commit_en then 1 else 0)
                else if rob_commit_en then
                  minstret + 1
                else
                  minstret
```

Note the `+ 1` in the write path when `rob_commit_en` is also asserted: this handles the case where the `csrw minstret` instruction itself is the one retiring. Since the CSR write and the retirement happen in the same cycle (the pipeline is drained, so the CSR instruction is the only thing retiring), both the write and the +1 apply.

**Separate from the CSR register file?**

Because `mcycle`/`minstret` have auto-increment logic, they don't fit cleanly into a plain register file. Two options:

1. **Keep them in the CSR file** but add increment inputs alongside the write port. The file becomes slightly irregular: 12 of 16 entries are plain registers, 4 have adders. This complicates the structural circuit but keeps the address decoding uniform.

2. **Pull them out** as standalone counter modules with their own read/write interface. The `CSRAddrDecoder` routes reads/writes for 0xB00/0xB02/0xB80/0xB82 to the counter modules instead of the register file. Cleaner hardware, slightly more complex wiring.

Option (2) is more natural in the DSL — a `Counter64` module (two Register32 + KoggeStoneAdder32 + carry chain) is a reusable building block. The CSR file stays as a pure 12-entry register file for the non-counter CSRs.

#### Decode Stage Changes

```lean
-- In cpuStep, after decode:
let csrOpDetected := match decodedOp with
  | some (.CSRRW | .CSRRS | .CSRRC | .CSRRWI | .CSRRSI | .CSRRCI) => true
  | _ => false

let fenceIDetected := match decodedOp with
  | some .FENCE_I => true
  | _ => false

-- Transition to draining state
let csrState' := match cpu.csrState with
  | .idle =>
    if csrOpDetected then
      .draining op csrAddr rs1Val rdTag hasRd
    else if fenceIDetected then
      .fenceIDraining
    else
      .idle
  | .draining .. => if cpu.rob.isEmpty then .idle else cpu.csrState
  | .fenceIDraining => if cpu.rob.isEmpty && cpu.lsu.storeBufferEmpty then .idle else cpu.csrState
```

#### Execution (When Drained)

```lean
def executeCSR (csrFile : CSRFile) (op : OpType) (rs1Val : UInt32) (addr : CSRAddr)
    : UInt32 × CSRFile :=
  let oldVal := csrFile.read addr
  let newVal := match op with
    | .CSRRW  | .CSRRWI => rs1Val
    | .CSRRS  | .CSRRSI => oldVal ||| rs1Val
    | .CSRRC  | .CSRRCI => oldVal &&& ~~~rs1Val
    | _ => oldVal  -- unreachable
  let csrFile' := if shouldWrite op rs1Val then
    csrFile.writeWARL addr newVal
  else
    csrFile
  (oldVal, csrFile')

-- shouldWrite: CSRRS/CSRRC with rs1=x0 (or zimm=0) skip the write
def shouldWrite (op : OpType) (rs1Val : UInt32) : Bool :=
  match op with
  | .CSRRW | .CSRRWI => true
  | .CSRRS | .CSRRC | .CSRRSI | .CSRRCI => rs1Val != 0
  | _ => false
```

When draining completes (`rob.isEmpty`):
1. Execute `executeCSR` to get `(oldVal, csrFile')`
2. Write `oldVal` directly to PRF at `rdTag` (bypass CDB — pipeline is empty, no one is listening)
3. Update `csrFile'` in CPU state
4. Clear `csrState` to `.idle`, resume fetch

#### FENCE.I (When Drained)

When `fenceIDraining` and ROB + store buffer are empty:
1. Invalidate fetch buffer (`fetchedInstr := none`)
2. Redirect fetch to `pc + 4` (re-fetch from current FENCE.I location + 4)
3. Clear `csrState` to `.idle`

No icache invalidation needed today (direct `imem` model). When an icache is added later, FENCE.I additionally sends an invalidate pulse to it.

### Structural Circuit Changes

New modules needed:

| Module | Type | Description |
|---|---|---|
| `CSRFile16x32` | Sequential | 16-entry x 32-bit register file with WARL masks |
| `CSRSerializeFSM` | Sequential | 3-state FSM (idle/draining/fenceI) |
| `CSRExecute` | Combinational | RMW logic (AND/OR/passthrough mux) |
| `CSRAddrDecoder` | Combinational | 12-bit CSR address → 4-bit file index |

The CSR address space is sparse (0x001-0x003, 0x300-0x344, 0xB00-0xB82), so `CSRAddrDecoder` maps the 12-bit `csr` field from the instruction to a dense 4-bit index for the register file. Illegal addresses produce an exception signal.

Integration in `cpuCircuit`: the FSM output `stall_for_csr` ORs into `global_stall`. The FSM output `csr_execute_en` (one cycle pulse when drain completes) gates the CSR file write enable and PRF write port.

### Performance Cost

With a 16-entry ROB:
- Worst-case drain: 16 cycles (all entries occupied) + execution latency of in-flight ops
- Typical drain: 8-12 cycles
- CSR execution: 1 cycle (combinational RMW)
- FENCE.I: drain + 1 cycle (fetch redirect)

CSR instructions are < 0.1% of dynamic instruction count in most workloads. The drain cost is dominated by how full the ROB is when the CSR instruction arrives. The impact on overall IPC is negligible.

For FP rounding mode changes (`csrw frm, ...`), serialization is actually desirable: it guarantees no in-flight FP instruction uses the wrong rounding mode.

### Proof Strategy

The key theorem is that the serialized CSR execution matches the ISA spec:

```lean
theorem serialize_csr_correct
    (cpu : CPUState config) (op : OpType) (csrAddr : CSRAddr) (rs1Val : UInt32)
    (h_drained : cpu.rob.isEmpty)
    (h_csr : op ∈ [.CSRRW, .CSRRS, .CSRRC, .CSRRWI, .CSRRSI, .CSRRCI]) :
    let (rdVal, csrFile') := executeCSR cpu.csrFile op rs1Val csrAddr
    -- Old value goes to rd
    rdVal = cpu.csrFile.read csrAddr ∧
    -- New value follows spec
    csrFile'.read csrAddr = applyCSROp op (cpu.csrFile.read csrAddr) rs1Val := by
  simp [executeCSR, applyCSROp]
```

Because the pipeline is empty when the CSR executes, there is no interaction with OoO state to reason about. The proof decomposes into:
1. **CSR RMW correctness** — `executeCSR` matches the spec (pure function, `simp` or `native_decide`)
2. **WARL masking** — `writeWARL` produces legal values (per-CSR mask lemmas)
3. **Drain invariant** — when `csrState = .draining` and `rob.isEmpty`, no speculative state exists
4. **FENCE.I correctness** — after drain + fetch redirect, next fetch sees coherent memory

The WARL proofs are per-CSR: `mstatus` WARL mask zeroes reserved bits, `mepc` clears bit 0, `misa` ignores all writes, etc. Each is a small `native_decide` or `bv_decide` proof on the 32-bit mask.

### Verification (LEC)

The CSR register file and FSM are small enough for direct SEC. The `CSRAddrDecoder` and `CSRExecute` are combinational and use SAT-based miter. Total: 4 new modules, all direct LEC — no compositional certs needed.

### Implementation Steps

1. Add `FENCE_I` to `OpType` and decoder (new instruction definition in `ISA.lean`)
2. Define `CSRFile` structure and `CSRSerializeState` in a new `lean/Shoumei/RISCV/CSR.lean`
3. Implement `executeCSR` with WARL write masks
4. Add `csrFile` and `csrState` to `CPUState`
5. Modify `cpuStep`: detect CSR/FENCE.I in decode, manage FSM transitions, execute when drained
6. Replace standalone `fflags`/`frm` fields with CSR file reads
7. Build structural circuits (`CSRFile16x32`, `CSRSerializeFSM`, `CSRExecute`, `CSRAddrDecoder`)
8. Add to `GenerateAll.lean`, run codegen + LEC
9. Write proofs (CSR RMW, WARL, drain invariant)
10. Add cosim test patterns (CSR read-after-write, FENCE.I self-modifying code)

**Estimated scope:** ~500-700 lines of Lean (behavioral + structural), 4 new modules, straightforward verification.

---

## Option C: Microcode Sequencer (Long-Term)

### Concept

A microcode sequencer replaces the decode stage when a complex instruction is encountered. Instead of emitting one macro-instruction, it emits a sequence of micro-operations from a ROM. The pipeline sees only primitive µops it already knows how to execute.

This option is not justified for Zicsr alone (6 instructions with identical structure). It becomes worthwhile when amortized across the full privileged ISA and future extensions:

| Extension | Instructions | µops per instruction |
|---|---|---|
| Zicsr | CSRRW/S/C, CSRRWI/SI/CI | 3-4 |
| Zifencei | FENCE.I | 2-3 |
| Machine-mode traps | trap entry sequence | 7-8 |
| MRET | return from trap | 5-6 |
| WFI | wait for interrupt | 2 |
| Zicbo (future) | cache management | 3-4 |
| A extension (future) | LR.W, SC.W, AMO* | 4-6 |

That's 20+ complex instructions sharing one sequencer. The per-instruction hardware cost drops to a ROM entry.

### Architecture

```
                    ┌─────────────────────────┐
                    │   Microcode Sequencer    │
  IMEM ──► Decode ──┤                         ├──► Rename ──► RS ──► Execute
                    │  ┌───────────────────┐  │
                    │  │   Microcode ROM    │  │
                    │  │  CSRRW: 3 µops    │  │
                    │  │  CSRRS: 4 µops    │  │
                    │  │  FENCE.I: 3 µops  │  │
                    │  │  TRAP_ENTRY: 8    │  │
                    │  │  MRET: 6 µops     │  │
                    │  │  ...              │  │
                    │  └───────────────────┘  │
                    │                         │
                    │  State: active, µPC,    │
                    │  capturedCSRAddr,       │
                    │  capturedRS1, tempRegs  │
                    └─────────────────────────┘
```

When decode encounters a microcoded instruction:
1. Capture instruction fields (CSR address, rs1, zimm, rd) into sequencer latches
2. Set `active := true`, load µPC with the entry point for this instruction class
3. Override the decode stage output: each cycle, emit the µop at `ROM[µPC]`
4. Advance µPC until the sequence ends, then set `active := false` and resume normal fetch

### Micro-operation Set

The sequencer emits µops from this instruction set. Each µop maps to an existing pipeline operation or a new primitive:

| µop | Meaning | Pipeline mapping |
|---|---|---|
| `DRAIN` | Wait for ROB to empty | Assert `globalStall`, wait for `rob.isEmpty` |
| `DRAIN_SB` | Wait for store buffer empty | Assert `globalStall`, wait for `lsu.sbEmpty` |
| `READ_CSR tmp, csr` | Read CSR → internal temp | New: CSR file read port → temp latch (counter CSRs read live value) |
| `WRITE_CSR csr, tmp` | Write internal temp → CSR | New: temp latch → CSR file write port (counter CSRs suppress auto-increment on write cycle) |
| `MOV_TO_RD tmp` | Internal temp → rd via PRF write | PRF write port (no CDB, pipeline is drained) |
| `ALU_OR tmp, tmp, rs1` | Bitwise OR on temp | Combinational, internal to sequencer |
| `ALU_ANDN tmp, tmp, rs1` | Bitwise AND-NOT on temp | Combinational, internal to sequencer |
| `ALU_MOV tmp, rs1` | Copy rs1 to temp | Combinational, internal to sequencer |
| `FLUSH_FETCH` | Invalidate fetch buffer, redirect PC | Existing: `branchRedirect` mechanism |
| `SET_PC tmp` | Load PC from temp register | Existing: `branchRedirect` mechanism |
| `DONE` | End sequence, resume normal decode | Clear `active` |

### Microcode ROM Contents

#### CSRRW rd, csr, rs1

```
entry_csrrw:
  DRAIN                          -- wait for pipeline to empty
  READ_CSR   t0, {csr}          -- t0 = CSR[csr]
  ALU_MOV    t1, {rs1}          -- t1 = rs1 value
  WRITE_CSR  {csr}, t1          -- CSR[csr] = t1
  MOV_TO_RD  t0                 -- rd = t0 (old CSR value)
  DONE
```

#### CSRRS rd, csr, rs1

```
entry_csrrs:
  DRAIN
  READ_CSR   t0, {csr}          -- t0 = CSR[csr]
  ALU_OR     t1, t0, {rs1}      -- t1 = t0 | rs1
  WRITE_CSR  {csr}, t1          -- CSR[csr] = t1 (skipped if rs1 == x0)
  MOV_TO_RD  t0                 -- rd = t0
  DONE
```

#### CSRRC rd, csr, rs1

```
entry_csrrc:
  DRAIN
  READ_CSR   t0, {csr}
  ALU_ANDN   t1, t0, {rs1}      -- t1 = t0 & ~rs1
  WRITE_CSR  {csr}, t1          -- (skipped if rs1 == x0)
  MOV_TO_RD  t0
  DONE
```

#### FENCE.I

```
entry_fencei:
  DRAIN                          -- wait for ROB empty
  DRAIN_SB                       -- wait for store buffer empty
  FLUSH_FETCH                    -- invalidate fetch, redirect to PC+4
  DONE
```

#### Trap Entry (future — motivates the architecture)

```
entry_trap:
  DRAIN
  READ_CSR   t0, mstatus        -- save current mstatus
  ALU_FIELD   t1, t0, MIE→MPIE  -- t1.MPIE = t0.MIE (shift field)
  ALU_CLEAR   t1, t1, MIE       -- t1.MIE = 0
  ALU_SET_FIELD t1, t1, MPP, {priv}  -- t1.MPP = current privilege
  WRITE_CSR  mstatus, t1
  WRITE_CSR  mepc, {trap_pc}
  WRITE_CSR  mcause, {cause}
  WRITE_CSR  mtval, {tval}
  READ_CSR   t2, mtvec
  SET_PC     t2                  -- redirect to trap vector
  DONE
```

This is 11 µops vs. a dedicated FSM with the same number of states, but the µop approach is **data** (ROM contents) rather than **logic** (state machine transitions). Adding a new trap cause or changing the entry sequence means editing ROM entries, not rewiring gates.

#### MRET (future)

```
entry_mret:
  DRAIN
  READ_CSR   t0, mstatus
  ALU_FIELD   t1, t0, MPIE→MIE  -- restore MIE from MPIE
  ALU_SET     t1, t1, MPIE      -- set MPIE = 1
  ALU_CLEAR_FIELD t1, t1, MPP   -- MPP = 0 (or lowest supported priv)
  WRITE_CSR  mstatus, t1
  READ_CSR   t2, mepc
  SET_PC     t2                  -- return to mepc
  DONE
```

### Sequencer State

```lean
structure MicrocodeState where
  /-- Sequencer is active (overriding normal decode) -/
  active : Bool
  /-- Current position in microcode ROM -/
  µPC : Fin romSize
  /-- Captured CSR address from macro-instruction -/
  csrAddr : UInt12
  /-- Captured rs1 value (read from PRF before entering sequence) -/
  rs1Val : UInt32
  /-- Captured zimm (for immediate CSR variants) -/
  zimm : UInt32
  /-- Physical destination register tag (for rd writeback) -/
  rdTag : Fin 64
  /-- Whether rd needs writeback (rd != x0) -/
  hasRd : Bool
  /-- Internal temporary registers -/
  temp : Fin 4 → UInt32
  /-- Waiting for drain condition -/
  waitingForDrain : Bool
```

### Structural Circuit

| Module | Type | Estimated Size |
|---|---|---|
| `MicrocodeROM` | Combinational | ~64 entries x 24-bit µop encoding |
| `MicrocodeSequencer` | Sequential | FSM + µPC register + temp latches |
| `MicrocodeDecoder` | Combinational | µop → control signals |
| `CSRFile16x32` | Sequential | Same as Option A |
| `CSRAddrDecoder` | Combinational | Same as Option A |
| `CSRExecute` | Combinational | Subset of Option A (just the ALU µops) |

The ROM is small — 64 entries at 24 bits each is 192 bytes. The µop encoding:

```
[23:20] opcode  (4 bits: DRAIN, READ_CSR, WRITE_CSR, ALU_OR, ALU_ANDN, MOV, etc.)
[19:16] dest    (4 bits: temp register index or control signal)
[15:12] src1    (4 bits: temp register, captured rs1, or CSR addr)
[11:0]  imm     (12 bits: CSR address or field mask, depending on opcode)
```

### Performance

Same as Option A for Zicsr and FENCE.I — every sequence starts with `DRAIN`, so the pipeline drain cost is identical. The sequencer adds 1 cycle of decode latency (ROM lookup) which is negligible.

The advantage appears with trap entry and MRET: instead of a dedicated multi-cycle FSM, the same drain → sequence → resume pattern handles everything uniformly. The sequencer is already built and proven correct; adding new sequences is a ROM content change.

### Proof Strategy

The proof decomposes into two layers:

**Layer 1: Sequencer correctness (pipeline-level)**

```lean
theorem sequencer_terminates
    (state : MicrocodeState) (rom : MicrocodeROM)
    (h_active : state.active)
    (h_valid : validSequence rom state.µPC) :
    ∃ n, (stepSequencer^[n] state).active = false := by ...

theorem sequencer_drain_invariant
    (cpu : CPUState config) (state : MicrocodeState)
    (h_drain_complete : cpu.rob.isEmpty) :
    noSpeculativeState cpu := by ...
```

The sequencer always terminates (ROM sequences are finite, no loops). When a DRAIN µop completes, the pipeline has no speculative state. These are structural properties of the sequencer FSM.

**Layer 2: Sequence correctness (ISA-level)**

Each ROM sequence is proven equivalent to its ISA specification:

```lean
theorem csrrw_sequence_correct
    (csrFile : CSRFile) (rs1Val : UInt32) (addr : CSRAddr) :
    executeSequence rom entry_csrrw csrFile rs1Val addr =
    (csrFile.read addr, csrFile.writeWARL addr rs1Val) := by ...

theorem trap_entry_sequence_correct
    (csrFile : CSRFile) (pc : UInt32) (cause : UInt32) (tval : UInt32) :
    executeSequence rom entry_trap csrFile pc cause tval =
    specTrapEntry csrFile pc cause tval := by ...
```

These proofs are independent of the pipeline — they reason about the ROM content as a pure function from initial state to final state. The pipeline proof (Layer 1) guarantees the sequencer faithfully executes the sequence; the sequence proof (Layer 2) guarantees the sequence matches the ISA spec. Composing them gives end-to-end correctness.

This two-layer decomposition is the key advantage for formal verification: the pipeline proof is done once and reused for every new sequence. Adding MRET requires only a Layer 2 proof for the MRET ROM entries.

### Why Not Now

The microcode sequencer adds complexity that isn't justified by 7 instructions:

- **ROM + sequencer FSM + temp registers + µop decoder** — 4 new modules vs. Option A's simple 3-state FSM
- **Every Zicsr sequence starts with DRAIN** — same performance as Option A, but more hardware
- **The temp registers and µop ALU** add state that must be saved/restored on flush (or proven unreachable during flush)
- **The verification story is cleaner for Option A** — one theorem per CSR instruction vs. the two-layer decomposition

The crossover point is around 15-20 microcoded instructions. At that point, the one-time cost of the sequencer is amortized across enough sequences that the per-instruction cost drops below a dedicated FSM. The privileged ISA (trap entry, MRET, SRET, WFI, SFENCE.VMA) plus atomics (LR.W, SC.W, AMO*) puts us well past that threshold.

---

## Recommendation

### Short-term: Option A

Implement the full serialize approach for Zicsr + FENCE.I. It's minimal, correct by construction, and slots cleanly into the existing `globalStall` + `fullFlush` infrastructure.

Estimated effort: 4 new modules, ~600 lines of Lean, straightforward SEC verification.

### Long-term: Option C (when adding privileged mode)

When the privileged ISA is on the roadmap (traps, MRET, interrupt delegation), refactor the Option A CSR serialize FSM into a microcode sequencer. The CSR register file, WARL masks, and address decoder from Option A carry over unchanged. The sequencer replaces the 3-state FSM with a ROM-driven engine that handles both Zicsr and the privilege transitions.

The migration path is clean: Option A's `CSRSerializeState` FSM becomes the sequencer's `MicrocodeState`. The `executeCSR` function becomes ROM entries. The CSR file and proofs don't change. No throwaway work.

### FENCE.I Note

In both options, FENCE.I is straightforward today (pipeline drain + fetch redirect) because we have no icache. When an icache is added, FENCE.I additionally needs an invalidate signal to the icache. In Option A, this is a one-line addition to the `fenceIDraining` completion logic. In Option C, it's a new µop (`INVALIDATE_ICACHE`) inserted into the FENCE.I sequence. Either way, the drain semantics are the same.

---

## Test Patterns

New hazard patterns for [hazard-patterns.md](hazard-patterns.md):

| ID | Pattern | Exercises |
|----|---------|-----------|
| Z1 | CSR read-after-write | Write CSR then read same CSR, verify new value in rd |
| Z2 | CSR read-modify-write chain | CSRRS then CSRRC on same CSR, verify cumulative effect |
| Z3 | CSR write with rs1=x0 | CSRRS x5, mstatus, x0 — verify no write, rd gets old value |
| Z4 | CSR write-only (rd=x0) | CSRRW x0, mscratch, x1 — verify write, no read side-effect |
| Z5 | FENCE.I self-modifying code | Store new instruction, FENCE.I, execute it |
| Z6 | fcsr/frm/fflags aliasing | Write fcsr, read frm and fflags separately, verify consistency |
| Z7 | CSR after long-latency op | DIV in flight when CSR arrives, verify correct drain timing |
| Z8 | minstret self-count | `csrr x5, minstret` — verify it does NOT count itself (matches Spike) |
| Z9 | minstret write-then-resume | `csrw minstret, x0` then 3 NOPs then `csrr x5, minstret` — expect 4 (write 0, +1 for csrw retire, +3 NOPs, +1 for csrr itself... but csrr doesn't count itself, so 4) |
| Z10 | mcycle monotonicity | Two `csrr` reads of mcycle with NOPs between — verify delta > 0 and plausible |
| Z11 | mcycleh carry | Write 0xFFFFFFFF to mcycle, NOP, read mcycleh — verify it incremented |
| Z12 | minstret write + retire interaction | `csrw minstret, 0` retires → counter = 1, verify with immediate read |
| Z13 | Illegal CSR address | Access non-existent CSR, verify exception |

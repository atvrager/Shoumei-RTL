/-
RISCV/Retirement/ROB.lean - Reorder Buffer for RV32I Tomasulo CPU

The ROB tracks in-flight instructions and enforces in-order commit.
It is a 16-entry circular buffer with three key interfaces:

1. **Allocate** (from Rename Stage): New instruction enters at tail
2. **CDB Snoop** (from Execution Units): Mark instruction complete when CDB tag matches
3. **Commit** (to Architectural State): Retire head entry in program order

Architecture: Tomasulo-style
- CDB writes directly to Physical Register File (not stored in ROB)
- ROB only tracks completion status, not result data
- At commit: update committed RAT, deallocate old physical register

Entry lifecycle:
1. ALLOCATE: Rename stage dispatches instruction -> ROB allocates at tail
2. EXECUTE: Reservation Station dispatches to execution unit
3. COMPLETE: CDB broadcasts (tag, data) -> ROB snoops, sets complete flag
4. COMMIT: Head entry complete -> update architectural state, free old phys reg

Branch recovery:
- CommittedRAT tracks architectural mapping (updated only at commit)
- On misprediction at commit: flush younger entries, restore speculative RAT
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.Register
import Shoumei.Circuits.Sequential.QueueComponents
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Circuits.Combinational.Comparator
import Shoumei.RISCV.Config

namespace Shoumei.RISCV.Retirement

open Shoumei
open Shoumei.Circuits.Sequential
open Shoumei.Circuits.Combinational

/-! ## ROB Entry -/

/-- Empty/default ROB entry. -/
structure ROBEntry where
  /-- Entry occupied (instruction allocated) -/
  valid : Bool
  /-- Execution finished (CDB broadcast received) -/
  complete : Bool
  /-- Destination physical register tag -/
  physRd : Fin 64
  /-- Whether physRd is meaningful (false for stores, branches w/o rd) -/
  hasPhysRd : Bool
  /-- Previous physical register mapped to archRd (for dealloc at commit) -/
  oldPhysRd : Fin 64
  /-- Whether oldPhysRd is meaningful -/
  hasOldPhysRd : Bool
  /-- Architectural destination register -/
  archRd : Fin 32
  /-- Exception occurred during execution -/
  exception : Bool
  /-- Does this instruction write to an FP register? -/
  isFpDest : Bool
  /-- Is this a branch/jump instruction? -/
  isBranch : Bool
  /-- Branch was mispredicted (set via CDB) -/
  branchMispredicted : Bool
  deriving Repr, BEq, DecidableEq

instance : Inhabited ROBEntry where
  default := {
    valid := false, complete := false,
    physRd := 0, hasPhysRd := false,
    oldPhysRd := 0, hasOldPhysRd := false,
    archRd := 0, exception := false,
    isFpDest := false, isBranch := false, branchMispredicted := false
  }

/-- Create an empty ROB entry. -/
def ROBEntry.empty : ROBEntry := default

/-! ## ROB State -/

/-- Reorder Buffer State: 16-entry circular buffer.

    Hybrid of QueueN (FIFO allocation/commit via head/tail pointers)
    and PhysRegFile (random-access CDB updates via content-addressable tag matching).
-/
structure ROBState where
  /-- 16-entry storage -/
  entries : Fin 16 -> ROBEntry
  /-- Head pointer: next entry to commit (oldest instruction) -/
  head : Fin 16
  /-- Tail pointer: next entry to allocate (newest slot) -/
  tail : Fin 16
  /-- Current entry count -/
  count : Nat
  /-- Invariant: count never exceeds capacity -/
  h_count : count <= 16

/-- Create an empty ROB. -/
def ROBState.empty : ROBState :=
  { entries := fun _ => ROBEntry.empty
    head := 0
    tail := 0
    count := 0
    h_count := by omega
  }

/-! ## Helper Functions -/

/-- Check if ROB is empty. -/
def ROBState.isEmpty (rob : ROBState) : Bool :=
  rob.count == 0

/-- Check if ROB is full. -/
def ROBState.isFull (rob : ROBState) : Bool :=
  rob.count >= 16

/-- Get current count. -/
def ROBState.getCount (rob : ROBState) : Nat :=
  rob.count

/-- Advance a 4-bit pointer (wraps at 16). -/
private def advancePointer (ptr : Fin 16) : Fin 16 :=
  ⟨(ptr.val + 1) % 16, by omega⟩

/-- Check if entry index `idx` is strictly younger than `ref` in circular buffer.
    Younger means allocated after `ref` (between ref+1 and tail-1). -/
private def isYoungerThan (idx : Fin 16) (ref : Fin 16) (_head : Fin 16) (tail : Fin 16) : Bool :=
  -- An entry is "in the buffer" if it's between head and tail (circularly)
  -- An entry is "younger than ref" if it's between ref+1 and tail-1 (circularly)
  let refNext := (ref.val + 1) % 16
  if tail.val >= refNext then
    -- No wraparound: younger entries are in [refNext, tail)
    idx.val >= refNext && idx.val < tail.val
  else
    -- Wraparound: younger entries are in [refNext, 16) ∪ [0, tail)
    idx.val >= refNext || idx.val < tail.val

/-! ## Core Operations -/

/-- Allocate a new ROB entry at the tail.

    Called when the Rename Stage dispatches a new instruction.
    Returns (updated state, allocated ROB index) or (unchanged state, none) if full.
-/
def ROBState.allocate
    (rob : ROBState)
    (physRd : Fin 64) (hasPhysRd : Bool)
    (oldPhysRd : Fin 64) (hasOldPhysRd : Bool)
    (archRd : Fin 32) (isFpDest : Bool := false) (isBranch : Bool)
    : ROBState × Option (Fin 16) :=
  if h : rob.count >= 16 then
    (rob, none)
  else
    let newEntry : ROBEntry := {
      valid := true
      complete := !(hasPhysRd || isBranch)  -- only stores auto-complete; branches need CDB
      physRd := physRd
      hasPhysRd := hasPhysRd
      oldPhysRd := oldPhysRd
      hasOldPhysRd := hasOldPhysRd
      archRd := archRd
      exception := false
      isFpDest := isFpDest
      isBranch := isBranch
      branchMispredicted := false
    }
    let allocIdx := rob.tail
    let newEntries := fun i =>
      if i == rob.tail then newEntry else rob.entries i
    ({ entries := newEntries
       head := rob.head
       tail := advancePointer rob.tail
       count := rob.count + 1
       h_count := by omega },
     some allocIdx)

/-- CDB broadcast: mark entries complete when their physRd matches the CDB tag.

    All 16 entries snoop the CDB in parallel (content-addressable matching).
    Only entries that are valid, not yet complete, and have hasPhysRd=true participate.
-/
def ROBState.cdbBroadcast
    (rob : ROBState)
    (cdb_tag : Fin 64)
    (cdb_exception : Bool := false)
    (cdb_mispredicted : Bool := false)
    : ROBState :=
  let newEntries := fun i =>
    let e := rob.entries i
    if e.valid && !e.complete && (e.hasPhysRd || e.isBranch) && e.physRd == cdb_tag then
      { e with
        complete := true
        exception := cdb_exception
        branchMispredicted := cdb_mispredicted }
    else e
  { rob with entries := newEntries }

/-- Commit the instruction at the head of the ROB.

    Preconditions: head entry is valid and complete.
    Returns: (updated ROB, committed entry data) or (unchanged, none).

    The caller uses the returned entry to:
    1. Update committed RAT (archRd -> physRd)
    2. Deallocate oldPhysRd to FreeList
    3. Detect misprediction (if isBranch && branchMispredicted)
-/
def ROBState.commit (rob : ROBState) : ROBState × Option ROBEntry :=
  if rob.isEmpty then (rob, none)
  else
    let headEntry := rob.entries rob.head
    if !headEntry.valid || !headEntry.complete then (rob, none)
    else
      let newEntries := fun i =>
        if i == rob.head then ROBEntry.empty else rob.entries i
      ({ entries := newEntries
         head := advancePointer rob.head
         tail := rob.tail
         count := rob.count - 1
         h_count := by have := rob.h_count; omega },
       some headEntry)

/-- Flush all entries younger than the given ROB index (for misprediction recovery).

    Clears valid for entries between (flushIdx+1) and (tail-1) circularly.
    Returns (updated state, list of physRd tags to return to FreeList).
-/
def ROBState.flush (rob : ROBState) (flushIdx : Fin 16) : ROBState × List (Fin 64) :=
  -- Collect physRd tags from entries being flushed
  let freedTags := (List.range 16).filterMap fun i =>
    if h : i < 16 then
      let idx : Fin 16 := ⟨i, h⟩
      let e := rob.entries idx
      if e.valid && isYoungerThan idx flushIdx rob.head rob.tail && e.hasPhysRd then
        some e.physRd
      else
        none
    else none

  -- Clear younger entries
  let newEntries := fun i =>
    let e := rob.entries i
    if isYoungerThan i flushIdx rob.head rob.tail then
      ROBEntry.empty
    else e

  -- Reset tail to just after flushIdx
  let newTail := advancePointer flushIdx

  -- Count surviving entries (head through flushIdx inclusive)
  let survivingCount := (List.range 16).filter (fun i =>
    if h : i < 16 then
      let idx : Fin 16 := ⟨i, h⟩
      (rob.entries idx).valid && !isYoungerThan idx flushIdx rob.head rob.tail
    else false
  ) |>.length

  ({ entries := newEntries
     head := rob.head
     tail := newTail
     count := min survivingCount 16
     h_count := Nat.min_le_right survivingCount 16 },
   freedTags)

/-- Full flush: clear ALL entries. Used for exceptions or full pipeline flush. -/
def ROBState.fullFlush (rob : ROBState) : ROBState × List (Fin 64) :=
  let freedTags := (List.range 16).filterMap fun i =>
    if h : i < 16 then
      let e := rob.entries ⟨i, h⟩
      if e.valid && e.hasPhysRd then some e.physRd else none
    else none
  (ROBState.empty, freedTags)

/-! ## Committed RAT (for branch recovery) -/

/-- Committed RAT: tracks architectural register mapping, updated only at commit.

    On misprediction: copy committed RAT -> speculative RAT to restore correct state.
    Structurally, this is just another RAT_32x6 instance wired to the commit path.
-/
structure CommittedRATState where
  /-- Architectural register -> physical register mapping -/
  mapping : Fin 32 -> Fin 64

/-- Initialize committed RAT with identity mapping (arch reg i -> phys reg i). -/
def CommittedRATState.init : CommittedRATState :=
  { mapping := fun i => ⟨i.val, by omega⟩ }

/-- Update committed RAT on instruction commit. -/
def CommittedRATState.update
    (crat : CommittedRATState)
    (archRd : Fin 32) (physRd : Fin 64) (hasPhysRd : Bool)
    : CommittedRATState :=
  if hasPhysRd && archRd.val != 0 then  -- Never update x0 mapping
    { mapping := fun i => if i == archRd then physRd else crat.mapping i }
  else
    crat

/-- Lookup in committed RAT. -/
def CommittedRATState.lookup (crat : CommittedRATState) (archReg : Fin 32) : Fin 64 :=
  crat.mapping archReg

/-! ## Combined Commit Logic -/

/-- Result of a commit operation. -/
structure CommitResult where
  /-- Updated ROB state -/
  rob : ROBState
  /-- Updated committed RAT -/
  committedRAT : CommittedRATState
  /-- Old physical register to deallocate (for FreeList) -/
  deallocTag : Option (Fin 64)
  /-- Misprediction detected? -/
  misprediction : Bool
  /-- Exception detected? -/
  exceptionDetected : Bool

/-- Perform a full commit step: ROB commit + committed RAT update + deallocation.

    This is the main commit interface used by the pipeline controller.
-/
def commitStep (rob : ROBState) (crat : CommittedRATState) : CommitResult :=
  let (rob', entry) := rob.commit
  match entry with
  | none =>
    { rob := rob', committedRAT := crat,
      deallocTag := none, misprediction := false, exceptionDetected := false }
  | some e =>
    let crat' := crat.update e.archRd e.physRd e.hasPhysRd
    let dealloc := if e.hasOldPhysRd then some e.oldPhysRd else none
    { rob := rob', committedRAT := crat',
      deallocTag := dealloc,
      misprediction := e.isBranch && e.branchMispredicted,
      exceptionDetected := e.exception }

/-! ## Query Helpers -/

/-- Read the head entry (for commit decision logic). -/
def ROBState.headEntry (rob : ROBState) : ROBEntry :=
  rob.entries rob.head

/-- Check if head is ready to commit. -/
def ROBState.headReady (rob : ROBState) : Bool :=
  !rob.isEmpty && (rob.entries rob.head).valid && (rob.entries rob.head).complete

/-- Count valid entries. -/
def ROBState.countValid (rob : ROBState) : Nat :=
  (List.range 16).filter (fun i =>
    if h : i < 16 then (rob.entries ⟨i, h⟩).valid else false
  ) |>.length

/-! ## N-Wide Allocate / Commit (superscalar behavioral model) -/

/-- Arguments bundle for a single ROB allocation (one dispatched instruction). -/
structure ROBAllocArgs where
  physRd      : Fin 64
  hasPhysRd   : Bool
  oldPhysRd   : Fin 64
  hasOldPhysRd : Bool
  archRd      : Fin 32
  isFpDest    : Bool
  isBranch    : Bool

/-- Allocate up to N entries in program order.
    Stops early if ROB fills mid-group; slots after the first failure return `none`.
    Returns (updated ROB, list of optional allocated indices, count actually allocated). -/
def ROBState.allocateN
    (rob : ROBState)
    (args : List ROBAllocArgs)
    : ROBState × List (Option (Fin 16)) :=
  args.foldl (fun (state, idxs) a =>
    let (state', idx) := state.allocate
      a.physRd a.hasPhysRd a.oldPhysRd a.hasOldPhysRd a.archRd a.isFpDest a.isBranch
    -- If allocation failed (ROB full), propagate failure for remaining slots
    match idx with
    | none   => (state, idxs ++ [none])   -- state unchanged, slot gets none
    | some i => (state', idxs ++ [some i])
  ) (rob, [])

/-- Commit up to `maxCommit` instructions from the head in program order.
    Stops at the first entry that is not valid and complete (in-order constraint).
    Returns (updated ROB, list of committed entries). -/
def ROBState.commitN
    (rob : ROBState)
    (maxCommit : Nat)
    : ROBState × List ROBEntry :=
  (List.range maxCommit).foldl (fun (acc : ROBState × List ROBEntry) _ =>
    let (state, committed) := acc
    let (state', entry) := state.commit
    match entry with
    | none   => (state', committed)
    | some e => (state', committed ++ [e])
  ) (rob, [])

/-- Result of an N-wide commit step. -/
structure CommitResultN where
  /-- Updated ROB state -/
  rob : ROBState
  /-- Updated committed RAT -/
  committedRAT : CommittedRATState
  /-- Old physical registers to deallocate (one per committed instruction, in order) -/
  deallocTags : List (Option (Fin 64))
  /-- True if ANY committed instruction caused a misprediction (stops at first) -/
  misprediction : Bool
  /-- True if ANY committed instruction raised an exception -/
  exceptionDetected : Bool
  /-- Number of instructions actually committed this cycle -/
  commitCount : Nat

/-- N-wide commit step: commit up to `maxCommit` instructions, updating RAT + dealloc list.
    Stops at first misprediction — later slots are never committed (in-order semantics). -/
def commitStepN
    (rob : ROBState)
    (crat : CommittedRATState)
    (maxCommit : Nat)
    : CommitResultN :=
  let go (acc : ROBState × CommittedRATState × List (Option (Fin 64)) × Bool × Bool × Nat)
      : ROBState × CommittedRATState × List (Option (Fin 64)) × Bool × Bool × Nat :=
    let (rob, crat, deallocs, misp, exc, cnt) := acc
    if misp || exc then (rob, crat, deallocs, misp, exc, cnt)
    else
      let (rob', entry) := rob.commit
      match entry with
      | none => (rob', crat, deallocs, false, false, cnt)
      | some e =>
          let crat'   := crat.update e.archRd e.physRd e.hasPhysRd
          let dealloc := if e.hasOldPhysRd then some e.oldPhysRd else none
          (rob', crat', deallocs ++ [dealloc],
           e.isBranch && e.branchMispredicted, e.exception, cnt + 1)
  let init : ROBState × CommittedRATState × List (Option (Fin 64)) × Bool × Bool × Nat :=
    (rob, crat, [], false, false, 0)
  let (rob', crat', deallocs, misp, exc, cnt) :=
    (List.range maxCommit).foldl (fun acc _ => go acc) init
  { rob := rob', committedRAT := crat', deallocTags := deallocs,
    misprediction := misp, exceptionDetected := exc, commitCount := cnt }

/-! ## Structural Circuit -/

/-- Build ROB16 structural circuit: 16-entry Reorder Buffer.

    **Architecture:**
    - 16 entries × 24 bits each (Register24)
    - Head/tail pointers (QueuePointer_4) with up/down count (QueueCounterUpDown_5)
    - CDB tag matching via 16 parallel Comparator6 instances
    - Head readout via MuxTree (Mux16x6 for physRd/oldPhysRd, Mux16x5 for archRd)
    - Allocation decoder (Decoder4) + commit decoder (Decoder4) for one-hot entry select
    - Full flush support (flush_en resets pointers and clears all entries)

    **Entry layout (24 bits):**
    | Bit(s)  | Width | Field             |
    |---------|-------|-------------------|
    | 0       | 1     | valid             |
    | 1       | 1     | complete          |
    | 2-7     | 6     | physRd            |
    | 8       | 1     | hasPhysRd         |
    | 9-14    | 6     | oldPhysRd         |
    | 15      | 1     | hasOldPhysRd      |
    | 16-20   | 5     | archRd            |
    | 21      | 1     | exception         |
    | 22      | 1     | isBranch          |
    | 23      | 1     | branchMispredicted|

    **Instances (40):**
    - 16× Register24 (entry storage)
    - 16× Comparator6 (CDB tag matching)
    - 2× QueuePointer_4 (head, tail)
    - 1× QueueCounterUpDown_5 (count)
    - 2× Decoder4 (alloc decode, commit decode)
    - 2× Mux16x6 (physRd, oldPhysRd readout)
    - 1× Mux16x5 (archRd readout)
-/
def mkROB16 (width : Nat := 2) : Circuit :=
  -- Local alias to resolve namespace ambiguity (both Combinational and Sequential are open)
  let mkWires := @Shoumei.Circuits.Combinational.makeIndexedWires
  if width == 1 then
  -- === Global Signals ===
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- === Allocation Interface ===
  let alloc_en := Wire.mk "alloc_en"
  let alloc_physRd := mkWires "alloc_physRd" 6
  let alloc_hasPhysRd := Wire.mk "alloc_hasPhysRd"
  let alloc_oldPhysRd := mkWires "alloc_oldPhysRd" 6
  let alloc_hasOldPhysRd := Wire.mk "alloc_hasOldPhysRd"
  let alloc_archRd := mkWires "alloc_archRd" 5
  let alloc_isBranch := Wire.mk "alloc_isBranch"

  -- === CDB Interface ===
  let cdb_valid := Wire.mk "cdb_valid"
  let cdb_tag := mkWires "cdb_tag" 6
  let cdb_exception := Wire.mk "cdb_exception"
  let cdb_mispredicted := Wire.mk "cdb_mispredicted"
  let cdb_is_fp := Wire.mk "cdb_is_fp"

  -- === Per-entry FP domain shadow (from CPU.lean shadow registers) ===
  let is_fp_shadow := (List.range 16).map (fun i => Wire.mk s!"is_fp_shadow_{i}")

  -- === Commit/Flush Interface ===
  let commit_en := Wire.mk "commit_en"
  let flush_en := Wire.mk "flush_en"

  -- === Status Outputs ===
  let full := Wire.mk "full"
  let empty := Wire.mk "empty"

  -- === Allocation Result ===
  let alloc_idx := mkWires "alloc_idx" 4

  -- === Head Index Output (for RVVI queue readout) ===
  let head_idx := mkWires "head_idx" 4

  -- === Head Entry Readout ===
  let head_valid := Wire.mk "head_valid"
  let head_complete := Wire.mk "head_complete"
  let head_physRd := mkWires "head_physRd" 6
  let head_hasPhysRd := Wire.mk "head_hasPhysRd"
  let head_oldPhysRd := mkWires "head_oldPhysRd" 6
  let head_hasOldPhysRd := Wire.mk "head_hasOldPhysRd"
  let head_archRd := mkWires "head_archRd" 5
  let head_exception := Wire.mk "head_exception"
  let head_isBranch := Wire.mk "head_isBranch"
  let head_mispredicted := Wire.mk "head_mispredicted"

  -- === Internal Wires ===
  let head_ptr := mkWires "head_ptr" 4
  let tail_ptr := mkWires "tail_ptr" 4
  let count := mkWires "count" 5
  let alloc_decode := mkWires "alloc_decode" 16
  let commit_decode := mkWires "commit_decode" 16

  -- === Global Control Gates ===
  let global_gates : List Gate := []

  -- Full = count[4] (count ≥ 16 iff bit 4 set; count ≤ 16 by construction)
  let full_gate := Gate.mkBUF count[4]! full

  -- Empty = NOR(count[4:0])
  let empty_or1 := Wire.mk "empty_or1"
  let empty_or2 := Wire.mk "empty_or2"
  let empty_or3 := Wire.mk "empty_or3"
  let empty_or4 := Wire.mk "empty_or4"
  let empty_gates := [
    Gate.mkOR count[0]! count[1]! empty_or1,
    Gate.mkOR empty_or1 count[2]! empty_or2,
    Gate.mkOR empty_or2 count[3]! empty_or3,
    Gate.mkOR empty_or3 count[4]! empty_or4,
    Gate.mkNOT empty_or4 empty
  ]

  -- Safe commit: gate commit_en with NOT(empty) to prevent underflow.
  -- Uses empty_or4 (= any count bit set = not empty) directly instead of reading
  -- from the empty output port.
  let commit_en_safe := Wire.mk "commit_en_safe"
  let commit_safe_gates := [
    Gate.mkAND commit_en empty_or4 commit_en_safe
  ]

  -- Alloc index output: BUF tail_ptr to alloc_idx
  let alloc_idx_gates := List.zipWith (fun src dst =>
    Gate.mkBUF src dst
  ) tail_ptr alloc_idx

  -- Head index output: BUF head_ptr to head_idx (for RVVI queue readout)
  let head_idx_gates := List.zipWith (fun src dst =>
    Gate.mkBUF src dst
  ) head_ptr head_idx

  -- === Infrastructure Instances ===

  let head_inst : CircuitInstance := {
    moduleName := "QueuePointer_4"
    instName := "u_head"
    portMap :=
      [("clock", clock), ("reset", reset), ("en", commit_en_safe),
       ("one", one), ("zero", zero)] ++
      (head_ptr.enum.map (fun ⟨i, w⟩ => (s!"count_{i}", w)))
  }

  let tail_inst : CircuitInstance := {
    moduleName := "QueuePointer_4"
    instName := "u_tail"
    portMap :=
      [("clock", clock), ("reset", reset), ("en", alloc_en),
       ("one", one), ("zero", zero)] ++
      (tail_ptr.enum.map (fun ⟨i, w⟩ => (s!"count_{i}", w)))
  }

  let count_inst : CircuitInstance := {
    moduleName := "QueueCounterUpDown_5"
    instName := "u_count"
    portMap :=
      [("clock", clock), ("reset", reset), ("inc", alloc_en),
       ("dec", commit_en_safe), ("one", one), ("zero", zero)] ++
      (count.enum.map (fun ⟨i, w⟩ => (s!"count_{i}", w)))
  }

  let alloc_dec_inst : CircuitInstance := {
    moduleName := "Decoder4"
    instName := "u_alloc_dec"
    portMap :=
      (tail_ptr.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (alloc_decode.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  let commit_dec_inst : CircuitInstance := {
    moduleName := "Decoder4"
    instName := "u_commit_dec"
    portMap :=
      (head_ptr.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (commit_decode.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- === Reset Buffer Tree (2-level: 4 roots × 4 leaves = 16 leaf buffers) ===
  let numRoots := 4
  let numResetLeaves := 16
  let reset_roots := (List.range numRoots).map (fun i =>
    Wire.mk s!"reset_root_{i}")
  let reset_root_gates := (List.range numRoots).map (fun i =>
    Gate.mkBUF reset (reset_roots[i]!))
  let reset_leaves := (List.range numResetLeaves).map (fun i =>
    Wire.mk s!"reset_buf_{i}")
  let reset_buf_gates := reset_root_gates ++ (List.range numResetLeaves).map (fun i =>
    Gate.mkBUF (reset_roots[i / 4]!) (reset_leaves[i]!))

  -- === Per-Entry Logic (16 entries) ===

  let entryResults := (List.range 16).map fun i =>
    let e_cur := mkWires s!"e{i}" 24
    let e_next := mkWires s!"e{i}_next" 24

    -- Current state field accessors
    let cur_valid := e_cur[0]!
    let cur_complete := e_cur[1]!
    let cur_physRd := (List.range 6).map (fun j => e_cur[2+j]!)
    let cur_hasPhysRd := e_cur[8]!
    let cur_oldPhysRd := (List.range 6).map (fun j => e_cur[9+j]!)
    let cur_hasOldPhysRd := e_cur[15]!
    let cur_archRd := (List.range 5).map (fun j => e_cur[16+j]!)
    let cur_exception := e_cur[21]!
    let cur_isBranch := e_cur[22]!
    let cur_mispred := e_cur[23]!

    -- Control: allocation write enable = AND(alloc_en, alloc_decode[i])
    let alloc_we := Wire.mk s!"e{i}_alloc_we"
    let alloc_we_gate := Gate.mkAND alloc_en alloc_decode[i]! alloc_we

    -- Control: CDB tag match (from Comparator6 eq output)
    let cdb_match := Wire.mk s!"e{i}_cdb_match"

    -- Control: CDB write enable = valid AND NOT(complete) AND (hasPhysRd OR isBranch) AND match AND cdb_valid AND domain_match
    -- domain_match = NOT(cdb_is_fp XOR is_fp_shadow[i])
    -- Branches need CDB completion for misprediction tracking even without physRd (rd=x0)
    let complete_n := Wire.mk s!"e{i}_complete_n"
    let cdb_tmp1 := Wire.mk s!"e{i}_cdb_tmp1"
    let hasPhysOrBranch := Wire.mk s!"e{i}_hasPhysOrBranch"
    let cdb_tmp2 := Wire.mk s!"e{i}_cdb_tmp2"
    let cdb_tmp3 := Wire.mk s!"e{i}_cdb_tmp3"
    let cdb_tmp4 := Wire.mk s!"e{i}_cdb_tmp4"
    let domain_xor := Wire.mk s!"e{i}_domain_xor"
    let domain_match := Wire.mk s!"e{i}_domain_match"
    let cdb_we := Wire.mk s!"e{i}_cdb_we"
    let cdb_we_gates := [
      Gate.mkNOT cur_complete complete_n,
      Gate.mkAND cur_valid complete_n cdb_tmp1,
      Gate.mkOR cur_hasPhysRd cur_isBranch hasPhysOrBranch,
      Gate.mkAND cdb_tmp1 hasPhysOrBranch cdb_tmp2,
      Gate.mkAND cdb_tmp2 cdb_match cdb_tmp3,
      Gate.mkAND cdb_tmp3 cdb_valid cdb_tmp4,
      Gate.mkXOR cdb_is_fp is_fp_shadow[i]! domain_xor,
      Gate.mkNOT domain_xor domain_match,
      Gate.mkAND cdb_tmp4 domain_match cdb_we
    ]

    -- Control: commit clear = AND(commit_en, commit_decode[i])
    let commit_clear := Wire.mk s!"e{i}_commit_clear"
    let commit_clear_gate := Gate.mkAND commit_en_safe commit_decode[i]! commit_clear

    -- Control: clear = OR(flush_en, commit_clear)
    let clear := Wire.mk s!"e{i}_clear"
    let clear_gate := Gate.mkOR flush_en commit_clear clear

    -- Comparator6 instance: CDB tag vs entry physRd
    let cmp_inst : CircuitInstance := {
      moduleName := "Comparator6"
      instName := s!"u_cmp{i}"
      portMap :=
        (cdb_tag.enum.map (fun ⟨j, w⟩ => (s!"a_{j}", w))) ++
        (cur_physRd.enum.map (fun ⟨j, w⟩ => (s!"b_{j}", w))) ++
        [("one", one), ("eq", cdb_match),
         ("lt", Wire.mk s!"e{i}_cmp_lt_unused"),
         ("ltu", Wire.mk s!"e{i}_cmp_ltu_unused"),
         ("gt", Wire.mk s!"e{i}_cmp_gt_unused"),
         ("gtu", Wire.mk s!"e{i}_cmp_gtu_unused")]
    }

    -- Register24 instance: entry storage
    let reg_inst : CircuitInstance := {
      moduleName := "Register24"
      instName := s!"u_entry{i}"
      portMap :=
        (e_next.enum.map (fun ⟨j, w⟩ => (s!"d_{j}", w))) ++
        [("clock", clock), ("reset", reset_leaves[i]!)] ++
        (e_cur.enum.map (fun ⟨j, w⟩ => (s!"q_{j}", w)))
    }

    -- === Next-State Logic ===

    -- valid_next: MUX priority: alloc > clear > hold
    -- When alloc and clear hit the same entry simultaneously (ROB wrap-around),
    -- the new allocation must win — the clear is for the old entry, alloc is for the new.
    let valid_mux1 := Wire.mk s!"e{i}_valid_mux1"
    let valid_gates := [
      Gate.mkMUX cur_valid zero clear valid_mux1,       -- clear clears valid
      Gate.mkMUX valid_mux1 one alloc_we e_next[0]!     -- alloc sets valid (highest priority)
    ]

    -- complete_next: MUX priority: alloc > clear > cdb > hold
    -- On alloc: set complete = NOT(hasPhysRd OR isBranch) — only stores are immediately complete
    -- Branches always wait for CDB to get misprediction status.
    -- When alloc and clear hit simultaneously (ROB wrap-around), alloc wins.
    let alloc_imm_complete := Wire.mk s!"e{i}_alloc_imm_complete"
    let alloc_needs_cdb := Wire.mk s!"e{i}_alloc_needs_cdb"
    let comp_mux1 := Wire.mk s!"e{i}_comp_mux1"
    let comp_mux2 := Wire.mk s!"e{i}_comp_mux2"
    let complete_gates := [
      Gate.mkOR alloc_hasPhysRd alloc_isBranch alloc_needs_cdb,
      Gate.mkNOT alloc_needs_cdb alloc_imm_complete,
      Gate.mkMUX cur_complete one cdb_we comp_mux1,       -- CDB sets complete
      Gate.mkMUX comp_mux1 zero clear comp_mux2,          -- clear clears complete
      Gate.mkMUX comp_mux2 alloc_imm_complete alloc_we e_next[1]!  -- alloc wins (highest priority)
    ]

    -- physRd_next: only changes on alloc
    let physRd_gates := (List.range 6).map fun j =>
      Gate.mkMUX cur_physRd[j]! alloc_physRd[j]! alloc_we e_next[2+j]!

    -- hasPhysRd_next: only changes on alloc
    let hasPhysRd_gate :=
      Gate.mkMUX cur_hasPhysRd alloc_hasPhysRd alloc_we e_next[8]!

    -- oldPhysRd_next: only changes on alloc
    let oldPhysRd_gates := (List.range 6).map fun j =>
      Gate.mkMUX cur_oldPhysRd[j]! alloc_oldPhysRd[j]! alloc_we e_next[9+j]!

    -- hasOldPhysRd_next: only changes on alloc
    let hasOldPhysRd_gate :=
      Gate.mkMUX cur_hasOldPhysRd alloc_hasOldPhysRd alloc_we e_next[15]!

    -- archRd_next: only changes on alloc
    let archRd_gates := (List.range 5).map fun j =>
      Gate.mkMUX cur_archRd[j]! alloc_archRd[j]! alloc_we e_next[16+j]!

    -- exception_next: MUX priority: alloc > clear > cdb > hold
    let exc_mux1 := Wire.mk s!"e{i}_exc_mux1"
    let exc_mux2 := Wire.mk s!"e{i}_exc_mux2"
    let exception_gates := [
      Gate.mkMUX cur_exception cdb_exception cdb_we exc_mux1,
      Gate.mkMUX exc_mux1 zero clear exc_mux2,
      Gate.mkMUX exc_mux2 zero alloc_we e_next[21]!   -- alloc clears exception (highest priority)
    ]

    -- isBranch_next: only changes on alloc
    let isBranch_gate :=
      Gate.mkMUX cur_isBranch alloc_isBranch alloc_we e_next[22]!

    -- branchMispredicted_next: MUX priority: alloc > clear > cdb > hold
    let mis_mux1 := Wire.mk s!"e{i}_mis_mux1"
    let mis_mux2 := Wire.mk s!"e{i}_mis_mux2"
    let mispred_gates := [
      Gate.mkMUX cur_mispred cdb_mispredicted cdb_we mis_mux1,
      Gate.mkMUX mis_mux1 zero clear mis_mux2,
      Gate.mkMUX mis_mux2 zero alloc_we e_next[23]!   -- alloc clears mispred (highest priority)
    ]

    -- Collect all per-entry gates
    let entry_gates :=
      [alloc_we_gate] ++ cdb_we_gates ++ [commit_clear_gate, clear_gate] ++
      valid_gates ++ complete_gates ++
      physRd_gates ++ [hasPhysRd_gate] ++
      oldPhysRd_gates ++ [hasOldPhysRd_gate] ++
      archRd_gates ++
      exception_gates ++ [isBranch_gate] ++ mispred_gates

    (entry_gates, [cmp_inst, reg_inst], e_cur)

  -- Flatten per-entry results
  let all_entry_gates := (entryResults.map (fun (g, _, _) => g)).flatten
  let all_entry_instances := (entryResults.map (fun (_, insts, _) => insts)).flatten
  let all_entry_cur := entryResults.map (fun (_, _, cur) => cur)

  -- === Head Entry Readout via MuxTree ===

  -- MuxTree 16 6 for physRd readout (sel = head_ptr)
  let physRd_mux_inst : CircuitInstance := {
    moduleName := "Mux16x6"
    instName := "u_mux_physrd"
    portMap :=
      ((List.range 16).map (fun i =>
        let e := all_entry_cur[i]!
        (List.range 6).map (fun j => (s!"in{i}[{j}]", e[2+j]!))
      )).flatten ++
      (head_ptr.enum.map (fun ⟨k, w⟩ => (s!"sel[{k}]", w))) ++
      (head_physRd.enum.map (fun ⟨j, w⟩ => (s!"out[{j}]", w)))
  }

  -- MuxTree 16 6 for oldPhysRd readout
  let oldPhysRd_mux_inst : CircuitInstance := {
    moduleName := "Mux16x6"
    instName := "u_mux_oldphysrd"
    portMap :=
      ((List.range 16).map (fun i =>
        let e := all_entry_cur[i]!
        (List.range 6).map (fun j => (s!"in{i}[{j}]", e[9+j]!))
      )).flatten ++
      (head_ptr.enum.map (fun ⟨k, w⟩ => (s!"sel[{k}]", w))) ++
      (head_oldPhysRd.enum.map (fun ⟨j, w⟩ => (s!"out[{j}]", w)))
  }

  -- MuxTree 16 5 for archRd readout
  let archRd_mux_inst : CircuitInstance := {
    moduleName := "Mux16x5"
    instName := "u_mux_archrd"
    portMap :=
      ((List.range 16).map (fun i =>
        let e := all_entry_cur[i]!
        (List.range 5).map (fun j => (s!"in{i}[{j}]", e[16+j]!))
      )).flatten ++
      (head_ptr.enum.map (fun ⟨k, w⟩ => (s!"sel[{k}]", w))) ++
      (head_archRd.enum.map (fun ⟨j, w⟩ => (s!"out[{j}]", w)))
  }

  -- Single-bit head readout via AND/OR tree
  -- head_field = OR-tree(AND(commit_decode[i], entry_i_field) for i in 0..15)
  let mkBitReadout (name : String) (bitIdx : Nat) (output : Wire) : List Gate :=
    -- Layer 1: 16 AND gates
    let ands := (List.range 16).map fun i =>
      let e := all_entry_cur[i]!
      let w := Wire.mk s!"hr_{name}_a{i}"
      (Gate.mkAND commit_decode[i]! e[bitIdx]! w, w)
    let and_gates := ands.map Prod.fst
    let and_outs := ands.map Prod.snd
    -- Layer 2: OR tree 16→8
    let l2 := (List.range 8).map fun i =>
      let w := Wire.mk s!"hr_{name}_l2_{i}"
      (Gate.mkOR and_outs[2*i]! and_outs[2*i+1]! w, w)
    let l2_gates := l2.map Prod.fst
    let l2_outs := l2.map Prod.snd
    -- Layer 3: OR tree 8→4
    let l3 := (List.range 4).map fun i =>
      let w := Wire.mk s!"hr_{name}_l3_{i}"
      (Gate.mkOR l2_outs[2*i]! l2_outs[2*i+1]! w, w)
    let l3_gates := l3.map Prod.fst
    let l3_outs := l3.map Prod.snd
    -- Layer 4: OR tree 4→2
    let l4 := (List.range 2).map fun i =>
      let w := Wire.mk s!"hr_{name}_l4_{i}"
      (Gate.mkOR l3_outs[2*i]! l3_outs[2*i+1]! w, w)
    let l4_gates := l4.map Prod.fst
    let l4_outs := l4.map Prod.snd
    -- Layer 5: OR tree 2→1
    let final := Gate.mkOR l4_outs[0]! l4_outs[1]! output
    and_gates ++ l2_gates ++ l3_gates ++ l4_gates ++ [final]

  let head_readout_gates :=
    mkBitReadout "valid" 0 head_valid ++
    mkBitReadout "complete" 1 head_complete ++
    mkBitReadout "hasPhysRd" 8 head_hasPhysRd ++
    mkBitReadout "hasOldPhysRd" 15 head_hasOldPhysRd ++
    mkBitReadout "exception" 21 head_exception ++
    mkBitReadout "isBranch" 22 head_isBranch ++
    mkBitReadout "mispred" 23 head_mispredicted

  -- === Assemble Circuit ===

  let all_inputs :=
    [clock, reset, zero, one] ++
    [alloc_en] ++ alloc_physRd ++ [alloc_hasPhysRd] ++
    alloc_oldPhysRd ++ [alloc_hasOldPhysRd] ++ alloc_archRd ++ [alloc_isBranch] ++
    [cdb_valid] ++ cdb_tag ++ [cdb_exception, cdb_mispredicted, cdb_is_fp] ++
    is_fp_shadow ++
    [commit_en, flush_en]

  let all_outputs :=
    [full, empty] ++ alloc_idx ++ head_idx ++
    [head_valid, head_complete] ++ head_physRd ++ [head_hasPhysRd] ++
    head_oldPhysRd ++ [head_hasOldPhysRd] ++ head_archRd ++
    [head_exception, head_isBranch, head_mispredicted]

  let all_gates :=
    global_gates ++ [full_gate] ++ empty_gates ++ commit_safe_gates ++ alloc_idx_gates ++ head_idx_gates ++
    reset_buf_gates ++ all_entry_gates ++ head_readout_gates

  let all_instances :=
    [head_inst, tail_inst, count_inst, alloc_dec_inst, commit_dec_inst] ++
    all_entry_instances ++
    [physRd_mux_inst, oldPhysRd_mux_inst, archRd_mux_inst]

  { name := "ROB16"
    inputs := all_inputs
    outputs := all_outputs
    gates := all_gates
    instances := all_instances
    -- V2 codegen annotations
    signalGroups := [
      { name := "alloc_physRd", width := 6, wires := alloc_physRd },
      { name := "alloc_oldPhysRd", width := 6, wires := alloc_oldPhysRd },
      { name := "alloc_archRd", width := 5, wires := alloc_archRd },
      { name := "cdb_tag", width := 6, wires := cdb_tag },
      { name := "alloc_idx", width := 4, wires := alloc_idx },
      { name := "head_idx", width := 4, wires := head_idx },
      { name := "head_physRd", width := 6, wires := head_physRd },
      { name := "head_oldPhysRd", width := 6, wires := head_oldPhysRd },
      { name := "head_archRd", width := 5, wires := head_archRd }
    ]
  }
  else
  -- === W=2: Dual-alloc, dual-commit ROB (from ROB_W2.lean) ===
  --
  -- Port additions vs. single-issue:
  -- Alloc: adds alloc_en_1, alloc_physRd_1[5:0], alloc_hasPhysRd_1,
  --         alloc_oldPhysRd_1[5:0], alloc_hasOldPhysRd_1, alloc_archRd_1[4:0],
  --         alloc_isBranch_1, alloc_idx_1[3:0]
  -- Commit: adds commit_en_1, head_valid_1, head_complete_1, head_physRd_1[5:0],
  --         head_hasPhysRd_1, head_oldPhysRd_1[5:0], head_hasOldPhysRd_1,
  --         head_archRd_1[4:0], head_exception_1, head_isBranch_1, head_mispredicted_1
  --
  -- Commit rule: commit_en_1 is only honoured when commit_en_0 also fires
  -- (slot 1 only retires if slot 0 does -- enforces in-order retirement).
  let mkWires2 := @Shoumei.Circuits.Combinational.makeIndexedWires
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero  := Wire.mk "zero"
  let one   := Wire.mk "one"

  -- === Alloc Slot 0 ===
  let alloc_en_0        := Wire.mk "alloc_en_0"
  let alloc_physRd_0    := mkWires2 "alloc_physRd_0" 6
  let alloc_hasPhysRd_0 := Wire.mk "alloc_hasPhysRd_0"
  let alloc_oldPhysRd_0 := mkWires2 "alloc_oldPhysRd_0" 6
  let alloc_hasOldPR_0  := Wire.mk "alloc_hasOldPhysRd_0"
  let alloc_archRd_0    := mkWires2 "alloc_archRd_0" 5
  let alloc_isBranch_0  := Wire.mk "alloc_isBranch_0"
  let alloc_idx_0       := mkWires2 "alloc_idx_0" 4

  -- === Alloc Slot 1 ===
  let alloc_en_1        := Wire.mk "alloc_en_1"
  let alloc_physRd_1    := mkWires2 "alloc_physRd_1" 6
  let alloc_hasPhysRd_1 := Wire.mk "alloc_hasPhysRd_1"
  let alloc_oldPhysRd_1 := mkWires2 "alloc_oldPhysRd_1" 6
  let alloc_hasOldPR_1  := Wire.mk "alloc_hasOldPhysRd_1"
  let alloc_archRd_1    := mkWires2 "alloc_archRd_1" 5
  let alloc_isBranch_1  := Wire.mk "alloc_isBranch_1"
  let alloc_idx_1       := mkWires2 "alloc_idx_1" 4

  -- === CDB Interface (W=2) ===
  let cdb_valid_0     := Wire.mk "cdb_valid"
  let cdb_tag         := mkWires2 "cdb_tag" 6
  let cdb_exception_0 := Wire.mk "cdb_exception"
  let cdb_mispred_0   := Wire.mk "cdb_mispredicted"
  let cdb_is_fp_0     := Wire.mk "cdb_is_fp"

  let cdb_valid_1     := Wire.mk "cdb_valid_1"
  let cdb_tag_1       := mkWires2 "cdb_tag_1" 6
  let cdb_exception_1 := Wire.mk "cdb_exception_1"
  let cdb_mispred_1   := Wire.mk "cdb_mispredicted_1"
  let cdb_is_fp_1     := Wire.mk "cdb_is_fp_1"

  let is_fp_shadow  := (List.range 16).map (fun i => Wire.mk s!"is_fp_shadow_{i}")

  -- === Commit / Flush ===
  let commit_en_0 := Wire.mk "commit_en_0"
  let commit_en_1 := Wire.mk "commit_en_1"
  let flush_en    := Wire.mk "flush_en"

  -- === Status ===
  let full  := Wire.mk "full"
  let empty := Wire.mk "empty"

  -- === Internal Pointers ===
  let head_ptr  := mkWires2 "head_ptr" 4
  let tail_ptr  := mkWires2 "tail_ptr" 4
  -- tail + 1 mod 16 (combinational carry-ripple)
  let tail1_ptr := mkWires2 "tail1_ptr" 4
  -- head + 1 mod 16 (combinational carry-ripple)
  let head1_ptr := mkWires2 "head1_ptr" 4
  let count     := mkWires2 "count" 5

  -- tail1 = tail + 1 mod 16 (4-bit ripple carry with initial cin=1)
  let t1_c := (List.range 5).map (fun i => Wire.mk s!"t1c_{i}")
  let t1_s := (List.range 4).map (fun i => Wire.mk s!"t1s_{i}")
  let tail1_gates :=
    [Gate.mkBUF one t1_c[0]!] ++
    (List.range 4).map (fun i => Gate.mkXOR tail_ptr[i]! t1_c[i]! t1_s[i]!) ++
    (List.range 4).map (fun i => Gate.mkAND tail_ptr[i]! t1_c[i]! t1_c[i+1]!) ++
    (List.range 4).map (fun i => Gate.mkBUF t1_s[i]! tail1_ptr[i]!)

  -- head1 = head + 1 mod 16
  let h1_c := (List.range 5).map (fun i => Wire.mk s!"h1c_{i}")
  let h1_s := (List.range 4).map (fun i => Wire.mk s!"h1s_{i}")
  let head1_gates :=
    [Gate.mkBUF one h1_c[0]!] ++
    (List.range 4).map (fun i => Gate.mkXOR head_ptr[i]! h1_c[i]! h1_s[i]!) ++
    (List.range 4).map (fun i => Gate.mkAND head_ptr[i]! h1_c[i]! h1_c[i+1]!) ++
    (List.range 4).map (fun i => Gate.mkBUF h1_s[i]! head1_ptr[i]!)

  -- count >= 2 = OR(count[4:1])
  let cge2_t1   := Wire.mk "cge2_t1"
  let cge2_t2   := Wire.mk "cge2_t2"
  let count_ge2 := Wire.mk "count_ge2"
  let count_ge2_gates := [
    Gate.mkOR count[1]! count[2]! cge2_t1,
    Gate.mkOR count[3]! count[4]! cge2_t2,
    Gate.mkOR cge2_t1 cge2_t2 count_ge2
  ]

  -- commit_en_0_safe = commit_en_0 AND (count >= 1)
  -- commit_en_1_safe = commit_en_1 AND commit_en_0_safe AND (count >= 2)
  let not_empty_w      := Wire.mk "not_empty_w"
  let commit_en_0_safe := Wire.mk "commit_en_0_safe"
  let commit_en_1_tmp  := Wire.mk "commit_en_1_tmp"
  let commit_en_1_safe := Wire.mk "commit_en_1_safe"
  let count_safe_gates := [
    Gate.mkOR count[0]! count[1]! not_empty_w,
    Gate.mkAND commit_en_0 not_empty_w commit_en_0_safe,
    Gate.mkAND commit_en_1 commit_en_0_safe commit_en_1_tmp,
    Gate.mkAND commit_en_1_tmp count_ge2 commit_en_1_safe
  ]

  -- alloc_idx outputs: slot 0 → tail, slot 1 → tail+1
  let alloc_idx_0_gates := List.zipWith Gate.mkBUF tail_ptr  alloc_idx_0
  let alloc_idx_1_gates := List.zipWith Gate.mkBUF tail1_ptr alloc_idx_1

  -- empty / full
  let eo1 := Wire.mk "w2_eo1"; let eo2 := Wire.mk "w2_eo2"
  let eo3 := Wire.mk "w2_eo3"; let eo4 := Wire.mk "w2_eo4"
  let empty_gates := [
    Gate.mkOR count[0]! count[1]! eo1,
    Gate.mkOR eo1 count[2]! eo2,
    Gate.mkOR eo2 count[3]! eo3,
    Gate.mkOR eo3 count[4]! eo4,
    Gate.mkNOT eo4 empty,
    Gate.mkBUF count[4]! full
  ]

  -- === Alloc Decoders (Decoder4) ===
  let alloc_dec_0 := mkWires2 "alloc_dec_0" 16
  let alloc_dec_0_inst : CircuitInstance := {
    moduleName := "Decoder4"
    instName := "u_alloc_dec_0"
    portMap := (tail_ptr.enum.map fun ⟨i,w⟩ => (s!"in_{i}", w)) ++
               (alloc_dec_0.enum.map fun ⟨i,w⟩ => (s!"out_{i}", w))
  }
  let alloc_dec_1 := mkWires2 "alloc_dec_1" 16
  let alloc_dec_1_inst : CircuitInstance := {
    moduleName := "Decoder4"
    instName := "u_alloc_dec_1"
    portMap := (tail1_ptr.enum.map fun ⟨i,w⟩ => (s!"in_{i}", w)) ++
               (alloc_dec_1.enum.map fun ⟨i,w⟩ => (s!"out_{i}", w))
  }

  -- === Commit Decoders ===
  let commit_dec_0 := mkWires2 "commit_dec_0" 16
  let commit_dec_0_inst : CircuitInstance := {
    moduleName := "Decoder4"
    instName := "u_commit_dec_0"
    portMap := (head_ptr.enum.map fun ⟨i,w⟩ => (s!"in_{i}", w)) ++
               (commit_dec_0.enum.map fun ⟨i,w⟩ => (s!"out_{i}", w))
  }
  let commit_dec_1 := mkWires2 "commit_dec_1" 16
  let commit_dec_1_inst : CircuitInstance := {
    moduleName := "Decoder4"
    instName := "u_commit_dec_1"
    portMap := (head1_ptr.enum.map fun ⟨i,w⟩ => (s!"in_{i}", w)) ++
               (commit_dec_1.enum.map fun ⟨i,w⟩ => (s!"out_{i}", w))
  }

  -- === Reset buffer tree ===
  let rr := (List.range 4).map  (fun i => Wire.mk s!"w2_rr_{i}")
  let rb := (List.range 16).map (fun i => Wire.mk s!"w2_rb_{i}")
  let reset_buf_gates2 :=
    (List.range 4).map  (fun i => Gate.mkBUF reset rr[i]!) ++
    (List.range 16).map (fun i => Gate.mkBUF rr[i/4]! rb[i]!)

  -- === Per-Entry Logic (16 entries) ===
  let entryResults2 := (List.range 16).map fun i =>
    let e_cur  := mkWires2 s!"e{i}" 24
    let e_next := mkWires2 s!"e{i}_nx" 24

    let cur_valid    := e_cur[0]!
    let cur_complete := e_cur[1]!
    let cur_physRd   := (List.range 6).map fun j => e_cur[2+j]!
    let cur_hasPhRd  := e_cur[8]!
    let cur_oldPhRd  := (List.range 6).map fun j => e_cur[9+j]!
    let cur_hasOPR   := e_cur[15]!
    let cur_archRd   := (List.range 5).map fun j => e_cur[16+j]!
    let cur_exc      := e_cur[21]!
    let cur_isBr     := e_cur[22]!
    let cur_misp     := e_cur[23]!

    -- Alloc write-enables (OR of both slots' decoder outputs AND alloc_en)
    let awe0 := Wire.mk s!"e{i}_awe0"
    let awe1 := Wire.mk s!"e{i}_awe1"
    let awe  := Wire.mk s!"e{i}_awe"
    let awe_gates := [
      Gate.mkAND alloc_en_0 alloc_dec_0[i]! awe0,
      Gate.mkAND alloc_en_1 alloc_dec_1[i]! awe1,
      Gate.mkOR  awe0 awe1 awe
    ]

    -- Select alloc data: slot 1 takes priority if both write (tags shouldn't collide in practice)
    let sel (pfx : String) (w0 w1 : Wire) : Gate × Wire :=
      let out := Wire.mk s!"e{i}_s{pfx}"
      (Gate.mkMUX w0 w1 awe1 out, out)

    let sel6 (pfx : String) (ws0 ws1 : List Wire) : List Gate × List Wire :=
      let pairs := (List.range 6).map fun j =>
        let out := Wire.mk s!"e{i}_s{pfx}{j}"
        (Gate.mkMUX ws0[j]! ws1[j]! awe1 out, out)
      (pairs.map Prod.fst, pairs.map Prod.snd)

    let sel5 (pfx : String) (ws0 ws1 : List Wire) : List Gate × List Wire :=
      let pairs := (List.range 5).map fun j =>
        let out := Wire.mk s!"e{i}_s{pfx}{j}"
        (Gate.mkMUX ws0[j]! ws1[j]! awe1 out, out)
      (pairs.map Prod.fst, pairs.map Prod.snd)

    let (g_physRd, sel_physRd)   := sel6 "pr"  alloc_physRd_0  alloc_physRd_1
    let (g_hasPhRd, sel_hasPhRd) := sel "hpr"  alloc_hasPhysRd_0 alloc_hasPhysRd_1
    let (g_oldPhRd, sel_oldPhRd) := sel6 "opr" alloc_oldPhysRd_0 alloc_oldPhysRd_1
    let (g_hasOPR, sel_hasOPR)   := sel "hopr" alloc_hasOldPR_0 alloc_hasOldPR_1
    let (g_archRd, sel_archRd)   := sel5 "ar"  alloc_archRd_0  alloc_archRd_1
    let (g_isBr, sel_isBr)       := sel "ibr"  alloc_isBranch_0 alloc_isBranch_1

    let sel_gates := g_physRd ++ [g_hasPhRd] ++ g_oldPhRd ++ [g_hasOPR] ++ g_archRd ++ [g_isBr]
    let sel_hasPhRd_w := sel_hasPhRd
    let sel_isBr_w    := sel_isBr

    -- CDB match (dual port): independently check vs. CDB 0 and CDB 1
    let cm0 := Wire.mk s!"e{i}_cm0"; let cm1 := Wire.mk s!"e{i}_cm1"
    let cmp0_inst : CircuitInstance := {
      moduleName := "Comparator6", instName := s!"u_cmp{i}_0",
      portMap := (cdb_tag.enum.map fun (jw : Nat × Wire) => (s!"a_{jw.1}", jw.2)) ++
                 (cur_physRd.enum.map fun (jw : Nat × Wire) => (s!"b_{jw.1}", jw.2)) ++
                 [("one", one), ("eq", cm0)]
    }
    let cmp1_inst : CircuitInstance := {
      moduleName := "Comparator6", instName := s!"u_cmp{i}_1",
      portMap := (cdb_tag_1.enum.map fun (jw : Nat × Wire) => (s!"a_{jw.1}", jw.2)) ++
                 (cur_physRd.enum.map fun (jw : Nat × Wire) => (s!"b_{jw.1}", jw.2)) ++
                 [("one", one), ("eq", cm1)]
    }

    let cn := Wire.mk s!"e{i}_cn"
    let hpob := Wire.mk s!"e{i}_hpob"
    let cdb_we_0 := Wire.mk s!"e{i}_cwe0"; let cdb_we_1 := Wire.mk s!"e{i}_cwe1"
    let cwe      := Wire.mk s!"e{i}_cwe"
    let exc_sel  := Wire.mk s!"e{i}_exc_sel"
    let mis_sel  := Wire.mk s!"e{i}_mis_sel"

    let cdb_we_gates := [
      Gate.mkNOT cur_complete cn,
      Gate.mkOR  cur_hasPhRd cur_isBr hpob,
      -- Port 0 write-enable
      Gate.mkAND cur_valid cn (Wire.mk s!"e{i}_ct0_1"),
      Gate.mkAND (Wire.mk s!"e{i}_ct0_1") hpob (Wire.mk s!"e{i}_ct0_2"),
      Gate.mkAND (Wire.mk s!"e{i}_ct0_2") cm0 (Wire.mk s!"e{i}_ct0_3"),
      Gate.mkAND (Wire.mk s!"e{i}_ct0_3") cdb_valid_0 (Wire.mk s!"e{i}_ct0_4"),
      Gate.mkXOR cdb_is_fp_0 is_fp_shadow[i]! (Wire.mk s!"e{i}_dx0"),
      Gate.mkNOT (Wire.mk s!"e{i}_dx0") (Wire.mk s!"e{i}_dm0"),
      Gate.mkAND (Wire.mk s!"e{i}_ct0_4") (Wire.mk s!"e{i}_dm0") cdb_we_0,
      -- Port 1 write-enable
      Gate.mkAND cur_valid cn (Wire.mk s!"e{i}_ct1_1"),
      Gate.mkAND (Wire.mk s!"e{i}_ct1_1") hpob (Wire.mk s!"e{i}_ct1_2"),
      Gate.mkAND (Wire.mk s!"e{i}_ct1_2") cm1 (Wire.mk s!"e{i}_ct1_3"),
      Gate.mkAND (Wire.mk s!"e{i}_ct1_3") cdb_valid_1 (Wire.mk s!"e{i}_ct1_4"),
      Gate.mkXOR cdb_is_fp_1 is_fp_shadow[i]! (Wire.mk s!"e{i}_dx1"),
      Gate.mkNOT (Wire.mk s!"e{i}_dx1") (Wire.mk s!"e{i}_dm1"),
      Gate.mkAND (Wire.mk s!"e{i}_ct1_4") (Wire.mk s!"e{i}_dm1") cdb_we_1,
      -- Combined WE (Port 1 priority for exception/mispred mux if both hit)
      Gate.mkOR cdb_we_0 cdb_we_1 cwe,
      Gate.mkMUX cdb_exception_0 cdb_exception_1 cdb_we_1 exc_sel,
      Gate.mkMUX cdb_mispred_0 cdb_mispred_1 cdb_we_1 mis_sel
    ]

    -- Commit clear
    let cc0 := Wire.mk s!"e{i}_cc0"; let cc1 := Wire.mk s!"e{i}_cc1"
    let commit_clear := Wire.mk s!"e{i}_cc"
    let cc_gates := [
      Gate.mkAND commit_en_0_safe commit_dec_0[i]! cc0,
      Gate.mkAND commit_en_1_safe commit_dec_1[i]! cc1,
      Gate.mkOR  cc0 cc1 commit_clear
    ]
    let clear := Wire.mk s!"e{i}_cl"
    let clear_gate := Gate.mkOR flush_en commit_clear clear

    let anc := Wire.mk s!"e{i}_anc"; let aic := Wire.mk s!"e{i}_aic"

    -- Next-state MUX chain
    let vm1 := Wire.mk s!"e{i}_vm1"
    let valid_gates := [
      Gate.mkMUX cur_valid zero clear vm1,
      Gate.mkMUX vm1 one awe e_next[0]!
    ]
    let cpm1 := Wire.mk s!"e{i}_cpm1"; let cpm2 := Wire.mk s!"e{i}_cpm2"
    let comp_gates := [
      Gate.mkOR  sel_hasPhRd_w sel_isBr_w anc,
      Gate.mkNOT anc aic,
      Gate.mkMUX cur_complete one cwe cpm1,
      Gate.mkMUX cpm1 zero clear cpm2,
      Gate.mkMUX cpm2 aic awe e_next[1]!
    ]
    let physRd_gates := (List.range 6).map fun j =>
      Gate.mkMUX cur_physRd[j]! sel_physRd[j]! awe e_next[2+j]!
    let hasPR_gate  := Gate.mkMUX cur_hasPhRd sel_hasPhRd_w awe e_next[8]!
    let oldPR_gates := (List.range 6).map fun j =>
      Gate.mkMUX cur_oldPhRd[j]! sel_oldPhRd[j]! awe e_next[9+j]!
    let hasOPR_gate := Gate.mkMUX cur_hasOPR sel_hasOPR awe e_next[15]!
    let archRd_gates := (List.range 5).map fun j =>
      Gate.mkMUX cur_archRd[j]! sel_archRd[j]! awe e_next[16+j]!
    let em1 := Wire.mk s!"e{i}_em1"; let em2 := Wire.mk s!"e{i}_em2"
    let exc_gates := [
      Gate.mkMUX cur_exc exc_sel cwe em1,
      Gate.mkMUX em1 zero clear em2,
      Gate.mkMUX em2 zero awe e_next[21]!
    ]
    let isBr_gate := Gate.mkMUX cur_isBr sel_isBr_w awe e_next[22]!
    let mm1 := Wire.mk s!"e{i}_mm1"; let mm2 := Wire.mk s!"e{i}_mm2"
    let misp_gates := [
      Gate.mkMUX cur_misp mis_sel cwe mm1,
      Gate.mkMUX mm1 zero clear mm2,
      Gate.mkMUX mm2 zero awe e_next[23]!
    ]

    let reg_inst : CircuitInstance := {
      moduleName := "Register24"
      instName := s!"u_entry{i}"
      portMap :=
        (e_next.enum.map (fun (jw : Nat × Wire) => (s!"d_{jw.1}", jw.2))) ++
        [("clock", clock), ("reset", rb[i]!)] ++
        (e_cur.enum.map (fun (jw : Nat × Wire) => (s!"q_{jw.1}", jw.2)))
    }

    let entry_gates :=
      awe_gates ++ sel_gates ++ cdb_we_gates ++ cc_gates ++
      [clear_gate] ++ valid_gates ++ comp_gates ++
      physRd_gates ++ [hasPR_gate] ++ oldPR_gates ++ [hasOPR_gate] ++
      archRd_gates ++ exc_gates ++ [isBr_gate] ++ misp_gates

    (entry_gates, [cmp0_inst, cmp1_inst, reg_inst], e_cur)

  let all_entry_gates2     := (entryResults2.map (fun (g,_,_) => g)).flatten
  let all_entry_instances2 := (entryResults2.map (fun (_,i,_) => i)).flatten
  let all_entry_cur2       :=  entryResults2.map (fun (_,_,c) => c)

  -- OR-tree readout helper for single-bit fields
  let mkBitReadout2 (pfx name : String) (dec : List Wire) (bitIdx : Nat) (out : Wire)
      : List Gate :=
    let ands := (List.range 16).map fun i =>
      let e := all_entry_cur2[i]!
      let w := Wire.mk s!"{pfx}_{name}_a{i}"
      (Gate.mkAND dec[i]! e[bitIdx]! w, w)
    let l2 := (List.range 8).map fun i =>
      let w := Wire.mk s!"{pfx}_{name}_l2_{i}"
      (Gate.mkOR (ands.map Prod.snd)[2*i]! (ands.map Prod.snd)[2*i+1]! w, w)
    let l3 := (List.range 4).map fun i =>
      let w := Wire.mk s!"{pfx}_{name}_l3_{i}"
      (Gate.mkOR (l2.map Prod.snd)[2*i]! (l2.map Prod.snd)[2*i+1]! w, w)
    let l4 := (List.range 2).map fun i =>
      let w := Wire.mk s!"{pfx}_{name}_l4_{i}"
      (Gate.mkOR (l3.map Prod.snd)[2*i]! (l3.map Prod.snd)[2*i+1]! w, w)
    ands.map Prod.fst ++ l2.map Prod.fst ++ l3.map Prod.fst ++ l4.map Prod.fst ++
    [Gate.mkOR (l4.map Prod.snd)[0]! (l4.map Prod.snd)[1]! out]

  -- Mux readout helper
  let mkMuxReadout2 (instName modName : String) (bitStart bitCount : Nat)
      (sel_ptr : List Wire) (outs : List Wire) : CircuitInstance := {
    moduleName := modName
    instName := instName
    portMap :=
      ((List.range 16).map fun i =>
        let e := all_entry_cur2[i]!
        (List.range bitCount).map fun j => (s!"in{i}[{j}]", e[bitStart+j]!)
      ).flatten ++
      (sel_ptr.enum.map (fun (jw : Nat × Wire) => (s!"sel[{jw.1}]", jw.2))) ++
      (outs.enum.map (fun (jw : Nat × Wire) => (s!"out[{jw.1}]", jw.2)))
  }

  -- === Commit Slot 0 Outputs ===
  let hv0    := Wire.mk "head_valid_0";    let hcmp0  := Wire.mk "head_complete_0"
  let hpr0   := mkWires2 "head_physRd_0" 6;  let hhpr0  := Wire.mk "head_hasPhysRd_0"
  let hopr0  := mkWires2 "head_oldPhysRd_0" 6; let hhopr0 := Wire.mk "head_hasOldPhysRd_0"
  let har0   := mkWires2 "head_archRd_0" 5
  let hexc0  := Wire.mk "head_exception_0"; let hibr0  := Wire.mk "head_isBranch_0"
  let hmisp0 := Wire.mk "head_mispredicted_0"

  -- === Commit Slot 1 Outputs ===
  let hv1    := Wire.mk "head_valid_1";    let hcmp1  := Wire.mk "head_complete_1"
  let hpr1   := mkWires2 "head_physRd_1" 6;  let hhpr1  := Wire.mk "head_hasPhysRd_1"
  let hopr1  := mkWires2 "head_oldPhysRd_1" 6; let hhopr1 := Wire.mk "head_hasOldPhysRd_1"
  let har1   := mkWires2 "head_archRd_1" 5
  let hexc1  := Wire.mk "head_exception_1"; let hibr1  := Wire.mk "head_isBranch_1"
  let hmisp1 := Wire.mk "head_mispredicted_1"

  let pr_mux_0  := mkMuxReadout2 "u_mux_pr_0"  "Mux16x6" 2  6 head_ptr  hpr0
  let opr_mux_0 := mkMuxReadout2 "u_mux_opr_0" "Mux16x6" 9  6 head_ptr  hopr0
  let ar_mux_0  := mkMuxReadout2 "u_mux_ar_0"  "Mux16x5" 16 5 head_ptr  har0
  let pr_mux_1  := mkMuxReadout2 "u_mux_pr_1"  "Mux16x6" 2  6 head1_ptr hpr1
  let opr_mux_1 := mkMuxReadout2 "u_mux_opr_1" "Mux16x6" 9  6 head1_ptr hopr1
  let ar_mux_1  := mkMuxReadout2 "u_mux_ar_1"  "Mux16x5" 16 5 head1_ptr har1

  let ro0 :=
    mkBitReadout2 "s0" "valid"    commit_dec_0 0  hv0   ++
    mkBitReadout2 "s0" "complete" commit_dec_0 1  hcmp0 ++
    mkBitReadout2 "s0" "hasPhRd"  commit_dec_0 8  hhpr0 ++
    mkBitReadout2 "s0" "hasOPR"   commit_dec_0 15 hhopr0 ++
    mkBitReadout2 "s0" "exc"      commit_dec_0 21 hexc0 ++
    mkBitReadout2 "s0" "isBr"     commit_dec_0 22 hibr0 ++
    mkBitReadout2 "s0" "misp"     commit_dec_0 23 hmisp0
  let ro1 :=
    mkBitReadout2 "s1" "valid"    commit_dec_1 0  hv1   ++
    mkBitReadout2 "s1" "complete" commit_dec_1 1  hcmp1 ++
    mkBitReadout2 "s1" "hasPhRd"  commit_dec_1 8  hhpr1 ++
    mkBitReadout2 "s1" "hasOPR"   commit_dec_1 15 hhopr1 ++
    mkBitReadout2 "s1" "exc"      commit_dec_1 21 hexc1 ++
    mkBitReadout2 "s1" "isBr"     commit_dec_1 22 hibr1 ++
    mkBitReadout2 "s1" "misp"     commit_dec_1 23 hmisp1

  -- === Head/Tail Pointer + Counter Instances ===
  let head_idx_0 := mkWires2 "head_idx_0" 4
  let head_idx_1 := mkWires2 "head_idx_1" 4
  let head_idx_gates :=
    List.zipWith Gate.mkBUF head_ptr  head_idx_0 ++
    List.zipWith Gate.mkBUF head1_ptr head_idx_1

  let head_inst2 : CircuitInstance := {
    moduleName := "QueuePointer_4"
    instName := "u_head"
    portMap := [("clock", clock), ("reset", reset), ("en", commit_en_0_safe),
                ("one", one), ("zero", zero)] ++
               (head_ptr.enum.map (fun (jw : Nat × Wire) => (s!"count_{jw.1}", jw.2)))
  }
  let tail_inst_0 : CircuitInstance := {
    moduleName := "QueuePointer_4"
    instName := "u_tail_s0"
    portMap := [("clock", clock), ("reset", reset), ("en", alloc_en_0),
                ("one", one), ("zero", zero)] ++
               (mkWires2 "tail_mid" 4).enum.map (fun (jw : Nat × Wire) => (s!"count_{jw.1}", jw.2))
  }
  let tail_inst_1 : CircuitInstance := {
    moduleName := "QueuePointer_4"
    instName := "u_tail_s1"
    portMap := [("clock", clock), ("reset", reset), ("en", alloc_en_1),
                ("one", one), ("zero", zero)] ++
               (tail_ptr.enum.map (fun (jw : Nat × Wire) => (s!"count_{jw.1}", jw.2)))
  }
  -- head slot-1 pointer: we derive head+1 combinationally via head1_ptr
  let count_inst_0 : CircuitInstance := {
    moduleName := "QueueCounterUpDown_5"
    instName := "u_count_s0"
    portMap := [("clock", clock), ("reset", reset),
                ("inc", alloc_en_0), ("dec", commit_en_0_safe),
                ("one", one), ("zero", zero)] ++
               (mkWires2 "count_mid" 5).enum.map (fun (jw : Nat × Wire) => (s!"count_{jw.1}", jw.2))
  }
  let count_inst_1 : CircuitInstance := {
    moduleName := "QueueCounterUpDown_5"
    instName := "u_count_s1"
    portMap := [("clock", clock), ("reset", reset),
                ("inc", alloc_en_1), ("dec", commit_en_1_safe),
                ("one", one), ("zero", zero)] ++
               (count.enum.map (fun (jw : Nat × Wire) => (s!"count_{jw.1}", jw.2)))
  }

  -- === Assemble ===
  let all_inputs2 :=
    [clock, reset, zero, one,
     alloc_en_0] ++ alloc_physRd_0 ++ [alloc_hasPhysRd_0] ++
    alloc_oldPhysRd_0 ++ [alloc_hasOldPR_0] ++ alloc_archRd_0 ++ [alloc_isBranch_0] ++
    [alloc_en_1] ++ alloc_physRd_1 ++ [alloc_hasPhysRd_1] ++
    alloc_oldPhysRd_1 ++ [alloc_hasOldPR_1] ++ alloc_archRd_1 ++ [alloc_isBranch_1] ++
    [cdb_valid_0] ++ cdb_tag ++ [cdb_exception_0, cdb_mispred_0, cdb_is_fp_0] ++
    [cdb_valid_1] ++ cdb_tag_1 ++ [cdb_exception_1, cdb_mispred_1, cdb_is_fp_1] ++
    is_fp_shadow ++ [commit_en_0, commit_en_1, flush_en]

  let all_outputs2 :=
    [full, empty] ++ alloc_idx_0 ++ alloc_idx_1 ++
    head_idx_0 ++ head_idx_1 ++
    [hv0, hcmp0] ++ hpr0 ++ [hhpr0] ++ hopr0 ++ [hhopr0] ++ har0 ++ [hexc0, hibr0, hmisp0] ++
    [hv1, hcmp1] ++ hpr1 ++ [hhpr1] ++ hopr1 ++ [hhopr1] ++ har1 ++ [hexc1, hibr1, hmisp1]

  let all_gates2 :=
    tail1_gates ++ head1_gates ++ count_ge2_gates ++ count_safe_gates ++
    alloc_idx_0_gates ++ alloc_idx_1_gates ++ empty_gates ++ reset_buf_gates2 ++
    all_entry_gates2 ++ ro0 ++ ro1 ++ head_idx_gates

  let all_instances2 :=
    [head_inst2, tail_inst_0, tail_inst_1, count_inst_0, count_inst_1,
     alloc_dec_0_inst, alloc_dec_1_inst, commit_dec_0_inst, commit_dec_1_inst] ++
    all_entry_instances2 ++
    [pr_mux_0, opr_mux_0, ar_mux_0, pr_mux_1, opr_mux_1, ar_mux_1]

  { name := "ROB16_W2"
    inputs := all_inputs2
    outputs := all_outputs2
    gates := all_gates2
    instances := all_instances2
    signalGroups := [
      { name := "alloc_physRd_0",    width := 6, wires := alloc_physRd_0 },
      { name := "alloc_oldPhysRd_0", width := 6, wires := alloc_oldPhysRd_0 },
      { name := "alloc_archRd_0",    width := 5, wires := alloc_archRd_0 },
      { name := "alloc_physRd_1",    width := 6, wires := alloc_physRd_1 },
      { name := "alloc_oldPhysRd_1", width := 6, wires := alloc_oldPhysRd_1 },
      { name := "alloc_archRd_1",    width := 5, wires := alloc_archRd_1 },
      { name := "cdb_tag",         width := 6, wires := cdb_tag },
      { name := "cdb_tag_1",         width := 6, wires := cdb_tag_1 },
      { name := "alloc_idx_0",       width := 4, wires := alloc_idx_0 },
      { name := "alloc_idx_1",       width := 4, wires := alloc_idx_1 },
      { name := "head_idx_0",        width := 4, wires := head_idx_0 },
      { name := "head_idx_1",        width := 4, wires := head_idx_1 },
      { name := "head_physRd_0",     width := 6, wires := hpr0 },
      { name := "head_oldPhysRd_0",  width := 6, wires := hopr0 },
      { name := "head_archRd_0",     width := 5, wires := har0 },
      { name := "head_physRd_1",     width := 6, wires := hpr1 },
      { name := "head_oldPhysRd_1",  width := 6, wires := hopr1 },
      { name := "head_archRd_1",     width := 5, wires := har1 }
    ]
  }

/-- Config-driven ROB: width is driven by config.commitWidth -/
def mkROBFromConfig (config : Shoumei.RISCV.CPUConfig) : Circuit :=
  mkROB16 config.commitWidth

end Shoumei.RISCV.Retirement


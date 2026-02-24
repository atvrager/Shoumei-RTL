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
def mkROB16 (_width : Nat := 2) : Circuit :=
  -- === W=2: Dual-alloc, dual-commit ROB ===
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
  let ne_t1 := Wire.mk "ne_t1"; let ne_t2 := Wire.mk "ne_t2"; let ne_t3 := Wire.mk "ne_t3"
  let count_safe_gates := [
    Gate.mkOR count[0]! count[1]! ne_t1,
    Gate.mkOR ne_t1 count[2]! ne_t2,
    Gate.mkOR ne_t2 count[3]! ne_t3,
    Gate.mkOR ne_t3 count[4]! not_empty_w,
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

  -- === Head/Tail Pointer + Counter: DFF-based dual-increment ===
  -- Helper: 4-bit ripple-carry adder (a + b, cin=0), returns (sum_wires, gates)
  -- b is padded to 4 bits with zero for bits >= b.length
  let mkAdd4 (pfx : String) (a b : List Wire) : List Wire × List Gate :=
    let carry := (List.range 5).map (fun i => Wire.mk s!"{pfx}_c_{i}")
    let xor_w := (List.range 4).map (fun i => Wire.mk s!"{pfx}_x_{i}")
    let sum_w := (List.range 4).map (fun i => Wire.mk s!"{pfx}_s_{i}")
    let and1  := (List.range 4).map (fun i => Wire.mk s!"{pfx}_a1_{i}")
    let and2  := (List.range 4).map (fun i => Wire.mk s!"{pfx}_a2_{i}")
    let b_ext := (List.range 4).map (fun i => if i < b.length then b[i]! else zero)
    let gates := [Gate.mkBUF zero carry[0]!] ++
      (List.range 4).flatMap (fun i => [
        Gate.mkXOR a[i]! b_ext[i]! xor_w[i]!,
        Gate.mkXOR xor_w[i]! carry[i]! sum_w[i]!,
        Gate.mkAND a[i]! b_ext[i]! and1[i]!,
        Gate.mkAND xor_w[i]! carry[i]! and2[i]!,
        Gate.mkOR and1[i]! and2[i]! carry[i+1]!
      ])
    (sum_w, gates)

  -- Tail pointer: 4-bit DFF register, increments by alloc_en_0 + alloc_en_1
  let tail_inc_lo := Wire.mk "tail_inc_lo"
  let tail_inc_hi := Wire.mk "tail_inc_hi"
  let tail_inc_gates := [
    Gate.mkXOR alloc_en_0 alloc_en_1 tail_inc_lo,
    Gate.mkAND alloc_en_0 alloc_en_1 tail_inc_hi
  ]
  let (tail_next, tail_add_gates) := mkAdd4 "ta" tail_ptr [tail_inc_lo, tail_inc_hi]
  let tail_dff_gates := (List.range 4).map (fun i =>
    Gate.mk .DFF [tail_next[i]!, clock, reset] tail_ptr[i]!)

  -- Head pointer: 4-bit DFF register, increments by commit_en_0_safe + commit_en_1_safe
  let head_inc_lo := Wire.mk "head_inc_lo"
  let head_inc_hi := Wire.mk "head_inc_hi"
  let head_inc_gates := [
    Gate.mkXOR commit_en_0_safe commit_en_1_safe head_inc_lo,
    Gate.mkAND commit_en_0_safe commit_en_1_safe head_inc_hi
  ]
  let (head_next, head_add_gates) := mkAdd4 "ha" head_ptr [head_inc_lo, head_inc_hi]
  let head_dff_gates := (List.range 4).map (fun i =>
    Gate.mk .DFF [head_next[i]!, clock, reset] head_ptr[i]!)

  -- Count: 5-bit DFF register, count_next = count + alloc_sum - commit_sum
  -- alloc_sum = {alloc_inc_hi, alloc_inc_lo} = alloc_en_0 + alloc_en_1
  -- commit_sum = {commit_inc_hi, commit_inc_lo} = commit_en_0_safe + commit_en_1_safe
  -- Use: count + alloc_sum + NOT(commit_sum) + 1 = count + alloc_sum - commit_sum
  -- Step 1: temp = count + {0,0,0,alloc_inc_hi,alloc_inc_lo} with cin=0
  let cnt_carry1 := (List.range 6).map (fun i => Wire.mk s!"cc1_{i}")
  let cnt_xor1   := (List.range 5).map (fun i => Wire.mk s!"cx1_{i}")
  let cnt_sum1   := (List.range 5).map (fun i => Wire.mk s!"cs1_{i}")
  let cnt_and1a  := (List.range 5).map (fun i => Wire.mk s!"ca1a_{i}")
  let cnt_and1b  := (List.range 5).map (fun i => Wire.mk s!"ca1b_{i}")
  let alloc_b    := [tail_inc_lo, tail_inc_hi, zero, zero, zero]
  let cnt_add1_gates := [Gate.mkBUF zero cnt_carry1[0]!] ++
    (List.range 5).flatMap (fun i => [
      Gate.mkXOR count[i]! alloc_b[i]! cnt_xor1[i]!,
      Gate.mkXOR cnt_xor1[i]! cnt_carry1[i]! cnt_sum1[i]!,
      Gate.mkAND count[i]! alloc_b[i]! cnt_and1a[i]!,
      Gate.mkAND cnt_xor1[i]! cnt_carry1[i]! cnt_and1b[i]!,
      Gate.mkOR cnt_and1a[i]! cnt_and1b[i]! cnt_carry1[i+1]!
    ])
  -- Step 2: count_next = temp + NOT({1,1,1,commit_inc_hi,commit_inc_lo}) + 1
  -- = temp - {0,0,0,commit_inc_hi,commit_inc_lo}
  -- NOT of commit_sum 5-bit: {NOT(1),NOT(1),NOT(1),NOT(chi),NOT(clo)} but commit_sum is
  -- {0,0,0,chi,clo} so NOT = {1,1,1,NOT(chi),NOT(clo)}
  let not_clo := Wire.mk "not_clo"
  let not_chi := Wire.mk "not_chi"
  let cnt_inv_gates := [
    Gate.mkNOT head_inc_lo not_clo,
    Gate.mkNOT head_inc_hi not_chi
  ]
  let commit_neg := [not_clo, not_chi, one, one, one]  -- NOT(commit_sum_5bit)
  let cnt_carry2 := (List.range 6).map (fun i => Wire.mk s!"cc2_{i}")
  let cnt_xor2   := (List.range 5).map (fun i => Wire.mk s!"cx2_{i}")
  let count_next := (List.range 5).map (fun i => Wire.mk s!"count_next_{i}")
  let cnt_and2a  := (List.range 5).map (fun i => Wire.mk s!"ca2a_{i}")
  let cnt_and2b  := (List.range 5).map (fun i => Wire.mk s!"ca2b_{i}")
  let cnt_add2_gates := [Gate.mkBUF one cnt_carry2[0]!] ++  -- cin=1 for two's complement
    (List.range 5).flatMap (fun i => [
      Gate.mkXOR cnt_sum1[i]! commit_neg[i]! cnt_xor2[i]!,
      Gate.mkXOR cnt_xor2[i]! cnt_carry2[i]! count_next[i]!,
      Gate.mkAND cnt_sum1[i]! commit_neg[i]! cnt_and2a[i]!,
      Gate.mkAND cnt_xor2[i]! cnt_carry2[i]! cnt_and2b[i]!,
      Gate.mkOR cnt_and2a[i]! cnt_and2b[i]! cnt_carry2[i+1]!
    ])
  let count_dff_gates := (List.range 5).map (fun i =>
    Gate.mk .DFF [count_next[i]!, clock, reset] count[i]!)

  -- Head/Tail index outputs
  let head_idx_0 := mkWires2 "head_idx_0" 4
  let head_idx_1 := mkWires2 "head_idx_1" 4
  let head_idx_gates :=
    List.zipWith Gate.mkBUF head_ptr  head_idx_0 ++
    List.zipWith Gate.mkBUF head1_ptr head_idx_1

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
    all_entry_gates2 ++ ro0 ++ ro1 ++ head_idx_gates ++
    tail_inc_gates ++ tail_add_gates ++ tail_dff_gates ++
    head_inc_gates ++ head_add_gates ++ head_dff_gates ++
    cnt_add1_gates ++ cnt_inv_gates ++ cnt_add2_gates ++ count_dff_gates

  let all_instances2 :=
    [alloc_dec_0_inst, alloc_dec_1_inst, commit_dec_0_inst, commit_dec_1_inst] ++
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


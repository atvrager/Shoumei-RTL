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
    isBranch := false, branchMispredicted := false
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
    (archRd : Fin 32) (isBranch : Bool)
    : ROBState × Option (Fin 16) :=
  if h : rob.count >= 16 then
    (rob, none)
  else
    let newEntry : ROBEntry := {
      valid := true
      complete := false
      physRd := physRd
      hasPhysRd := hasPhysRd
      oldPhysRd := oldPhysRd
      hasOldPhysRd := hasOldPhysRd
      archRd := archRd
      exception := false
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
    if e.valid && !e.complete && e.hasPhysRd && e.physRd == cdb_tag then
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
def mkROB16 : Circuit :=
  -- Local alias to resolve namespace ambiguity (both Combinational and Sequential are open)
  let mkWires := @Shoumei.Circuits.Combinational.makeIndexedWires
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

  -- === Commit/Flush Interface ===
  let commit_en := Wire.mk "commit_en"
  let flush_en := Wire.mk "flush_en"

  -- === Status Outputs ===
  let full := Wire.mk "full"
  let empty := Wire.mk "empty"

  -- === Allocation Result ===
  let alloc_idx := mkWires "alloc_idx" 4

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

  -- Alloc index output: BUF tail_ptr to alloc_idx
  let alloc_idx_gates := List.zipWith (fun src dst =>
    Gate.mkBUF src dst
  ) tail_ptr alloc_idx

  -- === Infrastructure Instances ===

  let head_inst : CircuitInstance := {
    moduleName := "QueuePointer_4"
    instName := "u_head"
    portMap :=
      [("clock", clock), ("reset", reset), ("en", commit_en),
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
       ("dec", commit_en), ("one", one), ("zero", zero)] ++
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

    -- Control: CDB write enable = valid AND NOT(complete) AND hasPhysRd AND match AND cdb_valid
    let complete_n := Wire.mk s!"e{i}_complete_n"
    let cdb_tmp1 := Wire.mk s!"e{i}_cdb_tmp1"
    let cdb_tmp2 := Wire.mk s!"e{i}_cdb_tmp2"
    let cdb_tmp3 := Wire.mk s!"e{i}_cdb_tmp3"
    let cdb_we := Wire.mk s!"e{i}_cdb_we"
    let cdb_we_gates := [
      Gate.mkNOT cur_complete complete_n,
      Gate.mkAND cur_valid complete_n cdb_tmp1,
      Gate.mkAND cdb_tmp1 cur_hasPhysRd cdb_tmp2,
      Gate.mkAND cdb_tmp2 cdb_match cdb_tmp3,
      Gate.mkAND cdb_tmp3 cdb_valid cdb_we
    ]

    -- Control: commit clear = AND(commit_en, commit_decode[i])
    let commit_clear := Wire.mk s!"e{i}_commit_clear"
    let commit_clear_gate := Gate.mkAND commit_en commit_decode[i]! commit_clear

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
        [("clock", clock), ("reset", reset)] ++
        (e_cur.enum.map (fun ⟨j, w⟩ => (s!"q_{j}", w)))
    }

    -- === Next-State Logic ===

    -- valid_next: MUX priority: clear > alloc > hold
    -- sel=0:hold, sel=1:set → MUX(hold, set, condition)
    let valid_mux1 := Wire.mk s!"e{i}_valid_mux1"
    let valid_gates := [
      Gate.mkMUX cur_valid one alloc_we valid_mux1,    -- alloc sets valid
      Gate.mkMUX valid_mux1 zero clear e_next[0]!      -- clear clears valid
    ]

    -- complete_next: MUX priority: clear > cdb > alloc > hold
    let comp_mux1 := Wire.mk s!"e{i}_comp_mux1"
    let comp_mux2 := Wire.mk s!"e{i}_comp_mux2"
    let complete_gates := [
      Gate.mkMUX cur_complete zero alloc_we comp_mux1,  -- alloc resets complete
      Gate.mkMUX comp_mux1 one cdb_we comp_mux2,       -- CDB sets complete
      Gate.mkMUX comp_mux2 zero clear e_next[1]!        -- clear clears complete
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

    -- exception_next: MUX priority: clear > cdb > alloc > hold
    let exc_mux1 := Wire.mk s!"e{i}_exc_mux1"
    let exc_mux2 := Wire.mk s!"e{i}_exc_mux2"
    let exception_gates := [
      Gate.mkMUX cur_exception zero alloc_we exc_mux1,
      Gate.mkMUX exc_mux1 cdb_exception cdb_we exc_mux2,
      Gate.mkMUX exc_mux2 zero clear e_next[21]!
    ]

    -- isBranch_next: only changes on alloc
    let isBranch_gate :=
      Gate.mkMUX cur_isBranch alloc_isBranch alloc_we e_next[22]!

    -- branchMispredicted_next: MUX priority: clear > cdb > alloc > hold
    let mis_mux1 := Wire.mk s!"e{i}_mis_mux1"
    let mis_mux2 := Wire.mk s!"e{i}_mis_mux2"
    let mispred_gates := [
      Gate.mkMUX cur_mispred zero alloc_we mis_mux1,
      Gate.mkMUX mis_mux1 cdb_mispredicted cdb_we mis_mux2,
      Gate.mkMUX mis_mux2 zero clear e_next[23]!
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
        (List.range 6).map (fun j => (s!"in{i}_b{j}", e[2+j]!))
      )).flatten ++
      (head_ptr.enum.map (fun ⟨k, w⟩ => (s!"sel_{k}", w))) ++
      (head_physRd.enum.map (fun ⟨j, w⟩ => (s!"out_{j}", w)))
  }

  -- MuxTree 16 6 for oldPhysRd readout
  let oldPhysRd_mux_inst : CircuitInstance := {
    moduleName := "Mux16x6"
    instName := "u_mux_oldphysrd"
    portMap :=
      ((List.range 16).map (fun i =>
        let e := all_entry_cur[i]!
        (List.range 6).map (fun j => (s!"in{i}_b{j}", e[9+j]!))
      )).flatten ++
      (head_ptr.enum.map (fun ⟨k, w⟩ => (s!"sel_{k}", w))) ++
      (head_oldPhysRd.enum.map (fun ⟨j, w⟩ => (s!"out_{j}", w)))
  }

  -- MuxTree 16 5 for archRd readout
  let archRd_mux_inst : CircuitInstance := {
    moduleName := "Mux16x5"
    instName := "u_mux_archrd"
    portMap :=
      ((List.range 16).map (fun i =>
        let e := all_entry_cur[i]!
        (List.range 5).map (fun j => (s!"in{i}_b{j}", e[16+j]!))
      )).flatten ++
      (head_ptr.enum.map (fun ⟨k, w⟩ => (s!"sel_{k}", w))) ++
      (head_archRd.enum.map (fun ⟨j, w⟩ => (s!"out_{j}", w)))
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
    [cdb_valid] ++ cdb_tag ++ [cdb_exception, cdb_mispredicted] ++
    [commit_en, flush_en]

  let all_outputs :=
    [full, empty] ++ alloc_idx ++
    [head_valid, head_complete] ++ head_physRd ++ [head_hasPhysRd] ++
    head_oldPhysRd ++ [head_hasOldPhysRd] ++ head_archRd ++
    [head_exception, head_isBranch, head_mispredicted]

  let all_gates :=
    global_gates ++ [full_gate] ++ empty_gates ++ alloc_idx_gates ++
    all_entry_gates ++ head_readout_gates

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
      { name := "head_physRd", width := 6, wires := head_physRd },
      { name := "head_oldPhysRd", width := 6, wires := head_oldPhysRd },
      { name := "head_archRd", width := 5, wires := head_archRd }
    ]
  }

end Shoumei.RISCV.Retirement

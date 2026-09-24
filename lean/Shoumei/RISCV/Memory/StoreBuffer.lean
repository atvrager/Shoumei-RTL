/-
RISCV/Memory/StoreBuffer.lean - Store Buffer with Forwarding (FIFO redesign)

8-entry circular buffer for pending store operations.
Store-to-load forwarding with youngest-match priority.
Behavioral model + structural circuit (StoreBuffer8).

Architecture: Split Valid/Committed Bitmaps + QueueRAM
- QueueRAM_8x66 stores payload (32b addr + 32b data + 2b size)
- Valid bitmap: 8 DFlipFlops. Set on enqueue, cleared on dequeue.
- Committed bitmap: 8 DFlipFlops. Cleared on enqueue, set by commit.
- On flush: valid[i] = valid[i] AND committed[i] (clear uncommitted)
- Tail pointer and count reloaded via Popcount8 on flush.

Entry lifecycle:
1. ENQUEUE: Dispatch allocates store at tail (valid=1, committed=0)
2. COMMITTED: ROB commits store → committed flag set via commit_idx
3. DEQUEUE: Committed head store written to memory via Decoupled port
4. FLUSH: Pipeline misprediction → clear uncommitted entries, reload tail/count

Forwarding:
- Loads check all valid entries for address match
- Youngest matching entry (closest to tail) wins
- Barrel rotation + PriorityArbiter8 for youngest-match selection
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.Register
import Shoumei.Circuits.Sequential.QueueComponents
import Shoumei.Circuits.Sequential.DFF
import Shoumei.Circuits.Combinational.Comparator
import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.Arbiter
import Shoumei.Circuits.Combinational.Popcount
import Shoumei.RISCV.Config

namespace Shoumei.RISCV.Memory

open Shoumei
open Shoumei.Circuits.Sequential
open Shoumei.Circuits.Combinational

private def mkOrTree (pfx : String) (inputs : List Wire) : Wire × List Gate :=
  match inputs with
  | [] => (Wire.mk s!"{pfx}_empty", [])
  | [w] => (w, [])
  | w0 :: w1 :: rest =>
    let firstOut := Wire.mk s!"{pfx}_0"
    let firstGate := Gate.mkOR w0 w1 firstOut
    let (finalW, restGates) := rest.enum.foldl (fun (acc : Wire × List Gate) (idx, w) =>
      let out := Wire.mk s!"{pfx}_{idx + 1}"
      let g := Gate.mkOR acc.1 w out
      (out, acc.2 ++ [g])
    ) (firstOut, [])
    (finalW, [firstGate] ++ restGates)

/-! ## Store Buffer Entry -/

/-- A single store buffer entry (130 bits in structural circuit).

    Bit layout:
    | Bit(s) | Width | Field     |
    |--------|-------|-----------|
    | 0-63   | 64    | address   |
    | 64-127 | 64    | data      |
    | 128-129| 2     | size      |
-/
structure StoreBufferEntry where
  /-- Entry occupied -/
  valid : Bool
  /-- ROB has committed this store -/
  committed : Bool
  /-- STA complete: effective address latched (decoupled micro-op) -/
  stA_done : Bool
  /-- STD complete: data + size latched (decoupled micro-op) -/
  stD_done : Bool
  /-- Memory address -/
  address : UInt64
  /-- Store data -/
  data : UInt64
  /-- Access size: 0=byte, 1=half, 2=word, 3=double -/
  size : Fin 4
  deriving Repr, BEq, DecidableEq

instance : Inhabited StoreBufferEntry where
  default := { valid := false, committed := false, stA_done := false, stD_done := false,
               address := 0, data := 0, size := 0 }

/-- Create an empty store buffer entry. -/
def StoreBufferEntry.empty : StoreBufferEntry := default

/-- Entry is forwardable: valid and both STA and STD micro-ops done. -/
def StoreBufferEntry.forwardable (e : StoreBufferEntry) : Bool :=
  e.valid && e.stA_done && e.stD_done

/-! ## Store Buffer State -/

/-- Store Buffer State: 8-entry circular buffer. -/
structure StoreBufferState where
  /-- 8-entry storage -/
  entries : Fin 8 → StoreBufferEntry
  /-- Head pointer: next entry to dequeue (oldest committed) -/
  head : Fin 8
  /-- Tail pointer: next entry to allocate -/
  tail : Fin 8
  /-- Current entry count -/
  count : Nat
  /-- Invariant: count never exceeds capacity -/
  h_count : count ≤ 8

/-- Create an empty store buffer. -/
def StoreBufferState.empty : StoreBufferState :=
  { entries := fun _ => StoreBufferEntry.empty
    head := 0
    tail := 0
    count := 0
    h_count := by omega
  }

/-! ## Helper Functions -/

/-- Check if store buffer is empty. -/
def StoreBufferState.isEmpty (sb : StoreBufferState) : Bool :=
  sb.count == 0

/-- Check if store buffer is full. -/
def StoreBufferState.isFull (sb : StoreBufferState) : Bool :=
  sb.count >= 8

/-- Get current count. -/
def StoreBufferState.getCount (sb : StoreBufferState) : Nat :=
  sb.count

/-- Advance a 3-bit pointer (wraps at 8). -/
private def advancePointer (ptr : Fin 8) : Fin 8 :=
  ⟨(ptr.val + 1) % 8, by omega⟩

/-! ## Core Operations -/

/-- Enqueue a new store at the tail (combined STA+STD: both done).

    Returns (updated state, allocated index) or (unchanged, none) if full.
-/
def StoreBufferState.enqueue
    (sb : StoreBufferState)
    (address : UInt64) (data : UInt64) (size : Fin 4)
    : StoreBufferState × Option (Fin 8) :=
  if h : sb.count >= 8 then (sb, none)
  else
    let newEntry : StoreBufferEntry := {
      valid := true
      committed := false  -- Speculative until ROB commits (redirect-from-commit)
      stA_done := true
      stD_done := true
      address := address
      data := data
      size := size
    }
    let allocIdx := sb.tail
    let newEntries := fun i =>
      if i == sb.tail then newEntry else sb.entries i
    ({ entries := newEntries
       head := sb.head
       tail := advancePointer sb.tail
       count := sb.count + 1
       h_count := by omega },
     some allocIdx)

/-- Allocate an SQ slot at the tail for a decoupled STA micro-op.
    The address lands in the slot only when the AGU result arrives
    (setStoreAddress); data lands later via STD (setStoreData).
-/
def StoreBufferState.enqueueSta
    (sb : StoreBufferState)
    : StoreBufferState × Option (Fin 8) :=
  sb.enqueue 0 0 0

/-- Complete the STA half of a decoupled entry: latch the effective address. -/
def StoreBufferState.setStoreAddress
    (sb : StoreBufferState) (idx : Fin 8) (address : UInt64)
    : StoreBufferState :=
  let e := sb.entries idx
  if !e.valid then sb
  else
    { sb with
      entries := fun i =>
        if i == idx then { e with address := address, stA_done := true } else sb.entries i }

/-- Complete the STD half of a decoupled entry: latch data and size. -/
def StoreBufferState.setStoreData
    (sb : StoreBufferState) (idx : Fin 8) (data : UInt64) (size : Fin 4)
    : StoreBufferState :=
  let e := sb.entries idx
  if !e.valid then sb
  else
    { sb with
      entries := fun i =>
        if i == idx then { e with data := data, size := size, stD_done := true } else sb.entries i }

/-- Circular age of an index: distance from head (0 = head/oldest). -/
def StoreBufferState.age (sb : StoreBufferState) (i : Fin 8) : Nat :=
  (i.val + 8 - sb.head.val) % 8

/-- Explicit age masking: `i` is older than `j` iff i is closer to the head
    in circular order.  Strict total order on live entries (Section 5.2). -/
def StoreBufferState.older (sb : StoreBufferState) (i j : Fin 8) : Bool :=
  sb.age i < sb.age j

/-- Youngest live entry index for an address: nearest to the tail among
    forwardable entries whose address matches.  None when no match. -/
def StoreBufferState.youngestMatchIdx (sb : StoreBufferState) (addr : UInt64)
    : Option (Fin 8) :=
  let results := (List.range 8).filterMap (fun j =>
    if h : j < 8 then
      let idx : Fin 8 := ⟨(sb.tail.val + 7 - j) % 8, by omega⟩
      let e := sb.entries idx
      if e.forwardable && e.address == addr then some idx else none
    else none
  )
  results.head?

/-- Mark an entry as committed (ROB has retired the store instruction). -/
def StoreBufferState.markCommitted (sb : StoreBufferState) (idx : Fin 8)
    : StoreBufferState :=
  let e := sb.entries idx
  if !e.valid then sb
  else
    let newEntries := fun i =>
      if i == idx then { e with committed := true } else sb.entries i
    { sb with entries := newEntries }

/-- Dequeue the head entry (send committed store to memory).

    Precondition: head entry is valid and committed.
    Returns (updated state, dequeued entry) or (unchanged, none).

    In the structural circuit, dequeue occurs on the Decoupled fire signal:
    deq_fire = deq_valid AND deq_ready
-/
def StoreBufferState.dequeue (sb : StoreBufferState)
    : StoreBufferState × Option StoreBufferEntry :=
  if sb.isEmpty then (sb, none)
  else
    let headEntry := sb.entries sb.head
    if !headEntry.valid || !headEntry.committed then (sb, none)
    else
      let newEntries := fun i =>
        if i == sb.head then StoreBufferEntry.empty else sb.entries i
      ({ entries := newEntries
         head := advancePointer sb.head
         tail := sb.tail
         count := sb.count - 1
         h_count := by have := sb.h_count; omega },
       some headEntry)

/-- Forward check: find youngest matching store entry.

    Returns the data from the youngest valid entry whose address matches.
    "Youngest" = closest to tail in circular buffer order.

    In the structural circuit, this is implemented with:
    - 8× Comparator32 for parallel address matching
    - Barrel rotation + PriorityArbiter8 for youngest-match priority
    - Mux8x32 for data selection
-/
def StoreBufferState.forwardCheck (sb : StoreBufferState) (addr : UInt64)
    : Option UInt64 :=
  -- Scan entries from youngest (tail-1) to oldest (head)
  let results := (List.range 8).filterMap fun j =>
    if h : j < 8 then
      let idx : Fin 8 := ⟨(sb.tail.val + 7 - j) % 8, by omega⟩
      let e := sb.entries idx
      if e.forwardable && e.address == addr then some e.data
      else if e.forwardable && e.size == 3 && e.address + 4 == addr then some (e.data >>> 32)
      else none
    else none
  -- Return youngest match (first in scan order)
  results.head?

/-- Forwarding probe: exact-match classification (M2 forwarding decision).
    Returns (data, isExact); partial overlap must assert replay_needed. -/
def StoreBufferState.forwardProbe (sb : StoreBufferState) (addr : UInt64)
    : Option (UInt64 × Bool) :=
  match sb.youngestMatchIdx addr with
  | some i =>
      let e := sb.entries i
      some (e.data, e.address == addr)
  | none => none

/-- Replay condition: an entry overlaps the load's 32-bit word without an
    exact byte match (multi-byte alignment collision).  The LSU must replay
    or stall; no iterative byte merger sits in the forwarding path. -/
def StoreBufferState.replayNeeded (sb : StoreBufferState) (addr : UInt64) : Bool :=
  (List.range 8).any (fun j =>
    if h : j < 8 then
      let idx : Fin 8 := ⟨(sb.tail.val + 7 - j) % 8, by omega⟩
      let e := sb.entries idx
      e.forwardable && (e.address != addr) && (e.address >>> 2) == (addr >>> 2)
    else false)

/-- Full flush: clear ALL entries.

    The pipeline controller must drain committed stores before flushing.
    In the structural circuit, flush_en OR'd with reset clears all registers.
-/
def StoreBufferState.fullFlush (_sb : StoreBufferState) : StoreBufferState :=
  StoreBufferState.empty

/-! ## Query Helpers -/

/-- Read the head entry. -/
def StoreBufferState.headEntry (sb : StoreBufferState) : StoreBufferEntry :=
  sb.entries sb.head

/-- Check if head is ready to dequeue (valid and committed). -/
def StoreBufferState.headReady (sb : StoreBufferState) : Bool :=
  !sb.isEmpty && (sb.entries sb.head).valid && (sb.entries sb.head).committed

/-! ## Structural Circuit -/

/-- Build StoreBuffer8 structural circuit: 8-entry store buffer with forwarding.

    **Architecture (FIFO redesign):**
    - QueueRAM_8x66 for payload storage (32b addr + 32b data + 2b size)
    - 8× DFlipFlop valid bitmap (set on enq, cleared on deq)
    - 8× DFlipFlop committed bitmap (cleared on enq, set by commit)
    - Loadable head/tail pointers (QueuePointerLoadable_3)
    - Loadable count (QueueCounterLoadable_4)
    - Popcount8 for flush recovery (count surviving committed entries)
    - Address matching via 8 parallel Comparator32 instances
    - Youngest-match forwarding: barrel rotation + PriorityArbiter8
    - Dequeue readout via Mux8x32 (address, data) + Mux8x2 (size)
    - Decoupled dequeue: deq_valid/deq_ready handshaking

    **Payload layout in QueueRAM (66 bits):**
    | Bit(s)  | Width | Field     |
    |---------|-------|-----------|
    | 0-31    | 32    | address   |
    | 32-63   | 32    | data      |
    | 64-65   | 2     | size      |
-/
def mkStoreBuffer8 : Circuit :=
  let mkWires := @Shoumei.Circuits.Combinational.makeIndexedWires

  -- === Global Signals ===
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- Flush enable: clears uncommitted entries only (committed stores survive)
  let flush_en := Wire.mk "flush_en"

  -- === Enqueue Interface ===
  let enq_en := Wire.mk "enq_en"
  let enq_idx_in := mkWires "enq_idx_in_" 3  -- externally-provided entry index for enqueue
  let enq_address := mkWires "enq_address_" 64
  let enq_data := mkWires "enq_data_" 64
  let enq_size := mkWires "enq_size_" 2

  -- === Commit Interface ===
  let commit_en := Wire.mk "commit_en"
  -- Internal commit pointer (replaces external commit_idx)
  let commit_ptr := mkWires "commit_ptr_" 3

  -- === Dequeue Interface (Decoupled) ===
  let deq_ready := Wire.mk "deq_ready"
  let deq_valid := Wire.mk "deq_valid"
  let deq_bits := mkWires "deq_bits_" 130

  -- === Forwarding Interface ===
  let fwd_address := mkWires "fwd_address_" 64
  let fwd_hit := Wire.mk "fwd_hit"
  let fwd_data := mkWires "fwd_data_" 64

  -- === Status Outputs ===
  let full := Wire.mk "full"
  let empty := Wire.mk "empty"
  let enq_idx := mkWires "enq_idx_" 3
  let flush_tail := mkWires "flush_tail_" 3  -- combinational flush-recovered tail for CPU
  let flush_applied := Wire.mk "flush_applied"
  let flush_pending := Wire.mk "flush_pending"
  -- Replay output: partial word overlap in the forwarding set.  The LSU
  -- replays/stalls instead of byte-merging in the critical path.
  let replay_needed := Wire.mk "replay_needed"

  -- === Internal Wires ===
  let head_ptr := mkWires "head_ptr_" 3
  let tail_ptr := mkWires "tail_ptr_" 3
  let count := mkWires "count_" 4
  let enq_decode := mkWires "enq_decode_" 8
  let commit_decode := mkWires "commit_decode_" 8

  -- Valid and committed bitmaps
  let valid := (List.range 8).map (fun i => Wire.mk s!"valid_e{i}")
  let committed := (List.range 8).map (fun i => Wire.mk s!"committed_e{i}")

  -- Pending-commit counter, driven by commit_gate_gates further down.  Declared
  -- here because the flush gating below needs it.
  let pc_nz := Wire.mk "pending_commit_nz"

  -- === Flush qualification ===
  -- A commit can be owed while its entry is still being written: the ROB retires
  -- a store out of the memory pipeline register, so `committed` can lag the
  -- retire.  Flushing in that window clears an entry the ROB has already
  -- accounted for and loses the store, because `head_ptr` stays put while
  -- `count`/`tail_ptr`/`commit_ptr` are all reloaded from the survivors.
  -- Every owed commit belongs to a store that already dispatched, so its entry
  -- always appears and the commit always lands; holding the flush until the
  -- accounting drains therefore cannot wedge.  This is the "drain committed
  -- stores before flushing" requirement stated at the top of this file.
  let flush_apply := flush_applied
  let flush_pending_next := Wire.mk "flush_pending_next"
  let flush_req := Wire.mk "flush_req"
  let flush_quiescent := Wire.mk "flush_quiescent"
  let not_flush_apply := Wire.mk "not_flush_apply"
  let flush_apply_gates := [
    Gate.mkNOT pc_nz (Wire.mk "not_pc_nz"),
    Gate.mkNOT commit_en (Wire.mk "not_commit_en_for_flush"),
    Gate.mkAND (Wire.mk "not_pc_nz") (Wire.mk "not_commit_en_for_flush") flush_quiescent,
    Gate.mkOR flush_en flush_pending flush_req,
    Gate.mkAND flush_req flush_quiescent flush_apply,
    Gate.mkNOT flush_apply not_flush_apply,
    Gate.mkAND flush_req not_flush_apply flush_pending_next
  ]
  let flush_pending_inst : CircuitInstance := {
    moduleName := "DFlipFlop"
    instName := "u_flush_pending"
    portMap := [("d", flush_pending_next), ("q", flush_pending),
                ("clock", clock), ("reset", reset)]
  }
  let valid_next := (List.range 8).map (fun i => Wire.mk s!"valid_next_e{i}")
  let committed_next := (List.range 8).map (fun i => Wire.mk s!"committed_next_e{i}")

  -- === Reset Buffer Tree ===
  -- Each Register66 has 66 DFFs; raw reset drives 8×66 = 528 DFF RESETN pins.
  -- 2-level tree: 2 root buffers × 4 leaf buffers each = 8 leaves (one per entry).
  let reset_roots := (List.range 2).map (fun i => Wire.mk s!"reset_root_{i}")
  let reset_leaves := (List.range 8).map (fun i => Wire.mk s!"reset_leaf_{i}")
  let reset_buf_gates :=
    (List.range 2).map (fun i => Gate.mkBUF reset (reset_roots[i]!)) ++
    (List.range 8).map (fun i => Gate.mkBUF (reset_roots[i / 4]!) (reset_leaves[i]!))

  -- === Global Control Gates ===

  -- Full = count[3] (count ≥ 8 iff bit 3 set; count ≤ 8 by construction)
  let full_gate := Gate.mkBUF count[3]! full

  -- Empty = NOR(count[3:0])
  let empty_or1 := Wire.mk "empty_or1"
  let empty_or2 := Wire.mk "empty_or2"
  let empty_or3 := Wire.mk "empty_or3"
  let empty_gates := [
    Gate.mkOR count[0]! count[1]! empty_or1,
    Gate.mkOR empty_or1 count[2]! empty_or2,
    Gate.mkOR empty_or2 count[3]! empty_or3,
    Gate.mkNOT empty_or3 empty
  ]

  -- Enq index output: BUF tail_ptr to enq_idx
  let enq_idx_gates := List.zipWith (fun src dst =>
    Gate.mkBUF src dst
  ) tail_ptr enq_idx

  -- Dequeue fire signal: AND(deq_valid, deq_ready)
  let deq_fire := Wire.mk "deq_fire"
  let deq_fire_gate := Gate.mkAND deq_valid deq_ready deq_fire

  -- === Infrastructure Instances ===

  -- Head pointer: loadable (load not used currently, but available for future)
  let head_inst : CircuitInstance := {
    moduleName := "QueuePointer_3"
    instName := "u_head"
    portMap :=
      [("clock", clock), ("reset", reset), ("en", deq_fire),
       ("one", one), ("zero", zero)] ++
      (head_ptr.enum.map (fun ⟨i, w⟩ => (s!"count_{i}", w)))
  }

  -- Tail pointer: loadable for flush recovery
  let flush_tail_load := mkWires "flush_tail_load_" 3
  let tail_inst : CircuitInstance := {
    moduleName := "QueuePointerLoadable_3"
    instName := "u_tail"
    portMap :=
      [("clock", clock), ("reset", reset), ("en", enq_en),
       ("load_en", flush_apply), ("one", one), ("zero", zero)] ++
      (flush_tail_load.enum.map (fun ⟨i, w⟩ => (s!"load_value_{i}", w))) ++
      (tail_ptr.enum.map (fun ⟨i, w⟩ => (s!"count_{i}", w)))
  }

  -- Count: loadable for flush recovery
  let flush_count_load := mkWires "flush_count_load_" 4
  let count_inst : CircuitInstance := {
    moduleName := "QueueCounterLoadable_4"
    instName := "u_count"
    portMap :=
      [("clock", clock), ("reset", reset), ("inc", enq_en),
       ("dec", deq_fire), ("load_en", flush_apply), ("one", one), ("zero", zero)] ++
      (flush_count_load.enum.map (fun ⟨i, w⟩ => (s!"load_value_{i}", w))) ++
      (count.enum.map (fun ⟨i, w⟩ => (s!"count_{i}", w)))
  }

  -- Enqueue decode uses externally-provided index (pre-allocated at rename time)
  -- This ensures entries are allocated in program order even when dispatched out of order.
  let enq_dec_inst : CircuitInstance := {
    moduleName := "Decoder3"
    instName := "u_enq_dec"
    portMap :=
      (enq_idx_in.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (enq_decode.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  let head_decode := mkWires "head_decode_" 8
  let head_dec_inst : CircuitInstance := {
    moduleName := "Decoder3"
    instName := "u_head_dec"
    portMap :=
      (head_ptr.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (head_decode.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- Commit gate with pending counter: the ROB may commit a store before it
  -- enters the SB (stores auto-complete).  A 3-bit counter buffers missed
  -- commits so they're applied when the target entry becomes valid.
  let commit_target_valid := Wire.mk "commit_target_valid"
  let commit_en_gated := Wire.mk "commit_en_gated"
  let ctv_bits := (List.range 8).map (fun i => Wire.mk s!"ctv_b{i}")
  let ctv_or := (List.range 4).map (fun i => Wire.mk s!"ctv_r{i}")
  let ctv_or2 := (List.range 2).map (fun i => Wire.mk s!"ctv_s{i}")

  -- Pending commit counter (3-bit): tracks commits that arrived before SB entry
  let pc := (List.range 3).map (fun i => Wire.mk s!"pending_commit_{i}")
  let pc_next := (List.range 3).map (fun i => Wire.mk s!"pending_commit_next_{i}")
  let pc_inc := Wire.mk "pending_commit_inc"
  let pc_dec := Wire.mk "pending_commit_dec"

  -- Increment value (pc + 1)
  let pc_inc_val := (List.range 3).map (fun i => Wire.mk s!"pc_inc_v{i}")
  -- Decrement value (pc - 1)
  let pc_dec_val := (List.range 3).map (fun i => Wire.mk s!"pc_dec_v{i}")

  let commit_gate_gates :=
    -- AND each commit_decode bit with valid bit
    (List.range 8).map (fun i =>
      Gate.mkAND commit_decode[i]! valid[i]! ctv_bits[i]!) ++
    -- OR-reduce: 8→4→2→1
    [Gate.mkOR ctv_bits[0]! ctv_bits[1]! ctv_or[0]!,
     Gate.mkOR ctv_bits[2]! ctv_bits[3]! ctv_or[1]!,
     Gate.mkOR ctv_bits[4]! ctv_bits[5]! ctv_or[2]!,
     Gate.mkOR ctv_bits[6]! ctv_bits[7]! ctv_or[3]!,
     Gate.mkOR ctv_or[0]! ctv_or[1]! ctv_or2[0]!,
     Gate.mkOR ctv_or[2]! ctv_or[3]! ctv_or2[1]!,
     Gate.mkOR ctv_or2[0]! ctv_or2[1]! commit_target_valid,
     -- pending_commit_nz = OR(pc[0], pc[1], pc[2])
     Gate.mkOR pc[0]! pc[1]! (Wire.mk "pc_nz_t"),
     Gate.mkOR (Wire.mk "pc_nz_t") pc[2]! pc_nz,
     -- commit fires when target valid AND (new commit OR pending > 0)
     Gate.mkOR commit_en pc_nz (Wire.mk "commit_available"),
     Gate.mkAND (Wire.mk "commit_available") commit_target_valid commit_en_gated,
     -- inc = commit_en AND NOT target_valid (missed commit → buffer)
     Gate.mkNOT commit_target_valid (Wire.mk "not_ctv"),
     Gate.mkAND commit_en (Wire.mk "not_ctv") pc_inc,
     -- dec = NOT commit_en AND target_valid AND pending > 0 (drain buffered)
     Gate.mkNOT commit_en (Wire.mk "not_commit_en"),
     Gate.mkAND (Wire.mk "not_commit_en") commit_target_valid (Wire.mk "dec_tmp"),
     Gate.mkAND (Wire.mk "dec_tmp") pc_nz pc_dec,
     -- pc + 1
     Gate.mkNOT pc[0]! pc_inc_val[0]!,
     Gate.mkXOR pc[1]! pc[0]! pc_inc_val[1]!,
     Gate.mkAND pc[1]! pc[0]! (Wire.mk "pc_carry1"),
     Gate.mkXOR pc[2]! (Wire.mk "pc_carry1") pc_inc_val[2]!,
     -- pc - 1
     Gate.mkNOT pc[0]! pc_dec_val[0]!,
     Gate.mkNOT pc[0]! (Wire.mk "pc_borrow0"),
     Gate.mkXOR pc[1]! (Wire.mk "pc_borrow0") pc_dec_val[1]!,
     Gate.mkNOT pc[1]! (Wire.mk "not_pc1"),
     Gate.mkAND (Wire.mk "not_pc1") (Wire.mk "pc_borrow0") (Wire.mk "pc_borrow1"),
     Gate.mkXOR pc[2]! (Wire.mk "pc_borrow1") pc_dec_val[2]!] ++
    -- pc_next: MUX(MUX(pc, pc-1, dec), pc+1, inc)
    (List.range 3).map (fun i =>
      Gate.mkMUX pc[i]! pc_dec_val[i]! pc_dec (Wire.mk s!"pc_mux1_{i}")) ++
    (List.range 3).map (fun i =>
      Gate.mkMUX (Wire.mk s!"pc_mux1_{i}") pc_inc_val[i]! pc_inc pc_next[i]!)

  -- Internal commit pointer: increments on commit_en_gated, loads flush_tail_load on flush
  let commit_ptr_inst : CircuitInstance := {
    moduleName := "QueuePointerLoadable_3"
    instName := "u_commit_ptr"
    portMap :=
      [("clock", clock), ("reset", reset), ("en", commit_en_gated),
       ("load_en", flush_apply), ("one", one), ("zero", zero)] ++
      (flush_tail_load.enum.map (fun ⟨i, w⟩ => (s!"load_value_{i}", w))) ++
      (commit_ptr.enum.map (fun ⟨i, w⟩ => (s!"count_{i}", w)))
  }

  let commit_dec_inst : CircuitInstance := {
    moduleName := "Decoder3"
    instName := "u_commit_dec"
    portMap :=
      (commit_ptr.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (commit_decode.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- === Flush Recovery: Popcount8 + Adder ===
  -- On flush, count surviving entries = popcount(valid AND committed)
  -- New tail = head + popcount (mod 8, only low 3 bits matter)

  let surviving := (List.range 8).map (fun i => Wire.mk s!"surviving_{i}")
  -- An entry dequeued on the same cycle as the flush is gone: `head_ptr` advances
  -- past it at the clock edge, so it must not be counted as surviving either.
  -- Counting it leaves count > 0 with an empty [head, tail) range, and the buffer
  -- never reports empty again -- any drain waiting on sb_empty then wedges.
  let surviving_gates := (List.range 8).flatMap (fun i =>
    let surv_vc := Wire.mk s!"surv_vc_{i}"
    let surv_deq := Wire.mk s!"surv_deq_{i}"
    let surv_not_deq := Wire.mk s!"surv_not_deq_{i}"
    [Gate.mkAND valid[i]! committed[i]! surv_vc,
     Gate.mkAND deq_fire head_decode[i]! surv_deq,
     Gate.mkNOT surv_deq surv_not_deq,
     Gate.mkAND surv_vc surv_not_deq surviving[i]!])

  let pop_count := mkWires "pop_count_" 4
  let pop_inst : CircuitInstance := {
    moduleName := "Popcount8"
    instName := "u_popcount"
    portMap :=
      (surviving.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (pop_count.enum.map (fun ⟨i, w⟩ => (s!"count_{i}", w)))
  }

  -- flush_count_load = pop_count (surviving entry count)
  let flush_count_gates := (List.range 4).map (fun i =>
    Gate.mkBUF pop_count[i]! flush_count_load[i]!)

  -- flush_tail_load = (head_ptr + deq_fire) + pop_count[2:0] (mod 8, wrapping add)
  -- The +deq_fire is what keeps head and tail consistent: a store dequeued on the
  -- flush cycle has already advanced head_ptr at the clock edge, and it is no
  -- longer in `surviving`, so tail must be measured from the advanced head.
  let hn_xor := (List.range 3).map (fun i => Wire.mk s!"hn_xor_b{i}")
  let hn_carry := (List.range 3).map (fun i => Wire.mk s!"hn_carry_b{i}")
  let head_next := (List.range 3).map (fun i => Wire.mk s!"hn_b{i}")
  let head_next_gates := [
    Gate.mkXOR head_ptr[0]! deq_fire hn_xor[0]!,
    Gate.mkBUF hn_xor[0]! head_next[0]!,
    Gate.mkAND head_ptr[0]! deq_fire hn_carry[0]!,
    Gate.mkXOR head_ptr[1]! hn_carry[0]! hn_xor[1]!,
    Gate.mkBUF hn_xor[1]! head_next[1]!,
    Gate.mkAND head_ptr[1]! hn_carry[0]! hn_carry[1]!,
    Gate.mkXOR head_ptr[2]! hn_carry[1]! hn_xor[2]!,
    Gate.mkBUF hn_xor[2]! head_next[2]!]

  let ft_xor := (List.range 3).map (fun i => Wire.mk s!"ft_xor_b{i}")
  let ft_carry := (List.range 4).map (fun i => Wire.mk s!"ft_carry_b{i}")
  let ft_and1 := (List.range 3).map (fun i => Wire.mk s!"ft_and1_b{i}")
  let ft_and2 := (List.range 3).map (fun i => Wire.mk s!"ft_and2_b{i}")
  let flush_tail_gates := head_next_gates ++ [
    Gate.mkBUF zero ft_carry[0]!
  ] ++ ((List.range 3).map (fun i =>
    [Gate.mkXOR head_next[i]! pop_count[i]! ft_xor[i]!,
     Gate.mkXOR ft_xor[i]! ft_carry[i]! flush_tail_load[i]!,
     Gate.mkAND head_next[i]! pop_count[i]! ft_and1[i]!,
     Gate.mkAND ft_xor[i]! ft_carry[i]! ft_and2[i]!,
     Gate.mkOR ft_and1[i]! ft_and2[i]! ft_carry[i+1]!]
  )).flatten

  -- Expose combinational flush tail for CPU's sb_alloc_ctr reload
  let flush_tail_out_gates := (List.range 3).map (fun i =>
    Gate.mkBUF flush_tail_load[i]! flush_tail[i]!)

  -- === Per-Entry Valid/Committed Bitmap Logic ===

  let bitmap_gates := (List.range 8).map (fun i =>
    -- Enqueue write enable = AND(enq_en, enq_decode[i])
    let enq_we := Wire.mk s!"e{i}_enq_we"
    let enq_we_gate := Gate.mkAND enq_en enq_decode[i]! enq_we

    -- Dequeue clear enable = AND(deq_fire, head_decode[i])
    let deq_clr := Wire.mk s!"e{i}_deq_clr"
    let deq_clr_gate := Gate.mkAND deq_fire head_decode[i]! deq_clr

    -- Commit write enable = AND(commit_en_gated, commit_decode[i])
    let commit_we := Wire.mk s!"e{i}_commit_we"
    let commit_we_gate := Gate.mkAND commit_en_gated commit_decode[i]! commit_we

    -- === Valid bitmap ===
    -- valid_next: priority: deq_clr (clear) > enq (set) > flush (clear uncommitted) > hold
    -- Step 1: hold or set on enq
    let v_enq := Wire.mk s!"e{i}_v_enq"
    -- Step 2: clear on deq
    let v_deq := Wire.mk s!"e{i}_v_deq"
    let not_deq_clr := Wire.mk s!"e{i}_not_deq_clr"
    -- Step 3: flush — valid survives only if committed
    let v_flush := Wire.mk s!"e{i}_v_flush"
    let v_after_flush := Wire.mk s!"e{i}_v_after_flush"
    let not_flush := Wire.mk s!"e{i}_not_flush"
    let valid_gates := [
      Gate.mkMUX valid[i]! one enq_we v_enq,          -- enq sets valid
      Gate.mkNOT deq_clr not_deq_clr,
      Gate.mkAND v_enq not_deq_clr v_deq,             -- deq clears valid
      -- Flush: valid_next = valid AND (NOT flush OR committed)
      Gate.mkAND v_deq committed[i]! v_flush,          -- surviving = valid AND committed
      Gate.mkNOT flush_apply not_flush,
      Gate.mkMUX v_flush v_deq not_flush v_after_flush, -- flush ? surviving : normal
      Gate.mkBUF v_after_flush valid_next[i]!
    ]

    -- === Committed bitmap ===
    -- committed_next: priority: enq (clear) > commit (set) > flush (clear uncommitted) > hold
    let c_commit := Wire.mk s!"e{i}_c_commit"
    let c_enq := Wire.mk s!"e{i}_c_enq"
    let committed_gates := [
      Gate.mkMUX committed[i]! one commit_we c_commit,   -- commit sets
      Gate.mkMUX c_commit zero enq_we c_enq              -- enq clears
      -- No flush logic needed: committed bitmap is not directly cleared by flush.
      -- Valid bitmap handles the flush (uncommitted entries lose valid, so committed doesn't matter).
    ]
    let committed_next_gate := Gate.mkBUF c_enq committed_next[i]!

    ([enq_we_gate, deq_clr_gate, commit_we_gate] ++ valid_gates ++ committed_gates ++ [committed_next_gate])
  ) |>.flatten

  -- DFlipFlop instances for valid and committed bitmaps
  -- Use distinct wire names to avoid codegen bus grouping bug
  let valid_dff_insts := (List.range 8).map (fun i =>
    { moduleName := "DFlipFlop", instName := s!"u_valid_{i}",
      portMap := [("d", valid_next[i]!), ("q", valid[i]!),
                  ("clock", clock), ("reset", reset)] : CircuitInstance })

  let committed_dff_insts := (List.range 8).map (fun i =>
    { moduleName := "DFlipFlop", instName := s!"u_committed_{i}",
      portMap := [("d", committed_next[i]!), ("q", committed[i]!),
                  ("clock", clock), ("reset", reset)] : CircuitInstance })

  -- DFFs for pending commit counter (reset on global reset OR flush)
  let pc_reset := Wire.mk "pc_reset"
  let pc_reset_gate := Gate.mkOR reset flush_apply pc_reset
  let pc_dff_insts := (List.range 3).map (fun i =>
    { moduleName := "DFlipFlop", instName := s!"u_pending_commit_{i}",
      portMap := [("d", pc_next[i]!), ("q", pc[i]!),
                  ("clock", clock), ("reset", pc_reset)] : CircuitInstance })

  -- === Per-Entry Forwarding Logic ===
  -- Read all entries from QueueRAM for forwarding (parallel read ports via per-entry storage)
  -- QueueRAM only has 1 read port (for dequeue). For forwarding, we read directly from
  -- the Register instances inside the QueueRAM. But since QueueRAM is a submodule,
  -- we can't access its internals. Instead, we use 8× Comparator32 + Mux8x32 with
  -- separate read logic.
  --
  -- Actually, the QueueRAM read port is used for dequeue. For forwarding, we need
  -- parallel access to all 8 entries' addresses. The cleanest approach:
  -- use the QueueRAM's internal registers directly by reading entry data from
  -- per-entry storage. Since QueueRAM uses Register66 instances internally,
  -- and we need parallel read, we keep the per-entry read wires.
  --
  -- Alternative: Don't use QueueRAM. Use 8× Register66 directly (like the old design
  -- but without valid/committed in the register). This gives us direct parallel read.
  -- This is simpler and matches the forwarding architecture better.

  -- Per-entry storage: 8× Register130 (address[63:0] + data[63:0] + size[1:0])
  let entryResults := (List.range 8).map fun i =>
    let e_cur := mkWires s!"e{i}_" 130
    let e_next := mkWires s!"e{i}_next_" 130

    let cur_address := (List.range 64).map (fun j => e_cur[j]!)
    let cur_data := (List.range 64).map (fun j => e_cur[64+j]!)
    let cur_size := (List.range 2).map (fun j => e_cur[128+j]!)

    -- Enqueue write enable = AND(enq_en, enq_decode[i])
    let enq_we := Wire.mk s!"e{i}_enq_we"  -- already created in bitmap logic, reuse wire name

    -- address_next: only changes on enq
    let address_gates := (List.range 64).map fun j =>
      Gate.mkMUX cur_address[j]! enq_address[j]! enq_we e_next[j]!

    -- data_next: only changes on enq
    let data_gates := (List.range 64).map fun j =>
      Gate.mkMUX cur_data[j]! enq_data[j]! enq_we e_next[64+j]!

    -- size_next: only changes on enq
    let size_gates := (List.range 2).map fun j =>
      Gate.mkMUX cur_size[j]! enq_size[j]! enq_we e_next[128+j]!

    -- EqualityComparator64 instance: fwd_address vs entry address (XOR + OR-tree, no subtraction)
    let cmp_eq := Wire.mk s!"e{i}_cmp_eq"
    let cmp_inst : CircuitInstance := {
      moduleName := "EqualityComparator64"
      instName := s!"u_cmp{i}"
      portMap :=
        (fwd_address.enum.map (fun ⟨j, w⟩ => (s!"a_{j}", w))) ++
        (cur_address.enum.map (fun ⟨j, w⟩ => (s!"b_{j}", w))) ++
        [("eq", cmp_eq)]
    }

    -- Register130 instance: entry storage (uses buffered reset leaf)
    let reg_inst : CircuitInstance := {
      moduleName := "Register130"
      instName := s!"u_entry{i}"
      portMap :=
        (e_next.enum.map (fun ⟨j, w⟩ => (s!"d_{j}", w))) ++
        [("clock", clock), ("reset", reset_leaves[i]!)] ++
        (e_cur.enum.map (fun ⟨j, w⟩ => (s!"q_{j}", w)))
    }

    -- Double-precision store check: size == 2'b11
    let is_double := Wire.mk s!"e{i}_is_double"
    let is_double_gate := Gate.mkAND cur_size[0]! cur_size[1]! is_double

    -- Word-level address match: compare bits [63:2] (word-aligned address)
    -- XOR bits 2..63 (62 bits)
    let word_xor := (List.range 62).map (fun j => Wire.mk s!"e{i}_wxor_{j}")
    let word_xor_gates := (List.range 62).map (fun j =>
      Gate.mkXOR fwd_address[j+2]! cur_address[j+2]! word_xor[j]!)

    -- Reduction of 61 upper address bits (bits 3..63, i.e. word_xor[1..61])
    let upper_bits := (List.range 61).map (fun j => word_xor[j + 1]!)
    let (upper_neq, wor_gates) := mkOrTree s!"e{i}_wor" upper_bits

    let upper_eq := Wire.mk s!"e{i}_upper_eq"
    let upper_eq_gate := Gate.mkNOT upper_neq upper_eq

    -- Low word address match: upper_eq AND (fwd_address[2] == cur_address[2])
    let not_wxor0 := Wire.mk s!"e{i}_not_wxor0"
    let not_wxor0_gate := Gate.mkNOT word_xor[0]! not_wxor0
    let word_eq := Wire.mk s!"e{i}_word_eq"
    let word_eq_gate := Gate.mkAND upper_eq not_wxor0 word_eq

    -- High word address match: upper_eq AND fwd_address[2] AND NOT(cur_address[2])
    let not_cur_addr2 := Wire.mk s!"e{i}_not_cur_addr2"
    let not_cur_addr2_gate := Gate.mkNOT cur_address[2]! not_cur_addr2
    let fwd2_and_not_cur2 := Wire.mk s!"e{i}_fwd2_not_cur2"
    let fwd2_and_not_cur2_gate := Gate.mkAND fwd_address[2]! not_cur_addr2 fwd2_and_not_cur2
    let hi_word_addr_match := Wire.mk s!"e{i}_hi_word_addr_match"
    let hi_word_addr_match_gate := Gate.mkAND upper_eq fwd2_and_not_cur2 hi_word_addr_match

    -- Compare bits 1:0 for exact match in high word
    let lo2_xor0 := Wire.mk s!"e{i}_lo2_xor0"
    let lo2_xor1 := Wire.mk s!"e{i}_lo2_xor1"
    let lo2_or := Wire.mk s!"e{i}_lo2_or"
    let lo2_eq := Wire.mk s!"e{i}_lo2_eq"
    let lo2_gates := [
      Gate.mkXOR fwd_address[0]! cur_address[0]! lo2_xor0,
      Gate.mkXOR fwd_address[1]! cur_address[1]! lo2_xor1,
      Gate.mkOR lo2_xor0 lo2_xor1 lo2_or,
      Gate.mkNOT lo2_or lo2_eq
    ]

    -- High word exact match: hi_word_addr_match AND lo2_eq
    let hi_word_eq := Wire.mk s!"e{i}_hi_word_eq"
    let hi_word_eq_gate := Gate.mkAND hi_word_addr_match lo2_eq hi_word_eq

    -- match_hi_word: is_double AND hi_word_eq
    let match_hi_word := Wire.mk s!"e{i}_match_hi_word"
    let match_hi_word_gate := Gate.mkAND is_double hi_word_eq match_hi_word

    -- Forwarding match: valid AND (cmp_eq OR match_hi_word)
    let match_any := Wire.mk s!"e{i}_match_any"
    let match_any_gate := Gate.mkOR cmp_eq match_hi_word match_any
    let fwd_match := Wire.mk s!"e{i}_fwd_match"
    let fwd_match_gate := Gate.mkAND valid[i]! match_any fwd_match

    -- Committed forwarding match: valid AND committed AND match_any
    let fwd_committed_match := Wire.mk s!"e{i}_fwd_committed_match"
    let fwd_committed_match_gate := Gate.mkAND fwd_match committed[i]! fwd_committed_match

    -- Word matches:
    let lo_word_match := Wire.mk s!"e{i}_lo_word_match"
    let lo_word_match_gate := Gate.mkAND valid[i]! word_eq lo_word_match

    let hi_word_valid := Wire.mk s!"e{i}_hi_word_valid"
    let hi_word_valid_gate := Gate.mkAND valid[i]! hi_word_addr_match hi_word_valid
    let hi_word_double_valid := Wire.mk s!"e{i}_hi_word_double_valid"
    let hi_word_double_valid_gate := Gate.mkAND hi_word_valid is_double hi_word_double_valid

    let word_match := Wire.mk s!"e{i}_word_match"
    let word_match_gate := Gate.mkOR lo_word_match hi_word_double_valid word_match

    -- Word-only matches (sub-word access stalling):
    let not_cmp_eq := Wire.mk s!"e{i}_not_cmp_eq"
    let not_cmp_eq_gate := Gate.mkNOT cmp_eq not_cmp_eq
    let lo_word_only_match := Wire.mk s!"e{i}_lo_word_only_match"
    let lo_word_only_gate := Gate.mkAND lo_word_match not_cmp_eq lo_word_only_match

    let hi_word_only_match := Wire.mk s!"e{i}_hi_word_only_match"
    let hi_word_only_gate := Gate.mkAND hi_word_double_valid lo2_or hi_word_only_match

    let word_only_match := Wire.mk s!"e{i}_word_only_match"
    let word_only_match_gate := Gate.mkOR lo_word_only_match hi_word_only_match word_only_match

    -- Forwarding data: on match_hi_word, bits [31:0] get cur_data[63:32]
    let entry_fwd_data := mkWires s!"e{i}_fwd_data_" 64
    let fwd_data_mux_gates :=
      (List.range 32).map (fun j =>
        Gate.mkMUX cur_data[j]! cur_data[32+j]! match_hi_word entry_fwd_data[j]!) ++
      (List.range 32).map (fun j =>
        Gate.mkBUF cur_data[32+j]! entry_fwd_data[32+j]!)

    -- Forwarding size: on match_hi_word, size becomes word (2'b10)
    let not_match_hi_word := Wire.mk s!"e{i}_not_match_hi_word"
    let not_match_hi_word_gate := Gate.mkNOT match_hi_word not_match_hi_word
    let entry_size := mkWires s!"e{i}_fwd_sz_" 2
    let fwd_size_gates := [
      Gate.mkAND cur_size[0]! not_match_hi_word entry_size[0]!,
      Gate.mkBUF cur_size[1]! entry_size[1]!
    ]

    let word_match_gates :=
      [is_double_gate] ++ word_xor_gates ++
      wor_gates ++
      [upper_eq_gate,
       not_wxor0_gate, word_eq_gate,
       not_cur_addr2_gate, fwd2_and_not_cur2_gate, hi_word_addr_match_gate] ++
      lo2_gates ++
      [hi_word_eq_gate, match_hi_word_gate,
       match_any_gate, fwd_match_gate, fwd_committed_match_gate,
       lo_word_match_gate, hi_word_valid_gate, hi_word_double_valid_gate, word_match_gate,
       not_cmp_eq_gate, lo_word_only_gate, hi_word_only_gate, word_only_match_gate,
       not_match_hi_word_gate] ++
      fwd_data_mux_gates ++ fwd_size_gates

    let entry_gates := address_gates ++ data_gates ++ size_gates ++ word_match_gates

    (entry_gates, [cmp_inst, reg_inst], e_cur, fwd_match, fwd_committed_match, entry_fwd_data, entry_size, word_match, word_only_match)

  -- Flatten per-entry results
  let all_entry_gates := (entryResults.map (fun (g, _, _, _, _, _, _, _, _) => g)).flatten
  let all_entry_instances := (entryResults.map (fun (_, insts, _, _, _, _, _, _, _) => insts)).flatten
  let all_entry_cur := entryResults.map (fun (_, _, cur, _, _, _, _, _, _) => cur)
  let fwd_matches := entryResults.map (fun (_, _, _, m, _, _, _, _, _) => m)
  let fwd_committed_matches := entryResults.map (fun (_, _, _, _, cm, _, _, _, _) => cm)
  let all_entry_data := entryResults.map (fun (_, _, _, _, _, d, _, _, _) => d)
  let all_entry_size := entryResults.map (fun (_, _, _, _, _, _, sz, _, _) => sz)
  let word_matches := entryResults.map (fun (_, _, _, _, _, _, _, wm, _) => wm)
  let word_only_matches := entryResults.map (fun (_, _, _, _, _, _, _, _, wom) => wom)

  -- === Forwarding Logic: Youngest-Match via Barrel Rotation ===

  -- Step 1: Barrel rotate match vector so youngest entry maps to position 0.
  let barrel_l0 := mkWires "barrel_l0_" 8
  let barrel_l0_gates := (List.range 8).map fun i =>
    Gate.mkMUX fwd_matches[i]! fwd_matches[(i+1) % 8]! tail_ptr[0]! barrel_l0[i]!

  let barrel_l1 := mkWires "barrel_l1_" 8
  let barrel_l1_gates := (List.range 8).map fun i =>
    Gate.mkMUX barrel_l0[i]! barrel_l0[(i+2) % 8]! tail_ptr[1]! barrel_l1[i]!

  let barrel_l2 := mkWires "barrel_l2_" 8
  let barrel_l2_gates := (List.range 8).map fun i =>
    Gate.mkMUX barrel_l1[i]! barrel_l1[(i+4) % 8]! tail_ptr[2]! barrel_l2[i]!

  -- Reverse so youngest is at position 0:
  let arb_requests := mkWires "arb_req_" 8
  let arb_request_gates := (List.range 8).map fun j =>
    Gate.mkBUF barrel_l2[7-j]! arb_requests[j]!

  -- Step 2: PriorityArbiter8 selects youngest match
  let arb_grants := mkWires "arb_grant_" 8
  let arb_valid := Wire.mk "arb_valid"
  let arb_inst : CircuitInstance := {
    moduleName := "PriorityArbiter8"
    instName := "u_arb"
    portMap :=
      (arb_requests.enum.map (fun ⟨i, w⟩ => (s!"request_{i}", w))) ++
      (arb_grants.enum.map (fun ⟨i, w⟩ => (s!"grant_{i}", w))) ++
      [("valid", arb_valid)]
  }

  -- fwd_hit = arbiter has a valid selection
  let fwd_hit_gate := Gate.mkBUF arb_valid fwd_hit

  -- fwd_word_hit = OR of all word_match[i]
  let fwd_word_hit := Wire.mk "fwd_word_hit"
  let fwh_t0 := Wire.mk "fwh_t0"
  let fwh_t1 := Wire.mk "fwh_t1"
  let fwh_t2 := Wire.mk "fwh_t2"
  let fwh_t3 := Wire.mk "fwh_t3"
  let fwh_t4 := Wire.mk "fwh_t4"
  let fwh_t5 := Wire.mk "fwh_t5"
  let fwd_word_hit_gates := [
    Gate.mkOR word_matches[0]! word_matches[1]! fwh_t0,
    Gate.mkOR word_matches[2]! word_matches[3]! fwh_t1,
    Gate.mkOR word_matches[4]! word_matches[5]! fwh_t2,
    Gate.mkOR word_matches[6]! word_matches[7]! fwh_t3,
    Gate.mkOR fwh_t0 fwh_t1 fwh_t4,
    Gate.mkOR fwh_t2 fwh_t3 fwh_t5,
    Gate.mkOR fwh_t4 fwh_t5 fwd_word_hit
  ]

  -- fwd_word_only_hit = OR of all word_only_match[i]
  -- True when any entry has a word-level match but NOT an exact byte-address match
  let fwd_word_only_hit := Wire.mk "fwd_word_only_hit"
  let fwoh_t0 := Wire.mk "fwoh_t0"
  let fwoh_t1 := Wire.mk "fwoh_t1"
  let fwoh_t2 := Wire.mk "fwoh_t2"
  let fwoh_t3 := Wire.mk "fwoh_t3"
  let fwoh_t4 := Wire.mk "fwoh_t4"
  let fwoh_t5 := Wire.mk "fwoh_t5"
  -- replay_needed = fwd_word_only_hit (partial word overlap, M2 decision)
  let replay_gate := Gate.mkBUF fwd_word_only_hit replay_needed
  let fwd_word_only_hit_gates := [
    Gate.mkOR word_only_matches[0]! word_only_matches[1]! fwoh_t0,
    Gate.mkOR word_only_matches[2]! word_only_matches[3]! fwoh_t1,
    Gate.mkOR word_only_matches[4]! word_only_matches[5]! fwoh_t2,
    Gate.mkOR word_only_matches[6]! word_only_matches[7]! fwoh_t3,
    Gate.mkOR fwoh_t0 fwoh_t1 fwoh_t4,
    Gate.mkOR fwoh_t2 fwoh_t3 fwoh_t5,
    Gate.mkOR fwoh_t4 fwoh_t5 fwd_word_only_hit
  ]

  -- fwd_committed_hit = OR of all committed matches
  let fwd_committed_hit := Wire.mk "fwd_committed_hit"
  let fch_t0 := Wire.mk "fch_t0"
  let fch_t1 := Wire.mk "fch_t1"
  let fch_t2 := Wire.mk "fch_t2"
  let fch_t3 := Wire.mk "fch_t3"
  let fch_t4 := Wire.mk "fch_t4"
  let fch_t5 := Wire.mk "fch_t5"
  let fwd_committed_hit_gates := [
    Gate.mkOR fwd_committed_matches[0]! fwd_committed_matches[1]! fch_t0,
    Gate.mkOR fwd_committed_matches[2]! fwd_committed_matches[3]! fch_t1,
    Gate.mkOR fwd_committed_matches[4]! fwd_committed_matches[5]! fch_t2,
    Gate.mkOR fwd_committed_matches[6]! fwd_committed_matches[7]! fch_t3,
    Gate.mkOR fch_t0 fch_t1 fch_t4,
    Gate.mkOR fch_t2 fch_t3 fch_t5,
    Gate.mkOR fch_t4 fch_t5 fwd_committed_hit
  ]

  -- Step 3: Reverse-rotate the grant vector back to original entry indices.
  let unreversed := mkWires "unreversed_" 8
  let unreversed_gates := (List.range 8).map fun k =>
    Gate.mkBUF arb_grants[7-k]! unreversed[k]!

  -- Rotate right by tail_ptr (undo the left rotation):
  let unrot_l0 := mkWires "unrot_l0_" 8
  let unrot_l0_gates := (List.range 8).map fun i =>
    Gate.mkMUX unreversed[i]! unreversed[(i + 8 - 1) % 8]! tail_ptr[0]! unrot_l0[i]!

  let unrot_l1 := mkWires "unrot_l1_" 8
  let unrot_l1_gates := (List.range 8).map fun i =>
    Gate.mkMUX unrot_l0[i]! unrot_l0[(i + 8 - 2) % 8]! tail_ptr[1]! unrot_l1[i]!

  let unrot_l2 := mkWires "unrot_l2_" 8
  let unrot_l2_gates := (List.range 8).map fun i =>
    Gate.mkMUX unrot_l1[i]! unrot_l1[(i + 8 - 4) % 8]! tail_ptr[2]! unrot_l2[i]!

  -- Convert one-hot to 3-bit binary for Mux8x32 selector:
  let fwd_sel := mkWires "fwd_sel_" 3
  let oh2b_t0 := Wire.mk "oh2b_t0"
  let oh2b_t1 := Wire.mk "oh2b_t1"
  let oh2b_t2 := Wire.mk "oh2b_t2"
  let oh2b_t3 := Wire.mk "oh2b_t3"
  let oh2b_t4 := Wire.mk "oh2b_t4"
  let oh2b_t5 := Wire.mk "oh2b_t5"
  let oh2b_gates := [
    Gate.mkOR unrot_l2[1]! unrot_l2[3]! oh2b_t0,
    Gate.mkOR unrot_l2[5]! unrot_l2[7]! oh2b_t1,
    Gate.mkOR oh2b_t0 oh2b_t1 fwd_sel[0]!,
    Gate.mkOR unrot_l2[2]! unrot_l2[3]! oh2b_t2,
    Gate.mkOR unrot_l2[6]! unrot_l2[7]! oh2b_t3,
    Gate.mkOR oh2b_t2 oh2b_t3 fwd_sel[1]!,
    Gate.mkOR unrot_l2[4]! unrot_l2[5]! oh2b_t4,
    Gate.mkOR unrot_l2[6]! unrot_l2[7]! oh2b_t5,
    Gate.mkOR oh2b_t4 oh2b_t5 fwd_sel[2]!
  ]

  -- Step 4: Mux8x64 selects forwarding data
  let fwd_mux_inst : CircuitInstance := {
    moduleName := "Mux8x64"
    instName := "u_fwd_mux"
    portMap :=
      ((List.range 8).map (fun i =>
        (List.range 64).map (fun j => (s!"in{i}[{j}]", all_entry_data[i]![j]!))
      )).flatten ++
      (fwd_sel.enum.map (fun ⟨k, w⟩ => (s!"sel[{k}]", w))) ++
      (fwd_data.enum.map (fun ⟨j, w⟩ => (s!"out[{j}]", w)))
  }

  -- Step 5: Mux8x2 selects forwarding entry's size
  let fwd_size := mkWires "fwd_size_" 2
  let fwd_size_mux_inst : CircuitInstance := {
    moduleName := "Mux8x2"
    instName := "u_fwd_size_mux"
    portMap :=
      ((List.range 8).map (fun i =>
        (List.range 2).map (fun j => (s!"in{i}[{j}]", all_entry_size[i]![j]!))
      )).flatten ++
      (fwd_sel.enum.map (fun ⟨k, w⟩ => (s!"sel[{k}]", w))) ++
      (fwd_size.enum.map (fun ⟨j, w⟩ => (s!"out[{j}]", w)))
  }

  -- === Dequeue Readout ===

  -- deq_valid = AND(head_valid, head_committed)
  -- With proper valid bitmap, no stale entry check needed!
  let head_valid := Wire.mk "head_valid"
  let head_committed := Wire.mk "head_committed"

  -- 8:1 mux for head valid/committed bits using head_ptr
  let mkBitMux8 (bits : List Wire) (sel : List Wire) (output : Wire) (pfx : String) : List Gate :=
    let l0 := (List.range 4).map fun k =>
      let w := Wire.mk s!"{pfx}_l0_{k}"
      (Gate.mkMUX bits[2*k]! bits[2*k+1]! sel[0]! w, w)
    let l0_gates := l0.map Prod.fst
    let l0_outs := l0.map Prod.snd
    let l1 := (List.range 2).map fun k =>
      let w := Wire.mk s!"{pfx}_l1_{k}"
      (Gate.mkMUX l0_outs[2*k]! l0_outs[2*k+1]! sel[1]! w, w)
    let l1_gates := l1.map Prod.fst
    let l1_outs := l1.map Prod.snd
    let final := Gate.mkMUX l1_outs[0]! l1_outs[1]! sel[2]! output
    l0_gates ++ l1_gates ++ [final]

  let head_valid_gates := mkBitMux8 valid head_ptr head_valid "hv"
  let head_committed_gates := mkBitMux8 committed head_ptr head_committed "hc"

  let deq_valid_gate := Gate.mkAND head_valid head_committed deq_valid

  -- Dequeue data readout via Mux8x64 (address)
  let deq_addr_mux_inst : CircuitInstance := {
    moduleName := "Mux8x64"
    instName := "u_deq_addr_mux"
    portMap :=
      ((List.range 8).map (fun i =>
        let e := all_entry_cur[i]!
        (List.range 64).map (fun j => (s!"in{i}[{j}]", e[j]!))
      )).flatten ++
      (head_ptr.enum.map (fun ⟨k, w⟩ => (s!"sel[{k}]", w))) ++
      ((List.range 64).map (fun j => (s!"out[{j}]", deq_bits[j]!)))
  }

  -- Dequeue data readout via Mux8x64 (data)
  let deq_data_mux_inst : CircuitInstance := {
    moduleName := "Mux8x64"
    instName := "u_deq_data_mux"
    portMap :=
      ((List.range 8).map (fun i =>
        let e := all_entry_cur[i]!
        (List.range 64).map (fun j => (s!"in{i}[{j}]", e[64+j]!))
      )).flatten ++
      (head_ptr.enum.map (fun ⟨k, w⟩ => (s!"sel[{k}]", w))) ++
      ((List.range 64).map (fun j => (s!"out[{j}]", deq_bits[64+j]!)))
  }

  -- Dequeue size readout via Mux8x2
  let deq_size_mux_inst : CircuitInstance := {
    moduleName := "Mux8x2"
    instName := "u_deq_size_mux"
    portMap :=
      ((List.range 8).map (fun i =>
        let e := all_entry_cur[i]!
        (List.range 2).map (fun j => (s!"in{i}[{j}]", e[128+j]!))
      )).flatten ++
      (head_ptr.enum.map (fun ⟨k, w⟩ => (s!"sel[{k}]", w))) ++
      ((List.range 2).map (fun j => (s!"out[{j}]", deq_bits[128+j]!)))
  }

  -- === Assemble Circuit ===

  let all_inputs :=
    [clock, reset, zero, one] ++
    [enq_en] ++ enq_idx_in ++ enq_address ++ enq_data ++ enq_size ++
    [commit_en] ++
    [deq_ready] ++
    fwd_address ++
    [flush_en]

  let all_outputs :=
    [full, empty] ++ enq_idx ++ flush_tail ++
    [flush_applied, flush_pending] ++
    [deq_valid] ++ deq_bits ++
    [fwd_hit, fwd_committed_hit, fwd_word_hit, fwd_word_only_hit] ++ fwd_data ++ fwd_size ++
    [replay_needed]

  let all_gates :=
    reset_buf_gates ++
    [full_gate] ++ empty_gates ++ enq_idx_gates ++
    [deq_fire_gate, deq_valid_gate] ++
    flush_apply_gates ++
    commit_gate_gates ++ [pc_reset_gate] ++
    bitmap_gates ++ surviving_gates ++
    flush_count_gates ++ flush_tail_gates ++ flush_tail_out_gates ++
    all_entry_gates ++
    barrel_l0_gates ++ barrel_l1_gates ++ barrel_l2_gates ++
    arb_request_gates ++ [fwd_hit_gate] ++ fwd_word_hit_gates ++ [replay_gate] ++ fwd_word_only_hit_gates ++ fwd_committed_hit_gates ++
    unreversed_gates ++ unrot_l0_gates ++ unrot_l1_gates ++ unrot_l2_gates ++
    oh2b_gates ++
    head_valid_gates ++ head_committed_gates

  let all_instances :=
    [head_inst, tail_inst, count_inst, commit_ptr_inst, enq_dec_inst, head_dec_inst, commit_dec_inst, pop_inst, flush_pending_inst] ++
    valid_dff_insts ++ committed_dff_insts ++ pc_dff_insts ++
    all_entry_instances ++
    [arb_inst, fwd_mux_inst, fwd_size_mux_inst] ++
    [deq_addr_mux_inst, deq_data_mux_inst, deq_size_mux_inst]

  { name := "StoreBuffer8"
    inputs := all_inputs
    outputs := all_outputs
    gates := all_gates
    instances := all_instances
    -- V2 codegen annotations
    signalGroups := [
      { name := "enq_idx_in_", width := 3, wires := enq_idx_in },
      { name := "enq_address_", width := 64, wires := enq_address },
      { name := "enq_data_", width := 64, wires := enq_data },
      { name := "enq_size_", width := 2, wires := enq_size },
      { name := "commit_ptr_", width := 3, wires := commit_ptr },
      { name := "deq_bits_", width := 130, wires := deq_bits },
      { name := "fwd_address_", width := 64, wires := fwd_address },
      { name := "fwd_data_", width := 64, wires := fwd_data },
      { name := "fwd_size_", width := 2, wires := fwd_size },
      { name := "enq_idx_", width := 3, wires := enq_idx },
      { name := "flush_tail_", width := 3, wires := flush_tail },
      { name := "head_ptr_", width := 3, wires := head_ptr },
      { name := "tail_ptr_", width := 3, wires := tail_ptr },
      { name := "count_", width := 4, wires := count },
      { name := "enq_decode_", width := 8, wires := enq_decode },
      { name := "commit_decode_", width := 8, wires := commit_decode },
      { name := "flush_tail_load_", width := 3, wires := flush_tail_load }
    ]
  }

/-- Config-driven Store Buffer (currently only supports 8 entries) -/
def mkStoreBufferFromConfig (_config : Shoumei.RISCV.CPUConfig) : Circuit :=
  mkStoreBuffer8

end Shoumei.RISCV.Memory

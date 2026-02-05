/-
RISCV/Memory/StoreBuffer.lean - Store Buffer with Forwarding

8-entry circular buffer for pending store operations.
Store-to-load forwarding with youngest-match priority.
Behavioral model + structural circuit (StoreBuffer8).

Entry lifecycle:
1. ENQUEUE: Dispatch allocates store at tail (valid=true, committed=false)
2. COMMITTED: ROB commits store → committed flag set via commit_idx
3. DEQUEUE: Committed head store written to memory via Decoupled port
4. FLUSH: Pipeline misprediction → full reset (committed stores drained first)

Forwarding:
- Loads check all valid entries for address match
- Youngest matching entry (closest to tail) wins
- Barrel rotation + PriorityArbiter8 for youngest-match selection
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.Register
import Shoumei.Circuits.Sequential.QueueComponents
import Shoumei.Circuits.Combinational.Comparator
import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.Arbiter

namespace Shoumei.RISCV.Memory

open Shoumei
open Shoumei.Circuits.Sequential
open Shoumei.Circuits.Combinational

/-! ## Store Buffer Entry -/

/-- A single store buffer entry (68 bits in structural circuit).

    Bit layout:
    | Bit(s) | Width | Field     |
    |--------|-------|-----------|
    | 0      | 1     | valid     |
    | 1      | 1     | committed |
    | 2-33   | 32    | address   |
    | 34-65  | 32    | data      |
    | 66-67  | 2     | size      |
-/
structure StoreBufferEntry where
  /-- Entry occupied -/
  valid : Bool
  /-- ROB has committed this store -/
  committed : Bool
  /-- Memory address -/
  address : UInt32
  /-- Store data -/
  data : UInt32
  /-- Access size: 0=byte, 1=half, 2=word -/
  size : Fin 4
  deriving Repr, BEq, DecidableEq

instance : Inhabited StoreBufferEntry where
  default := { valid := false, committed := false, address := 0, data := 0, size := 0 }

/-- Create an empty store buffer entry. -/
def StoreBufferEntry.empty : StoreBufferEntry := default

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

/-- Enqueue a new store at the tail.

    Returns (updated state, allocated index) or (unchanged, none) if full.
-/
def StoreBufferState.enqueue
    (sb : StoreBufferState)
    (address : UInt32) (data : UInt32) (size : Fin 4)
    : StoreBufferState × Option (Fin 8) :=
  if h : sb.count >= 8 then (sb, none)
  else
    let newEntry : StoreBufferEntry := {
      valid := true
      committed := false
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
def StoreBufferState.forwardCheck (sb : StoreBufferState) (addr : UInt32)
    : Option UInt32 :=
  -- Scan entries from youngest (tail-1) to oldest (head)
  let results := (List.range 8).filterMap fun j =>
    if h : j < 8 then
      let idx : Fin 8 := ⟨(sb.tail.val + 7 - j) % 8, by omega⟩
      let e := sb.entries idx
      if e.valid && e.address == addr then some e.data else none
    else none
  -- Return youngest match (first in scan order)
  results.head?

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

    **Architecture:**
    - 8 entries × 68 bits each (Register68)
    - Head/tail pointers (QueuePointer_3) with up/down count (QueueCounterUpDown_4)
    - Allocation decoder (Decoder3) + commit decoder (Decoder3)
    - Address matching via 8 parallel Comparator32 instances
    - Youngest-match forwarding: barrel rotation + PriorityArbiter8
    - Dequeue readout via Mux8x32 (address, data) + Mux8x2 (size)
    - Decoupled dequeue: deq_valid/deq_ready handshaking

    **Entry layout (68 bits):**
    | Bit(s)  | Width | Field     |
    |---------|-------|-----------|
    | 0       | 1     | valid     |
    | 1       | 1     | committed |
    | 2-33    | 32    | address   |
    | 34-65   | 32    | data      |
    | 66-67   | 2     | size      |

    **Instances (26):**
    - 8× Register68 (entry storage)
    - 8× Comparator32 (address matching for forwarding)
    - 2× QueuePointer_3 (head, tail)
    - 1× QueueCounterUpDown_4 (count)
    - 2× Decoder3 (enqueue decode, commit decode)
    - 3× Mux8x32 (fwd data, deq address, deq data)
    - 1× Mux8x2 (deq size)
    - 1× PriorityArbiter8 (youngest-match selection)
-/
def mkStoreBuffer8 : Circuit :=
  let mkWires := @Shoumei.Circuits.Combinational.makeIndexedWires

  -- === Global Signals ===
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- Combined reset: OR(reset, flush_en) for full flush support
  let flush_en := Wire.mk "flush_en"
  let combined_reset := Wire.mk "combined_reset"
  let combined_reset_gate := Gate.mkOR reset flush_en combined_reset

  -- === Enqueue Interface ===
  let enq_en := Wire.mk "enq_en"
  let enq_address := mkWires "enq_address_" 32
  let enq_data := mkWires "enq_data_" 32
  let enq_size := mkWires "enq_size_" 2

  -- === Commit Interface ===
  let commit_en := Wire.mk "commit_en"
  let commit_idx := mkWires "commit_idx_" 3

  -- === Dequeue Interface (Decoupled) ===
  let deq_ready := Wire.mk "deq_ready"
  let deq_valid := Wire.mk "deq_valid"
  let deq_bits := mkWires "deq_bits_" 66

  -- === Forwarding Interface ===
  let fwd_address := mkWires "fwd_address_" 32
  let fwd_hit := Wire.mk "fwd_hit"
  let fwd_data := mkWires "fwd_data_" 32

  -- === Status Outputs ===
  let full := Wire.mk "full"
  let empty := Wire.mk "empty"
  let enq_idx := mkWires "enq_idx_" 3

  -- === Internal Wires ===
  let head_ptr := mkWires "head_ptr_" 3
  let tail_ptr := mkWires "tail_ptr_" 3
  let count := mkWires "count_" 4
  let enq_decode := mkWires "enq_decode_" 8
  let commit_decode := mkWires "commit_decode_" 8

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

  let head_inst : CircuitInstance := {
    moduleName := "QueuePointer_3"
    instName := "u_head"
    portMap :=
      [("clock", clock), ("reset", combined_reset), ("en", deq_fire),
       ("one", one), ("zero", zero)] ++
      (head_ptr.enum.map (fun ⟨i, w⟩ => (s!"count_{i}", w)))
  }

  let tail_inst : CircuitInstance := {
    moduleName := "QueuePointer_3"
    instName := "u_tail"
    portMap :=
      [("clock", clock), ("reset", combined_reset), ("en", enq_en),
       ("one", one), ("zero", zero)] ++
      (tail_ptr.enum.map (fun ⟨i, w⟩ => (s!"count_{i}", w)))
  }

  let count_inst : CircuitInstance := {
    moduleName := "QueueCounterUpDown_4"
    instName := "u_count"
    portMap :=
      [("clock", clock), ("reset", combined_reset), ("inc", enq_en),
       ("dec", deq_fire), ("one", one), ("zero", zero)] ++
      (count.enum.map (fun ⟨i, w⟩ => (s!"count_{i}", w)))
  }

  let enq_dec_inst : CircuitInstance := {
    moduleName := "Decoder3"
    instName := "u_enq_dec"
    portMap :=
      (tail_ptr.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (enq_decode.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  let commit_dec_inst : CircuitInstance := {
    moduleName := "Decoder3"
    instName := "u_commit_dec"
    portMap :=
      (commit_idx.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (commit_decode.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- === Per-Entry Logic (8 entries) ===

  let entryResults := (List.range 8).map fun i =>
    let e_cur := mkWires s!"e{i}_" 68
    let e_next := mkWires s!"e{i}_next_" 68

    -- Current state field accessors
    let cur_valid := e_cur[0]!
    let cur_committed := e_cur[1]!
    let cur_address := (List.range 32).map (fun j => e_cur[2+j]!)
    let cur_data := (List.range 32).map (fun j => e_cur[34+j]!)
    let cur_size := (List.range 2).map (fun j => e_cur[66+j]!)

    -- Control: enqueue write enable = AND(enq_en, enq_decode[i])
    let enq_we := Wire.mk s!"e{i}_enq_we"
    let enq_we_gate := Gate.mkAND enq_en enq_decode[i]! enq_we

    -- Control: commit write enable = AND(commit_en, commit_decode[i])
    let commit_we := Wire.mk s!"e{i}_commit_we"
    let commit_we_gate := Gate.mkAND commit_en commit_decode[i]! commit_we

    -- Comparator32 instance: fwd_address vs entry address (for forwarding)
    let cmp_eq := Wire.mk s!"e{i}_cmp_eq"
    let cmp_inst : CircuitInstance := {
      moduleName := "Comparator32"
      instName := s!"u_cmp{i}"
      portMap :=
        (fwd_address.enum.map (fun ⟨j, w⟩ => (s!"a_{j}", w))) ++
        (cur_address.enum.map (fun ⟨j, w⟩ => (s!"b_{j}", w))) ++
        [("one", one), ("eq", cmp_eq),
         ("lt", Wire.mk s!"e{i}_cmp_lt_unused"),
         ("ltu", Wire.mk s!"e{i}_cmp_ltu_unused"),
         ("gt", Wire.mk s!"e{i}_cmp_gt_unused"),
         ("gtu", Wire.mk s!"e{i}_cmp_gtu_unused")]
    }

    -- Register68 instance: entry storage
    let reg_inst : CircuitInstance := {
      moduleName := "Register68"
      instName := s!"u_entry{i}"
      portMap :=
        (e_next.enum.map (fun ⟨j, w⟩ => (s!"d_{j}", w))) ++
        [("clock", clock), ("reset", combined_reset)] ++
        (e_cur.enum.map (fun ⟨j, w⟩ => (s!"q_{j}", w)))
    }

    -- === Next-State Logic ===

    -- valid_next: MUX priority: flush/reset (via combined_reset) > enq > hold
    -- Since combined_reset goes to Register68 reset, we just handle enq > hold
    let valid_gate :=
      Gate.mkMUX cur_valid one enq_we e_next[0]!

    -- committed_next: MUX priority: enq (clears) > commit (sets) > hold
    let committed_mux1 := Wire.mk s!"e{i}_committed_mux1"
    let committed_gates := [
      Gate.mkMUX cur_committed one commit_we committed_mux1,  -- commit sets committed
      Gate.mkMUX committed_mux1 zero enq_we e_next[1]!        -- enq clears committed
    ]

    -- address_next: only changes on enq
    let address_gates := (List.range 32).map fun j =>
      Gate.mkMUX cur_address[j]! enq_address[j]! enq_we e_next[2+j]!

    -- data_next: only changes on enq
    let data_gates := (List.range 32).map fun j =>
      Gate.mkMUX cur_data[j]! enq_data[j]! enq_we e_next[34+j]!

    -- size_next: only changes on enq
    let size_gates := (List.range 2).map fun j =>
      Gate.mkMUX cur_size[j]! enq_size[j]! enq_we e_next[66+j]!

    -- Forwarding match: valid AND address_eq
    let fwd_match := Wire.mk s!"e{i}_fwd_match"
    let fwd_match_gate := Gate.mkAND cur_valid cmp_eq fwd_match

    -- Collect all per-entry gates
    let entry_gates :=
      [enq_we_gate, commit_we_gate] ++
      [valid_gate] ++ committed_gates ++
      address_gates ++ data_gates ++ size_gates ++
      [fwd_match_gate]

    (entry_gates, [cmp_inst, reg_inst], e_cur, fwd_match, cur_data)

  -- Flatten per-entry results
  let all_entry_gates := (entryResults.map (fun (g, _, _, _, _) => g)).flatten
  let all_entry_instances := (entryResults.map (fun (_, insts, _, _, _) => insts)).flatten
  let all_entry_cur := entryResults.map (fun (_, _, cur, _, _) => cur)
  let fwd_matches := entryResults.map (fun (_, _, _, m, _) => m)
  let all_entry_data := entryResults.map (fun (_, _, _, _, d) => d)

  -- === Forwarding Logic: Youngest-Match via Barrel Rotation ===

  -- Step 1: Barrel rotate match vector so youngest entry maps to position 0.
  -- We rotate LEFT by tail_ptr, then reverse (youngest = tail-1 → position 0).
  --
  -- Barrel rotate left by shift[2:0]:
  --   Level 0 (shift[0]): conditionally shift by 1
  --   Level 1 (shift[1]): conditionally shift by 2
  --   Level 2 (shift[2]): conditionally shift by 4

  let barrel_l0 := mkWires "barrel_l0_" 8
  let barrel_l0_gates := (List.range 8).map fun i =>
    -- If tail_ptr[0], take match[(i+1) mod 8]; else take match[i]
    Gate.mkMUX fwd_matches[i]! fwd_matches[(i+1) % 8]! tail_ptr[0]! barrel_l0[i]!

  let barrel_l1 := mkWires "barrel_l1_" 8
  let barrel_l1_gates := (List.range 8).map fun i =>
    Gate.mkMUX barrel_l0[i]! barrel_l0[(i+2) % 8]! tail_ptr[1]! barrel_l1[i]!

  let barrel_l2 := mkWires "barrel_l2_" 8
  let barrel_l2_gates := (List.range 8).map fun i =>
    Gate.mkMUX barrel_l1[i]! barrel_l1[(i+4) % 8]! tail_ptr[2]! barrel_l2[i]!

  -- After rotate-left by tail_ptr: barrel_l2[k] = match[(k + tail) mod 8]
  -- Entry at (tail-1) mod 8 is the youngest → it's at barrel_l2[(tail-1-tail+8) mod 8]
  --   = barrel_l2[7]
  -- Reverse so youngest is at position 0:
  -- reversed[j] = barrel_l2[7-j]
  -- PriorityArbiter8 gives lowest-index priority, so reversed[0] = youngest gets highest priority.

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

  -- Step 3: Reverse-rotate the grant vector back to original entry indices.
  -- The grant is in reversed-rotated domain. Un-reverse first:
  -- unreversed[k] = arb_grants[7-k]
  -- Then un-rotate (rotate RIGHT by tail_ptr):
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

  -- unrot_l2 is a one-hot vector in the original entry domain.
  -- Convert one-hot to 3-bit binary for Mux8x32 selector:
  -- sel[0] = grant[1] OR grant[3] OR grant[5] OR grant[7]
  -- sel[1] = grant[2] OR grant[3] OR grant[6] OR grant[7]
  -- sel[2] = grant[4] OR grant[5] OR grant[6] OR grant[7]
  let fwd_sel := mkWires "fwd_sel_" 3
  let oh2b_t0 := Wire.mk "oh2b_t0"
  let oh2b_t1 := Wire.mk "oh2b_t1"
  let oh2b_t2 := Wire.mk "oh2b_t2"
  let oh2b_t3 := Wire.mk "oh2b_t3"
  let oh2b_t4 := Wire.mk "oh2b_t4"
  let oh2b_t5 := Wire.mk "oh2b_t5"
  let oh2b_gates := [
    -- sel[0] = OR(grant[1], grant[3], grant[5], grant[7])
    Gate.mkOR unrot_l2[1]! unrot_l2[3]! oh2b_t0,
    Gate.mkOR unrot_l2[5]! unrot_l2[7]! oh2b_t1,
    Gate.mkOR oh2b_t0 oh2b_t1 fwd_sel[0]!,
    -- sel[1] = OR(grant[2], grant[3], grant[6], grant[7])
    Gate.mkOR unrot_l2[2]! unrot_l2[3]! oh2b_t2,
    Gate.mkOR unrot_l2[6]! unrot_l2[7]! oh2b_t3,
    Gate.mkOR oh2b_t2 oh2b_t3 fwd_sel[1]!,
    -- sel[2] = OR(grant[4], grant[5], grant[6], grant[7])
    Gate.mkOR unrot_l2[4]! unrot_l2[5]! oh2b_t4,
    Gate.mkOR unrot_l2[6]! unrot_l2[7]! oh2b_t5,
    Gate.mkOR oh2b_t4 oh2b_t5 fwd_sel[2]!
  ]

  -- Step 4: Mux8x32 selects forwarding data
  let fwd_mux_inst : CircuitInstance := {
    moduleName := "Mux8x32"
    instName := "u_fwd_mux"
    portMap :=
      ((List.range 8).map (fun i =>
        (List.range 32).map (fun j => (s!"in{i}[{j}]", all_entry_data[i]![j]!))
      )).flatten ++
      (fwd_sel.enum.map (fun ⟨k, w⟩ => (s!"sel[{k}]", w))) ++
      (fwd_data.enum.map (fun ⟨j, w⟩ => (s!"out[{j}]", w)))
  }

  -- === Dequeue Readout ===

  -- Head entry valid/committed via 3-level MUX tree (8:1 mux for single bits)
  let mkBitMux8 (entries : List (List Wire)) (bitIdx : Nat)
      (sel : List Wire) (output : Wire) (pfx : String) : List Gate :=
    -- Level 0: select between pairs using sel[0]
    let l0 := (List.range 4).map fun k =>
      let w := Wire.mk s!"{pfx}_l0_{k}"
      let e0bit := entries[2*k]![bitIdx]!
      let e1bit := entries[2*k+1]![bitIdx]!
      (Gate.mkMUX e0bit e1bit sel[0]! w, w)
    let l0_gates := l0.map Prod.fst
    let l0_outs := l0.map Prod.snd
    -- Level 1: select between pairs using sel[1]
    let l1 := (List.range 2).map fun k =>
      let w := Wire.mk s!"{pfx}_l1_{k}"
      (Gate.mkMUX l0_outs[2*k]! l0_outs[2*k+1]! sel[1]! w, w)
    let l1_gates := l1.map Prod.fst
    let l1_outs := l1.map Prod.snd
    -- Level 2: final select using sel[2]
    let final := Gate.mkMUX l1_outs[0]! l1_outs[1]! sel[2]! output
    l0_gates ++ l1_gates ++ [final]

  let head_valid := Wire.mk "head_valid"
  let head_committed := Wire.mk "head_committed"
  let head_valid_gates := mkBitMux8 all_entry_cur 0 head_ptr head_valid "hv"
  let head_committed_gates := mkBitMux8 all_entry_cur 1 head_ptr head_committed "hc"

  -- deq_valid = AND(head_valid, head_committed)
  let deq_valid_gate := Gate.mkAND head_valid head_committed deq_valid

  -- Dequeue data readout via Mux8x32 (address)
  let deq_addr_mux_inst : CircuitInstance := {
    moduleName := "Mux8x32"
    instName := "u_deq_addr_mux"
    portMap :=
      ((List.range 8).map (fun i =>
        let e := all_entry_cur[i]!
        (List.range 32).map (fun j => (s!"in{i}[{j}]", e[2+j]!))
      )).flatten ++
      (head_ptr.enum.map (fun ⟨k, w⟩ => (s!"sel[{k}]", w))) ++
      ((List.range 32).map (fun j => (s!"out[{j}]", deq_bits[j]!)))
  }

  -- Dequeue data readout via Mux8x32 (data)
  let deq_data_mux_inst : CircuitInstance := {
    moduleName := "Mux8x32"
    instName := "u_deq_data_mux"
    portMap :=
      ((List.range 8).map (fun i =>
        let e := all_entry_cur[i]!
        (List.range 32).map (fun j => (s!"in{i}[{j}]", e[34+j]!))
      )).flatten ++
      (head_ptr.enum.map (fun ⟨k, w⟩ => (s!"sel[{k}]", w))) ++
      ((List.range 32).map (fun j => (s!"out[{j}]", deq_bits[32+j]!)))
  }

  -- Dequeue size readout via Mux8x2
  let deq_size_mux_inst : CircuitInstance := {
    moduleName := "Mux8x2"
    instName := "u_deq_size_mux"
    portMap :=
      ((List.range 8).map (fun i =>
        let e := all_entry_cur[i]!
        (List.range 2).map (fun j => (s!"in{i}[{j}]", e[66+j]!))
      )).flatten ++
      (head_ptr.enum.map (fun ⟨k, w⟩ => (s!"sel[{k}]", w))) ++
      ((List.range 2).map (fun j => (s!"out[{j}]", deq_bits[64+j]!)))
  }

  -- === Assemble Circuit ===

  let all_inputs :=
    [clock, reset, zero, one] ++
    [enq_en] ++ enq_address ++ enq_data ++ enq_size ++
    [commit_en] ++ commit_idx ++
    [deq_ready] ++
    fwd_address ++
    [flush_en]

  let all_outputs :=
    [full, empty] ++ enq_idx ++
    [deq_valid] ++ deq_bits ++
    [fwd_hit] ++ fwd_data

  let all_gates :=
    [combined_reset_gate, full_gate] ++ empty_gates ++ enq_idx_gates ++
    [deq_fire_gate, deq_valid_gate] ++
    all_entry_gates ++
    barrel_l0_gates ++ barrel_l1_gates ++ barrel_l2_gates ++
    arb_request_gates ++ [fwd_hit_gate] ++
    unreversed_gates ++ unrot_l0_gates ++ unrot_l1_gates ++ unrot_l2_gates ++
    oh2b_gates ++
    head_valid_gates ++ head_committed_gates

  let all_instances :=
    [head_inst, tail_inst, count_inst, enq_dec_inst, commit_dec_inst] ++
    all_entry_instances ++
    [arb_inst, fwd_mux_inst] ++
    [deq_addr_mux_inst, deq_data_mux_inst, deq_size_mux_inst]

  { name := "StoreBuffer8"
    inputs := all_inputs
    outputs := all_outputs
    gates := all_gates
    instances := all_instances
    -- V2 codegen annotations
    signalGroups := [
      { name := "enq_address_", width := 32, wires := enq_address },
      { name := "enq_data_", width := 32, wires := enq_data },
      { name := "enq_size_", width := 2, wires := enq_size },
      { name := "commit_idx_", width := 3, wires := commit_idx },
      { name := "deq_bits_", width := 66, wires := deq_bits },
      { name := "fwd_address_", width := 32, wires := fwd_address },
      { name := "fwd_data_", width := 32, wires := fwd_data },
      { name := "enq_idx_", width := 3, wires := enq_idx },
      { name := "head_ptr_", width := 3, wires := head_ptr },
      { name := "tail_ptr_", width := 3, wires := tail_ptr },
      { name := "count_", width := 4, wires := count },
      { name := "enq_decode_", width := 8, wires := enq_decode },
      { name := "commit_decode_", width := 8, wires := commit_decode }
    ]
  }

end Shoumei.RISCV.Memory

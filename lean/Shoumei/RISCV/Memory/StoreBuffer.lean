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
      committed := false  -- Speculative until ROB commits (redirect-from-commit)
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

  -- Valid and committed bitmaps
  let valid := (List.range 8).map (fun i => Wire.mk s!"valid_e{i}")
  let committed := (List.range 8).map (fun i => Wire.mk s!"committed_e{i}")
  let valid_next := (List.range 8).map (fun i => Wire.mk s!"valid_next_e{i}")
  let committed_next := (List.range 8).map (fun i => Wire.mk s!"committed_next_e{i}")

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
       ("load_en", flush_en), ("one", one), ("zero", zero)] ++
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
       ("dec", deq_fire), ("load_en", flush_en), ("one", one), ("zero", zero)] ++
      (flush_count_load.enum.map (fun ⟨i, w⟩ => (s!"load_value_{i}", w))) ++
      (count.enum.map (fun ⟨i, w⟩ => (s!"count_{i}", w)))
  }

  let enq_dec_inst : CircuitInstance := {
    moduleName := "Decoder3"
    instName := "u_enq_dec"
    portMap :=
      (tail_ptr.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
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

  let commit_dec_inst : CircuitInstance := {
    moduleName := "Decoder3"
    instName := "u_commit_dec"
    portMap :=
      (commit_idx.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (commit_decode.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- === Flush Recovery: Popcount8 + Adder ===
  -- On flush, count surviving entries = popcount(valid AND committed)
  -- New tail = head + popcount (mod 8, only low 3 bits matter)

  let surviving := (List.range 8).map (fun i => Wire.mk s!"surviving_{i}")
  let surviving_gates := (List.range 8).map (fun i =>
    Gate.mkAND valid[i]! committed[i]! surviving[i]!)

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

  -- flush_tail_load = head_ptr + pop_count[2:0] (mod 8, wrapping 3-bit add)
  -- Simple 3-bit ripple-carry adder
  let ft_xor := (List.range 3).map (fun i => Wire.mk s!"ft_xor_b{i}")
  let ft_carry := (List.range 4).map (fun i => Wire.mk s!"ft_carry_b{i}")
  let ft_and1 := (List.range 3).map (fun i => Wire.mk s!"ft_and1_b{i}")
  let ft_and2 := (List.range 3).map (fun i => Wire.mk s!"ft_and2_b{i}")
  let flush_tail_gates := [
    Gate.mkBUF zero ft_carry[0]!
  ] ++ ((List.range 3).map (fun i =>
    [Gate.mkXOR head_ptr[i]! pop_count[i]! ft_xor[i]!,
     Gate.mkXOR ft_xor[i]! ft_carry[i]! flush_tail_load[i]!,
     Gate.mkAND head_ptr[i]! pop_count[i]! ft_and1[i]!,
     Gate.mkAND ft_xor[i]! ft_carry[i]! ft_and2[i]!,
     Gate.mkOR ft_and1[i]! ft_and2[i]! ft_carry[i+1]!]
  )).flatten

  -- === Per-Entry Valid/Committed Bitmap Logic ===

  let bitmap_gates := (List.range 8).map (fun i =>
    -- Enqueue write enable = AND(enq_en, enq_decode[i])
    let enq_we := Wire.mk s!"e{i}_enq_we"
    let enq_we_gate := Gate.mkAND enq_en enq_decode[i]! enq_we

    -- Dequeue clear enable = AND(deq_fire, head_decode[i])
    let deq_clr := Wire.mk s!"e{i}_deq_clr"
    let deq_clr_gate := Gate.mkAND deq_fire head_decode[i]! deq_clr

    -- Commit write enable = AND(commit_en, commit_decode[i])
    let commit_we := Wire.mk s!"e{i}_commit_we"
    let commit_we_gate := Gate.mkAND commit_en commit_decode[i]! commit_we

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
      Gate.mkNOT flush_en not_flush,
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

  -- Per-entry storage: 8× Register66 (address[31:0] + data[31:0] + size[1:0])
  let entryResults := (List.range 8).map fun i =>
    let e_cur := mkWires s!"e{i}_" 66
    let e_next := mkWires s!"e{i}_next_" 66

    let cur_address := (List.range 32).map (fun j => e_cur[j]!)
    let cur_data := (List.range 32).map (fun j => e_cur[32+j]!)
    let cur_size := (List.range 2).map (fun j => e_cur[64+j]!)

    -- Enqueue write enable = AND(enq_en, enq_decode[i])
    let enq_we := Wire.mk s!"e{i}_enq_we"  -- already created in bitmap logic, reuse wire name

    -- address_next: only changes on enq
    let address_gates := (List.range 32).map fun j =>
      Gate.mkMUX cur_address[j]! enq_address[j]! enq_we e_next[j]!

    -- data_next: only changes on enq
    let data_gates := (List.range 32).map fun j =>
      Gate.mkMUX cur_data[j]! enq_data[j]! enq_we e_next[32+j]!

    -- size_next: only changes on enq
    let size_gates := (List.range 2).map fun j =>
      Gate.mkMUX cur_size[j]! enq_size[j]! enq_we e_next[64+j]!

    -- Comparator32 instance: fwd_address vs entry address
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

    -- Register66 instance: entry storage
    let reg_inst : CircuitInstance := {
      moduleName := "Register66"
      instName := s!"u_entry{i}"
      portMap :=
        (e_next.enum.map (fun ⟨j, w⟩ => (s!"d_{j}", w))) ++
        [("clock", clock), ("reset", reset)] ++
        (e_cur.enum.map (fun ⟨j, w⟩ => (s!"q_{j}", w)))
    }

    -- Forwarding match: valid AND address_eq (no stale match possible!)
    let fwd_match := Wire.mk s!"e{i}_fwd_match"
    let fwd_match_gate := Gate.mkAND valid[i]! cmp_eq fwd_match

    -- Committed forwarding match: valid AND committed AND address_eq
    let fwd_committed_match := Wire.mk s!"e{i}_fwd_committed_match"
    let fwd_committed_match_gate := Gate.mkAND fwd_match committed[i]! fwd_committed_match

    let entry_gates := address_gates ++ data_gates ++ size_gates ++
      [fwd_match_gate, fwd_committed_match_gate]

    (entry_gates, [cmp_inst, reg_inst], e_cur, fwd_match, fwd_committed_match, cur_data)

  -- Flatten per-entry results
  let all_entry_gates := (entryResults.map (fun (g, _, _, _, _, _) => g)).flatten
  let all_entry_instances := (entryResults.map (fun (_, insts, _, _, _, _) => insts)).flatten
  let all_entry_cur := entryResults.map (fun (_, _, cur, _, _, _) => cur)
  let fwd_matches := entryResults.map (fun (_, _, _, m, _, _) => m)
  let fwd_committed_matches := entryResults.map (fun (_, _, _, _, cm, _) => cm)
  let all_entry_data := entryResults.map (fun (_, _, _, _, _, d) => d)

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

  -- Step 5: Mux8x2 selects forwarding entry's size
  let fwd_size := mkWires "fwd_size_" 2
  let fwd_size_mux_inst : CircuitInstance := {
    moduleName := "Mux8x2"
    instName := "u_fwd_size_mux"
    portMap :=
      ((List.range 8).map (fun i =>
        let e := all_entry_cur[i]!
        (List.range 2).map (fun j => (s!"in{i}[{j}]", e[64+j]!))
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

  -- Dequeue data readout via Mux8x32 (address)
  let deq_addr_mux_inst : CircuitInstance := {
    moduleName := "Mux8x32"
    instName := "u_deq_addr_mux"
    portMap :=
      ((List.range 8).map (fun i =>
        let e := all_entry_cur[i]!
        (List.range 32).map (fun j => (s!"in{i}[{j}]", e[j]!))
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
        (List.range 32).map (fun j => (s!"in{i}[{j}]", e[32+j]!))
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
        (List.range 2).map (fun j => (s!"in{i}[{j}]", e[64+j]!))
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
    [fwd_hit, fwd_committed_hit] ++ fwd_data ++ fwd_size ++
    flush_tail_load  -- committed_tail: new tail value on flush (for CPU commit ptr sync)

  let all_gates :=
    [full_gate] ++ empty_gates ++ enq_idx_gates ++
    [deq_fire_gate, deq_valid_gate] ++
    bitmap_gates ++ surviving_gates ++
    flush_count_gates ++ flush_tail_gates ++
    all_entry_gates ++
    barrel_l0_gates ++ barrel_l1_gates ++ barrel_l2_gates ++
    arb_request_gates ++ [fwd_hit_gate] ++ fwd_committed_hit_gates ++
    unreversed_gates ++ unrot_l0_gates ++ unrot_l1_gates ++ unrot_l2_gates ++
    oh2b_gates ++
    head_valid_gates ++ head_committed_gates

  let all_instances :=
    [head_inst, tail_inst, count_inst, enq_dec_inst, head_dec_inst, commit_dec_inst, pop_inst] ++
    valid_dff_insts ++ committed_dff_insts ++
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
      { name := "enq_address_", width := 32, wires := enq_address },
      { name := "enq_data_", width := 32, wires := enq_data },
      { name := "enq_size_", width := 2, wires := enq_size },
      { name := "commit_idx_", width := 3, wires := commit_idx },
      { name := "deq_bits_", width := 66, wires := deq_bits },
      { name := "fwd_address_", width := 32, wires := fwd_address },
      { name := "fwd_data_", width := 32, wires := fwd_data },
      { name := "fwd_size_", width := 2, wires := fwd_size },
      { name := "enq_idx_", width := 3, wires := enq_idx },
      { name := "head_ptr_", width := 3, wires := head_ptr },
      { name := "tail_ptr_", width := 3, wires := tail_ptr },
      { name := "count_", width := 4, wires := count },
      { name := "enq_decode_", width := 8, wires := enq_decode },
      { name := "commit_decode_", width := 8, wires := commit_decode },
      { name := "flush_tail_load_", width := 3, wires := flush_tail_load }
    ]
  }

end Shoumei.RISCV.Memory

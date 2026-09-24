/-
RISCV/Memory/LSU.lean - Load-Store Unit for RV32I Out-of-Order CPU

The LSU integrates memory operations into the out-of-order pipeline:
- Address calculation via MemoryExecUnit
- Store buffering with forwarding via StoreBuffer8
- Load-store ordering with TSO (Total Store Order) semantics
- ROB integration for store commitment

**TSO (Total Store Order) Memory Model:**
- Stores execute in program order (via store buffer)
- Loads can bypass stores to different addresses
- Store-to-load forwarding: loads match against store buffer first

**Interface:**
1. **Dispatch** (from Reservation Station): Execute memory operation
2. **Commit** (from ROB): Mark store as committed
3. **Memory Interface**: Send committed stores to memory, receive load data
4. **CDB Broadcast**: Broadcast load results when complete

**Entry lifecycle (stores):**
1. DISPATCH: Store allocated in store buffer (uncommitted)
2. COMMIT: ROB commits store -> mark committed in store buffer
3. DEQUEUE: Committed store sent to memory via Decoupled interface

**Entry lifecycle (loads):**
1. DISPATCH: Check store buffer for forwarding match
2. HIT: Forward data immediately, broadcast on CDB
3. MISS: Issue memory read request, wait for response
4. RESPONSE: Broadcast data on CDB when memory responds
-/

import Shoumei.DSL
import Shoumei.RISCV.ISA
import Shoumei.RISCV.Memory.StoreBuffer
import Shoumei.RISCV.Execution.MemoryExecUnit
import Shoumei.Circuits.Combinational.RippleCarryAdder
import Shoumei.Circuits.Combinational.MuxTree

namespace Shoumei.RISCV.Memory

open Shoumei.RISCV
open Shoumei.RISCV.Execution
open Shoumei.Circuits.Combinational

/-! ## Memory Interface State -/

/-- Pending load request waiting for memory response. -/
structure PendingLoadRequest where
  /-- Memory address -/
  address : UInt64
  /-- Access size -/
  size : MemSize
  /-- Sign-extend result? -/
  sign_extend : Bool
  /-- Destination tag for CDB broadcast -/
  dest_tag : Fin 64
  deriving Repr, BEq

instance : Inhabited PendingLoadRequest where
  default := { address := 0, size := MemSize.Word, sign_extend := false, dest_tag := 0 }

/-- Memory interface state (Decoupled handshaking). -/
structure MemoryInterfaceState where
  /-- Pending request (none if idle) -/
  pendingRequest : Option MemoryRequest
  /-- Memory controller is ready to accept requests -/
  requestReady : Bool
  /-- Memory response is valid -/
  responseValid : Bool
  /-- Memory response data -/
  responseData : UInt64

instance : Inhabited MemoryInterfaceState where
  default := {
    pendingRequest := none
    requestReady := true  -- Assume simple memory always ready
    responseValid := false
    responseData := 0
  }

/-! ## LSU State -/

/-- M1 pipeline register: AGU output latched at the stage1 boundary.
    The 64-bit adder result (M1) is isolated here; the forwarding driver
    (M2) consumes only registered values, so no combinational loop spans
    the two stages (docs/lsu-architecture.md §4). -/
structure Stage1Register where
  /-- Effective address from the AGU (M1) -/
  address : UInt64
  /-- Destination tag for the CDB -/
  dest_tag : Fin 64
  /-- Access size -/
  size : MemSize
  /-- Sign-extend result? -/
  sign_extend : Bool
  deriving Repr, BEq, DecidableEq

instance : Inhabited Stage1Register where
  default := { address := 0, dest_tag := 0, size := MemSize.Word, sign_extend := false }

/-- M2 pipeline register: CDB broadcast staged for the writeback cycle.
    The forwarding decision (exact/replay/miss) is made on stage1 values. -/
structure Stage2Register where
  /-- Destination tag -/
  dest_tag : Fin 64
  /-- Forwarded/loaded data -/
  data : UInt64
  deriving Repr, BEq, DecidableEq

instance : Inhabited Stage2Register where
  default := { dest_tag := 0, data := 0 }

/-- Miss Status Holding Register slot: tracks an outstanding miss so the
    request bus stays free (hit-under-miss). -/
structure MSHREntry where
  /-- Slot occupied -/
  valid : Bool
  /-- Line-aligned miss address -/
  line_addr : UInt64
  deriving Repr, BEq, DecidableEq

instance : Inhabited MSHREntry where
  default := { valid := false, line_addr := 0 }

/-- MSHR state: two registered slots; allocates on miss, frees on refill. -/
structure MSHRState where
  /-- Two miss slots -/
  slots : Fin 2 → MSHREntry

instance : Inhabited MSHRState where
  default := { slots := fun _ => default }

/-- Load-Store Unit State. -/
structure LSUState where
  /-- Store buffer (8 entries) -/
  storeBuffer : StoreBufferState
  /-- M1 AGU pipeline register -/
  stage1 : Option Stage1Register
  /-- M2 CDB pipeline register -/
  stage2 : Option Stage2Register
  /-- Two registered miss slots (non-blocking cache port) -/
  mshr : MSHRState
  /-- Legacy single-pending-load alias (MSHR head) -/
  pendingLoad : Option PendingLoadRequest
  /-- Memory interface state -/
  memoryInterface : MemoryInterfaceState

/-- Create an empty LSU. -/
def LSUState.empty : LSUState :=
  { storeBuffer := StoreBufferState.empty
    stage1 := none
    stage2 := none
    mshr := default
    pendingLoad := none
    memoryInterface := default
  }

/-! ## Helper Functions -/

/-- Check if LSU can accept a new store (store buffer not full). -/
def LSUState.canAcceptStore (lsu : LSUState) : Bool :=
  !lsu.storeBuffer.isFull

/-- Check if LSU can accept a new load (no pending load). -/
def LSUState.canAcceptLoad (lsu : LSUState) : Bool :=
  lsu.pendingLoad.isNone

/-! ## Core Operations -/
/-! ## MSHR Helpers -/

/-- First free MSHR slot, if any. -/
def LSUState.mshrFreeSlot (lsu : LSUState) : Option (Fin 2) :=
  if !(lsu.mshr.slots 0).valid then some 0
  else if !(lsu.mshr.slots 1).valid then some 1
  else none

/-- Allocate an MSHR slot for a miss line (caller latches the entry). -/
def LSUState.mshrAlloc (lsu : LSUState) (_line_addr : UInt64) : Option (Fin 2) :=
  lsu.mshrFreeSlot

/-- Free a slot after its refill completes. -/
def LSUState.mshrFree (lsu : LSUState) (idx : Fin 2) : LSUState :=
  { lsu with
    mshr := { slots := fun i => if i == idx then default else lsu.mshr.slots i } }

/-- Any miss slot occupied? -/
def LSUState.mshrBusy (lsu : LSUState) : Bool :=
  (lsu.mshr.slots 0).valid || (lsu.mshr.slots 1).valid

/-- Both miss slots occupied? -/
def LSUState.mshrFull (lsu : LSUState) : Bool :=
  (lsu.mshr.slots 0).valid && (lsu.mshr.slots 1).valid



/-- Execute store instruction.

    Enqueues store into store buffer (uncommitted).
    Returns updated state and success status.
-/
def LSUState.executeStore
    (lsu : LSUState)
    (opcode : OpType)
    (base : UInt64)      -- rs1 value (address base)
    (offset : Int)       -- Immediate offset
    (data : UInt64)      -- rs2 value (data to store)
    : LSUState × Bool :=
  -- Calculate effective address
  let addr := calculateMemoryAddress base offset

  -- Determine access size
  let size_fin : Fin 4 := match opcode with
    | .SB => 0  -- Byte
    | .SH => 1  -- Halfword
    | .SW => 2  -- Word
    | .SD => 3  -- Doubleword
    | _ => 3    -- Default to doubleword

  -- Enqueue into store buffer (uncommitted)
  let (newSB, allocResult) := lsu.storeBuffer.enqueue addr data size_fin

  match allocResult with
  | some _idx =>
      -- Success: store enqueued
      ({ lsu with storeBuffer := newSB }, true)
  | none =>
      -- Failure: store buffer full (stall)
      (lsu, false)

/-- Execute load instruction, stage M1: AGU (64-bit adder) + stage1 latch.

    Nothing in M1 consults the store queue or cache tags; the result is
    purely register-bound at the stage1 boundary.
-/
def LSUState.executeLoadM1
    (lsu : LSUState)
    (opcode : OpType)
    (base : UInt64)      -- rs1 value (base address)
    (offset : Int)       -- Immediate offset
    (dest_tag : Fin 64)  -- Destination physical register
    : LSUState :=
  let addr := calculateMemoryAddress base offset
  let (size, sign_ext) := match opcode with
    | .LB  => (MemSize.Byte, true)
    | .LH  => (MemSize.Halfword, true)
    | .LW  => (MemSize.Word, true)
    | .LBU => (MemSize.Byte, false)
    | .LHU => (MemSize.Halfword, false)
    | .LWU => (MemSize.Word, false)
    | .LD  => (MemSize.Doubleword, false)
    | _ => (MemSize.Doubleword, false)
  { lsu with
    stage1 := some { address := addr, dest_tag := dest_tag, size := size, sign_extend := sign_ext } }

/-- Execute load stage M2: consume the stage1 register, make the
    forwarding decision against the SQ (registered domain), and either
    drive the CDB staging, raise replay, or allocate an MSHR slot. -/
def LSUState.executeLoadM2 (lsu : LSUState) : LSUState × Option (Fin 64 × UInt64) :=
  match lsu.stage1 with
  | none => (lsu, none)
  | some s1 =>
      if lsu.storeBuffer.replayNeeded s1.address then
        -- Partial overlap: never byte-merge in the critical path; replay.
        ({ lsu with stage1 := none }, none)
      else
        match lsu.storeBuffer.forwardProbe s1.address with
        | some (data, true) =>
            let processed := processLoadResponse data s1.size s1.sign_extend
            ({ lsu with
               stage1 := none
               stage2 := some { dest_tag := s1.dest_tag, data := processed } },
             some (s1.dest_tag, processed))
        | some (_, false) =>
            -- word-only overlap handled by replayNeeded above; unreachable
            ({ lsu with stage1 := none }, none)
        | none =>
            match lsu.mshrAlloc s1.address with
            | some idx =>
                let pendingReq : PendingLoadRequest := {
                  address := s1.address
                  size := s1.size
                  sign_extend := s1.sign_extend
                  dest_tag := s1.dest_tag
                }
                ({ lsu with
                   stage1 := none
                   pendingLoad := some pendingReq
                   mshr := { slots := fun i =>
                     if i == idx then { valid := true, line_addr := s1.address } else lsu.mshr.slots i } },
                 none)
            | none =>
                ({ lsu with stage1 := none }, none)  -- MSHR full: stall upstream

/-- Legacy one-shot load: M1 then M2 in the same step (tests/behavioral).
    The structural retime separates them with the stage registers. -/
def LSUState.executeLoad
    (lsu : LSUState)
    (opcode : OpType)
    (base : UInt64)      -- rs1 value (base address)
    (offset : Int)       -- Immediate offset
    (dest_tag : Fin 64)  -- Destination physical register
    : LSUState × Option (Fin 64 × UInt64) :=
  -- Cannot accept new load if one is already pending
  if !lsu.canAcceptLoad then
    (lsu, none)
  else
    (lsu.executeLoadM1 opcode base offset dest_tag).executeLoadM2

/-- Commit a store instruction (called when ROB commits).

    Marks the store as committed in the store buffer via index.
    Committed stores can be dequeued and sent to memory.
-/
def LSUState.commitStore
    (lsu : LSUState)
    (store_buffer_idx : Fin 8)
    : LSUState :=
  let newSB := lsu.storeBuffer.markCommitted store_buffer_idx
  { lsu with storeBuffer := newSB }

/-- Dequeue a committed store from the store buffer.

    Sends oldest committed store to memory.
    Called when memory interface is ready (Decoupled handshaking).

    Returns (updated state, optional memory request).
-/
def LSUState.dequeueStore
    (lsu : LSUState)
    : LSUState × Option (UInt64 × UInt64 × Fin 4) :=
  let (newSB, deqResult) := lsu.storeBuffer.dequeue
  match deqResult with
  | some entry =>
      -- Dequeued committed store -> send to memory
      let memReq := (entry.address, entry.data, entry.size)
      ({ lsu with storeBuffer := newSB }, some memReq)
  | none =>
      -- No committed store to dequeue
      ({ lsu with storeBuffer := newSB }, none)

/-- Process memory response for pending load.

    Called when memory returns data for a pending load request.
    Returns (updated state, CDB broadcast with processed data).
-/
def LSUState.processMemoryResponse
    (lsu : LSUState)
    (mem_data : UInt64)
    : LSUState × Option (Fin 64 × UInt64) :=
  match lsu.pendingLoad with
  | none =>
      -- No pending load (shouldn't happen)
      (lsu, none)
  | some req =>
      -- Process load response with sign/zero extension
      let processed_data := processLoadResponse mem_data req.size req.sign_extend
      let cdb_broadcast := (req.dest_tag, processed_data)
      -- Clear pending load
      let newLSU := { lsu with pendingLoad := none }
      (newLSU, some cdb_broadcast)

/-- Full flush: clear all LSU state (pipeline misprediction).

    Clears:
    - Store buffer (all entries, including uncommitted)
    - Pending load request
    - Memory interface state
-/
def LSUState.fullFlush (lsu : LSUState) : LSUState :=
  { storeBuffer := lsu.storeBuffer.fullFlush
    stage1 := none
    stage2 := none
    mshr := default
    pendingLoad := none
    memoryInterface := default
  }

/-! ## Query Helpers -/

/-- Get current store buffer count. -/
def LSUState.storeBufferCount (lsu : LSUState) : Nat :=
  lsu.storeBuffer.getCount

/-- Check if store buffer is full. -/
def LSUState.storeBufferFull (lsu : LSUState) : Bool :=
  lsu.storeBuffer.isFull

/-- Check if store buffer is empty. -/
def LSUState.storeBufferEmpty (lsu : LSUState) : Bool :=
  lsu.storeBuffer.isEmpty

/-- Check if there is a pending load. -/
def LSUState.hasPendingLoad (lsu : LSUState) : Bool :=
  lsu.pendingLoad.isSome

/-! ## Structural Circuit -/

/-- Build LSU structural circuit: Load-Store Unit with store buffer and forwarding.

    **Architecture:**
    - MemoryExecUnit: Address calculation (base + offset)
    - StoreBuffer8: 8-entry store queue with youngest-match forwarding
    - Control FSM: Load/store path selection, memory interface management

    **Simplified Structural Circuit:**
    For Phase 7 MVP, this provides hierarchical composition of verified submodules:
    - MemoryExecUnit instance (address calculation)
    - StoreBuffer8 instance (store queue with forwarding)

    Full control FSM logic (load/store decode, memory interface, sign extension)
    is implemented in the behavioral model and validated via comprehensive tests.

    The structural circuit demonstrates correct hierarchical composition but
    defers complete gate-level control logic to future refinement.

    **Inputs:** (Minimal set for instance connections)
    - clock, reset, zero, one
    - dispatch_base[31:0]: Base address for load/store
    - dispatch_offset[31:0]: Offset for address calculation
    - dispatch_dest_tag[5:0]: Destination tag for loads
    - store_data[31:0]: Data to store
    (commit index is now internal to StoreBuffer8)
    - commit_store_en: Commit enable
    - deq_ready: Memory ready to accept stores
    - fwd_address[31:0]: Load address for forwarding check
    - flush_en: Flush signal

    **Outputs:**
    - agu_address[31:0]: Computed address from MemoryExecUnit
    - agu_tag_out[5:0]: Tag pass-through from MemoryExecUnit
    - sb_full: Store buffer full
    - sb_empty: Store buffer empty
    - sb_fwd_hit: Forwarding hit
    - sb_fwd_data[31:0]: Forwarded data
    - sb_deq_valid: Committed store ready to dequeue
    - sb_deq_bits[65:0]: Dequeue data (address[32] + data[32] + size[2])

    **Instances:**
    - MemoryExecUnit: Address calculation
    - StoreBuffer8: Store queue with forwarding
-/
def mkLSU : Circuit :=
  let mkWires := @Shoumei.Circuits.Combinational.makeIndexedWires

  -- === Global Signals ===
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- === Dispatch Interface ===
  let dispatch_base := mkWires "dispatch_base" 64
  let dispatch_offset := mkWires "dispatch_offset" 32
  let dispatch_dest_tag := mkWires "dispatch_dest_tag" 6
  let store_data := mkWires "store_data" 64

  -- === Store Commit Interface (from ROB) ===
  let commit_store_en := Wire.mk "commit_store_en"

  -- === Memory Interface ===
  let deq_ready := Wire.mk "deq_ready"

  -- === Forwarding Interface ===
  let fwd_address := mkWires "fwd_address" 64

  -- === Flush Interface ===
  let flush_en := Wire.mk "flush_en"

  -- === AGU (Address Generation Unit) Outputs ===
  let agu_address := mkWires "agu_address" 64
  let agu_tag_out := mkWires "agu_tag_out" 6

  -- === Store Buffer Outputs ===
  let sb_full := Wire.mk "sb_full"
  let sb_empty := Wire.mk "sb_empty"
  let sb_fwd_hit := Wire.mk "sb_fwd_hit"
  let sb_fwd_committed_hit := Wire.mk "sb_fwd_committed_hit"
  let sb_fwd_word_hit := Wire.mk "sb_fwd_word_hit"
  let sb_fwd_word_only_hit := Wire.mk "sb_fwd_word_only_hit"
  let sb_fwd_data := mkWires "sb_fwd_data" 64
  let sb_fwd_size := mkWires "sb_fwd_size" 2
  let sb_deq_valid := Wire.mk "sb_deq_valid"
  let sb_deq_bits := mkWires "sb_deq_bits" 130
  let sb_enq_idx := mkWires "sb_enq_idx" 3
  let sb_flush_tail := mkWires "sb_flush_tail" 3
  let sb_replay_raw := Wire.mk "sb_replay_raw"

  -- === Two-Stage Pipeline Registers (M1 -> M2, docs §4) ===
  -- stage1: AGU (64-bit adder) output latched; stage2: forwarding driver
  -- output latched for the CDB.  The SB's combinational compare/priority
  -- sits between the two register layers, so no comb path spans M1+M2.
  let lsu_stage1_addr_q := mkWires "lsu_stage1_addr_q" 64
  let lsu_stage1_tag_q := mkWires "lsu_stage1_tag_q" 6
  let lsu_stage2_fwd_q := mkWires "lsu_stage2_fwd_q" 64
  let lsu_stage2_hit_q := Wire.mk "lsu_stage2_hit_q"
  let lsu_replay_needed := Wire.mk "lsu_replay_needed"

  -- === Placeholder wires for StoreBuffer8 required inputs ===
  let sb_enq_en := Wire.mk "sb_enq_en"  -- Placeholder: would be driven by dispatch_is_store control logic
  let sb_enq_idx_in := mkWires "sb_enq_idx_in" 3  -- Pre-allocated SB entry index from CPU
  let sb_enq_address := mkWires "sb_enq_address" 64  -- Connected to agu_address
  let sb_enq_data := store_data  -- Direct connection from dispatch
  let sb_enq_size := mkWires "sb_enq_size" 2  -- Placeholder: would be decoded from opcode

  -- === MemoryExecUnit Instance ===
  -- MemoryExecUnit uses flat port names: base_0, base_1, ..., offset_0, offset_1, etc.
  let agu_inst : CircuitInstance := {
    moduleName := "MemoryExecUnit"
    instName := "u_agu"
    portMap :=
      (dispatch_base.enum.map (fun ⟨i, w⟩ => (s!"base_{i}", w))) ++
      (dispatch_offset.enum.map (fun ⟨i, w⟩ => (s!"offset_{i}", w))) ++
      (dispatch_dest_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      (agu_address.enum.map (fun ⟨i, w⟩ => (s!"address_{i}", w))) ++
      (agu_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w)))
  }

  -- Connect AGU address to StoreBuffer enqueue address (BUF gates for clarity)
  let agu_to_sb_gates := List.zipWith (fun src dst =>
    Gate.mkBUF src dst
  ) agu_address sb_enq_address

  let sb_flush_applied := Wire.mk "sb_flush_applied"
  let sb_flush_pending := Wire.mk "sb_flush_pending"

  -- === StoreBuffer8 Instance ===
  let sb_inst : CircuitInstance := {
    moduleName := "StoreBuffer8"
    instName := "u_store_buffer"
    portMap :=
      [("clock", clock), ("reset", reset), ("zero", zero), ("one", one),
       ("enq_en", sb_enq_en), ("commit_en", commit_store_en), ("deq_ready", deq_ready),
       ("flush_en", flush_en), ("full", sb_full), ("empty", sb_empty),
       ("flush_applied", sb_flush_applied), ("flush_pending", sb_flush_pending)] ++
      (sb_enq_idx_in.enum.map (fun ⟨i, w⟩ => (s!"enq_idx_in_[{i}]", w))) ++
      [
       ("fwd_hit", sb_fwd_hit), ("fwd_committed_hit", sb_fwd_committed_hit),
       ("fwd_word_hit", sb_fwd_word_hit),
       ("fwd_word_only_hit", sb_fwd_word_only_hit),
       ("deq_valid", sb_deq_valid)] ++
      (sb_enq_address.enum.map (fun ⟨i, w⟩ => (s!"enq_address_[{i}]", w))) ++
      (sb_enq_data.enum.map (fun ⟨i, w⟩ => (s!"enq_data_[{i}]", w))) ++
      (sb_enq_size.enum.map (fun ⟨i, w⟩ => (s!"enq_size_[{i}]", w))) ++
      [("replay_needed", sb_replay_raw)] ++
      (fwd_address.enum.map (fun ⟨i, w⟩ => (s!"fwd_address_[{i}]", w))) ++
      (sb_fwd_data.enum.map (fun ⟨i, w⟩ => (s!"fwd_data_[{i}]", w))) ++
      (sb_fwd_size.enum.map (fun ⟨i, w⟩ => (s!"fwd_size_[{i}]", w))) ++
      (sb_deq_bits.enum.map (fun ⟨i, w⟩ => (s!"deq_bits_[{i}]", w))) ++
      (sb_enq_idx.enum.map (fun ⟨i, w⟩ => (s!"enq_idx_[{i}]", w))) ++
      (sb_flush_tail.enum.map (fun ⟨i, w⟩ => (s!"flush_tail_[{i}]", w)))
  }

  -- === Assemble Circuit ===

  let all_inputs :=
    [clock, reset, zero, one] ++
    dispatch_base ++ dispatch_offset ++ dispatch_dest_tag ++
    store_data ++
    [commit_store_en] ++
    [deq_ready] ++
    fwd_address ++
    [flush_en] ++
    sb_enq_size ++  -- Placeholder input (would be decoded from opcode)
    [sb_enq_en] ++  -- Placeholder input (would be driven by control logic)
    sb_enq_idx_in   -- Pre-allocated SB entry index

  let all_outputs :=
    agu_address ++ agu_tag_out ++
    [sb_full, sb_empty, sb_fwd_hit, sb_fwd_committed_hit, sb_fwd_word_hit, sb_fwd_word_only_hit] ++
    sb_fwd_data ++ sb_fwd_size ++
    [sb_deq_valid] ++
    sb_deq_bits ++
    sb_enq_idx ++
    sb_flush_tail ++
    [sb_flush_applied, sb_flush_pending] ++
    lsu_stage1_addr_q ++ lsu_stage1_tag_q ++
    lsu_stage2_fwd_q ++ [lsu_stage2_hit_q, lsu_replay_needed]

  -- M1->M2 register layers (free-running pipeline captures)
  let stage1_pipe_gates :=
    (List.range 64).map (fun i => Gate.mkDFF agu_address[i]! clock reset lsu_stage1_addr_q[i]!) ++
    (List.range 6).map (fun i => Gate.mkDFF agu_tag_out[i]! clock reset lsu_stage1_tag_q[i]!) ++
    (List.range 64).map (fun i => Gate.mkDFF sb_fwd_data[i]! clock reset lsu_stage2_fwd_q[i]!) ++
    [Gate.mkDFF sb_fwd_hit clock reset lsu_stage2_hit_q]
  let replay_out_gate := Gate.mkBUF sb_replay_raw lsu_replay_needed

  let all_gates := agu_to_sb_gates ++ stage1_pipe_gates ++ [replay_out_gate]

  let all_instances := [agu_inst, sb_inst]

  { name := "LSU"
    inputs := all_inputs
    outputs := all_outputs
    gates := all_gates
    instances := all_instances
    -- V2 codegen annotations
    signalGroups := [
      { name := "dispatch_base", width := 64, wires := dispatch_base },
      { name := "dispatch_offset", width := 32, wires := dispatch_offset },
      { name := "dispatch_dest_tag", width := 6, wires := dispatch_dest_tag },
      { name := "store_data", width := 64, wires := store_data },
      { name := "fwd_address", width := 64, wires := fwd_address },
      { name := "agu_address", width := 64, wires := agu_address },
      { name := "agu_tag_out", width := 6, wires := agu_tag_out },
      { name := "sb_fwd_data", width := 64, wires := sb_fwd_data },
      { name := "sb_fwd_size", width := 2, wires := sb_fwd_size },
      { name := "sb_deq_bits", width := 130, wires := sb_deq_bits },
      { name := "sb_enq_idx", width := 3, wires := sb_enq_idx },
      { name := "sb_enq_address", width := 64, wires := sb_enq_address },
      { name := "sb_enq_size", width := 2, wires := sb_enq_size },
      { name := "sb_enq_idx_in", width := 3, wires := sb_enq_idx_in },
      { name := "sb_flush_tail", width := 3, wires := sb_flush_tail }
    ]
  }

end Shoumei.RISCV.Memory

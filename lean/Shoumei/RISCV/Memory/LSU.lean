/-
RISCV/Memory/LSU.lean - Load-Store Unit for RV32I Tomasulo CPU

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
  address : UInt32
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
  responseData : UInt32

instance : Inhabited MemoryInterfaceState where
  default := {
    pendingRequest := none
    requestReady := true  -- Assume simple memory always ready
    responseValid := false
    responseData := 0
  }

/-! ## LSU State -/

/-- Load-Store Unit State. -/
structure LSUState where
  /-- Store buffer (8 entries) -/
  storeBuffer : StoreBufferState
  /-- Pending load request (only one load in-flight for MVP) -/
  pendingLoad : Option PendingLoadRequest
  /-- Memory interface state -/
  memoryInterface : MemoryInterfaceState

/-- Create an empty LSU. -/
def LSUState.empty : LSUState :=
  { storeBuffer := StoreBufferState.empty
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

/-- Execute store instruction.

    Enqueues store into store buffer (uncommitted).
    Returns updated state and success status.
-/
def LSUState.executeStore
    (lsu : LSUState)
    (opcode : OpType)
    (base : UInt32)      -- rs1 value (address base)
    (offset : Int)       -- Immediate offset
    (data : UInt32)      -- rs2 value (data to store)
    : LSUState × Bool :=
  -- Calculate effective address
  let addr := calculateMemoryAddress base offset

  -- Determine access size
  let size_fin : Fin 4 := match opcode with
    | .SB => 0  -- Byte
    | .SH => 1  -- Halfword
    | .SW => 2  -- Word
    | _ => 2    -- Default to word

  -- Enqueue into store buffer (uncommitted)
  let (newSB, allocResult) := lsu.storeBuffer.enqueue addr data size_fin

  match allocResult with
  | some _idx =>
      -- Success: store enqueued
      ({ lsu with storeBuffer := newSB }, true)
  | none =>
      -- Failure: store buffer full (stall)
      (lsu, false)

/-- Execute load instruction.

    Checks store buffer for forwarding match first (TSO semantics).
    If match: return forwarded data immediately.
    If no match: issue memory read request.

    Returns (updated state, optional CDB broadcast).
-/
def LSUState.executeLoad
    (lsu : LSUState)
    (opcode : OpType)
    (base : UInt32)      -- rs1 value (address base)
    (offset : Int)       -- Immediate offset
    (dest_tag : Fin 64)  -- Destination physical register
    : LSUState × Option (Fin 64 × UInt32) :=
  -- Cannot accept new load if one is already pending
  if !lsu.canAcceptLoad then
    (lsu, none)
  else
    -- Calculate effective address
    let addr := calculateMemoryAddress base offset

    -- Determine access size and sign extension
    let (size, sign_ext) := match opcode with
      | .LB  => (MemSize.Byte, true)       -- Load byte, sign-extend
      | .LH  => (MemSize.Halfword, true)   -- Load halfword, sign-extend
      | .LW  => (MemSize.Word, false)      -- Load word (no extension needed)
      | .LBU => (MemSize.Byte, false)      -- Load byte unsigned
      | .LHU => (MemSize.Halfword, false)  -- Load halfword unsigned
      | _ => (MemSize.Word, false)         -- Invalid (shouldn't happen)

    -- Check store buffer for forwarding match (TSO: youngest match wins)
    match lsu.storeBuffer.forwardCheck addr with
    | some fwd_data =>
        -- FORWARDING HIT: Return data immediately, broadcast on CDB
        let processed_data := processLoadResponse fwd_data size sign_ext
        (lsu, some (dest_tag, processed_data))

    | none =>
        -- FORWARDING MISS: Issue memory read request
        let pendingReq : PendingLoadRequest := {
          address := addr
          size := size
          sign_extend := sign_ext
          dest_tag := dest_tag
        }
        let newLSU := { lsu with pendingLoad := some pendingReq }
        -- Memory request will be handled by memory interface (next cycle)
        (newLSU, none)

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
    : LSUState × Option (UInt32 × UInt32 × Fin 4) :=
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
    (mem_data : UInt32)
    : LSUState × Option (Fin 64 × UInt32) :=
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
    - commit_store_idx[2:0]: Store buffer index to commit
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
  let dispatch_base := mkWires "dispatch_base_" 32
  let dispatch_offset := mkWires "dispatch_offset_" 32
  let dispatch_dest_tag := mkWires "dispatch_dest_tag_" 6
  let store_data := mkWires "store_data_" 32

  -- === Store Commit Interface (from ROB) ===
  let commit_store_en := Wire.mk "commit_store_en"
  let commit_store_idx := mkWires "commit_store_idx_" 3

  -- === Memory Interface ===
  let deq_ready := Wire.mk "deq_ready"

  -- === Forwarding Interface ===
  let fwd_address := mkWires "fwd_address_" 32

  -- === Flush Interface ===
  let flush_en := Wire.mk "flush_en"

  -- === AGU (Address Generation Unit) Outputs ===
  let agu_address := mkWires "agu_address_" 32
  let agu_tag_out := mkWires "agu_tag_out_" 6

  -- === Store Buffer Outputs ===
  let sb_full := Wire.mk "sb_full"
  let sb_empty := Wire.mk "sb_empty"
  let sb_fwd_hit := Wire.mk "sb_fwd_hit"
  let sb_fwd_data := mkWires "sb_fwd_data_" 32
  let sb_deq_valid := Wire.mk "sb_deq_valid"
  let sb_deq_bits := mkWires "sb_deq_bits_" 66
  let sb_enq_idx := mkWires "sb_enq_idx_" 3

  -- === Placeholder wires for StoreBuffer8 required inputs ===
  let sb_enq_en := Wire.mk "sb_enq_en"  -- Placeholder: would be driven by dispatch_is_store control logic
  let sb_enq_address := mkWires "sb_enq_address_" 32  -- Connected to agu_address
  let sb_enq_data := store_data  -- Direct connection from dispatch
  let sb_enq_size := mkWires "sb_enq_size_" 2  -- Placeholder: would be decoded from opcode

  -- === MemoryExecUnit Instance ===
  let agu_inst : CircuitInstance := {
    moduleName := "MemoryExecUnit"
    instName := "u_agu"
    portMap :=
      (dispatch_base.map (fun w => ("base", w))) ++
      (dispatch_offset.map (fun w => ("offset", w))) ++
      (dispatch_dest_tag.map (fun w => ("dest_tag", w))) ++
      [("zero", zero)] ++
      (agu_address.map (fun w => ("address", w))) ++
      (agu_tag_out.map (fun w => ("tag_out", w)))
  }

  -- Connect AGU address to StoreBuffer enqueue address (BUF gates for clarity)
  let agu_to_sb_gates := List.zipWith (fun src dst =>
    Gate.mkBUF src dst
  ) agu_address sb_enq_address

  -- === StoreBuffer8 Instance ===
  let sb_inst : CircuitInstance := {
    moduleName := "StoreBuffer8"
    instName := "u_store_buffer"
    portMap :=
      [("clock", clock), ("reset", reset), ("zero", zero), ("one", one),
       ("enq_en", sb_enq_en), ("commit_en", commit_store_en), ("deq_ready", deq_ready),
       ("flush_en", flush_en), ("full", sb_full), ("empty", sb_empty),
       ("fwd_hit", sb_fwd_hit), ("deq_valid", sb_deq_valid)] ++
      (sb_enq_address.map (fun w => ("enq_address", w))) ++
      (sb_enq_data.map (fun w => ("enq_data", w))) ++
      (sb_enq_size.map (fun w => ("enq_size", w))) ++
      (commit_store_idx.map (fun w => ("commit_idx", w))) ++
      (fwd_address.map (fun w => ("fwd_address", w))) ++
      (sb_fwd_data.map (fun w => ("fwd_data", w))) ++
      (sb_deq_bits.map (fun w => ("deq_bits", w))) ++
      (sb_enq_idx.map (fun w => ("enq_idx", w)))
  }

  -- === Assemble Circuit ===

  let all_inputs :=
    [clock, reset, zero, one] ++
    dispatch_base ++ dispatch_offset ++ dispatch_dest_tag ++
    store_data ++
    [commit_store_en] ++ commit_store_idx ++
    [deq_ready] ++
    fwd_address ++
    [flush_en] ++
    sb_enq_size ++  -- Placeholder input (would be decoded from opcode)
    [sb_enq_en]     -- Placeholder input (would be driven by control logic)

  let all_outputs :=
    agu_address ++ agu_tag_out ++
    [sb_full, sb_empty, sb_fwd_hit] ++
    sb_fwd_data ++
    [sb_deq_valid] ++
    sb_deq_bits ++
    sb_enq_idx

  let all_gates := agu_to_sb_gates

  let all_instances := [agu_inst, sb_inst]

  { name := "LSU"
    inputs := all_inputs
    outputs := all_outputs
    gates := all_gates
    instances := all_instances
  }

end Shoumei.RISCV.Memory

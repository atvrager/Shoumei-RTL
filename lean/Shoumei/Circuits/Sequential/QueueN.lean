/-
Circuits/Sequential/QueueN.lean - Multi-Entry Circular Buffer Queue

Extends the single-entry Queue to support arbitrary depth N using a circular buffer
implementation with head/tail pointers.

This is needed for:
- Free List (Phase 3): 64-entry queue of physical register tags
- Reservation Stations (Phase 4): Multiple entry queues for instructions
- Reorder Buffer (Phase 6): Large circular buffer for in-order commit

Design:
- Storage: N registers, each width bits
- Head pointer: ceil(log2(N)) bits (points to next dequeue position)
- Tail pointer: ceil(log2(N)) bits (points to next enqueue position)
- Count register: ceil(log2(N))+1 bits (current number of entries)
- Empty when count == 0
- Full when count == N
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.Queue
import Shoumei.Circuits.Sequential.Register
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Circuits.Combinational.RippleCarryAdder

namespace Shoumei.Circuits.Sequential

open Shoumei

/-!
## Circular Buffer State

Extends QueueState to track head/tail pointers for efficient enqueue/dequeue.
-/

structure CircularBufferState (α : Type) (n : Nat) where
  storage : Fin n → Option α  -- Circular array storage
  head : Fin n                -- Read pointer (next dequeue)
  tail : Fin n                -- Write pointer (next enqueue)
  count : Nat                 -- Current number of entries
  h_count : count ≤ n         -- Invariant: count never exceeds capacity

namespace CircularBufferState

-- Is the circular buffer empty?
def isEmpty {α : Type} {n : Nat} (cb : CircularBufferState α n) : Bool :=
  cb.count == 0

-- Is the circular buffer full?
def isFull {α : Type} {n : Nat} (cb : CircularBufferState α n) : Bool :=
  cb.count >= n

-- Enqueue operation (add to tail, advance tail pointer)
def enqueue {α : Type} {n : Nat} (cb : CircularBufferState α n) (data : α)
    : CircularBufferState α n :=
  if h : cb.isFull then
    cb  -- No-op if full
  else
    let newStorage := fun i => if i = cb.tail then some data else cb.storage i
    let newTail := if h' : cb.tail.val + 1 < n then
                     ⟨cb.tail.val + 1, h'⟩
                   else
                     ⟨0, Nat.zero_lt_of_lt cb.tail.isLt⟩
    let newCount := cb.count + 1
    { storage := newStorage
      head := cb.head
      tail := newTail
      count := newCount
      h_count := by
        simp [isFull] at h
        omega }

-- Dequeue operation (remove from head, advance head pointer)
def dequeue {α : Type} {n : Nat} (cb : CircularBufferState α n)
    : CircularBufferState α n × Option α :=
  if h : cb.isEmpty then
    (cb, none)  -- Empty buffer
  else
    let data := cb.storage cb.head
    let newStorage := fun i => if i = cb.head then none else cb.storage i
    let newHead := if h' : cb.head.val + 1 < n then
                     ⟨cb.head.val + 1, h'⟩
                   else
                     ⟨0, Nat.zero_lt_of_lt cb.head.isLt⟩
    let newCount := cb.count - 1
    let newCb : CircularBufferState α n :=
      { storage := newStorage
        head := newHead
        tail := cb.tail
        count := newCount
        h_count := by
          simp [isEmpty] at h
          have : cb.count > 0 := by omega
          have : cb.count ≤ n := cb.h_count
          omega }
    (newCb, data)

-- Peek at head without removing
def peek {α : Type} {n : Nat} (cb : CircularBufferState α n) : Option α :=
  if cb.isEmpty then none else cb.storage cb.head

-- Create empty circular buffer with given depth
def empty {α : Type} (n : Nat) (h : n > 0) : CircularBufferState α n :=
  { storage := fun _ => none
    head := ⟨0, h⟩
    tail := ⟨0, h⟩
    count := 0
    h_count := Nat.zero_le n }

end CircularBufferState

/-!
## QueueN Circuit Definition

For code generation, we need a structural representation of multi-entry queues.
-/

structure QueueNCircuit where
  name : String
  width : Nat        -- Bit width of data
  depth : Nat        -- Number of entries (must be power of 2 for simple addressing)
  deriving Repr

-- Convenience constructor for multi-entry queues
def mkQueueN (depth width : Nat) : QueueNCircuit :=
  { name := s!"Queue{depth}_{width}", width := width, depth := depth }

-- Specific instances for common depths
def mkQueueN2 (width : Nat) : QueueNCircuit := mkQueueN 2 width
def mkQueueN4 (width : Nat) : QueueNCircuit := mkQueueN 4 width
def mkQueueN8 (width : Nat) : QueueNCircuit := mkQueueN 8 width
def mkQueueN16 (width : Nat) : QueueNCircuit := mkQueueN 16 width
def mkQueueN32 (width : Nat) : QueueNCircuit := mkQueueN 32 width
def mkQueueN64 (width : Nat) : QueueNCircuit := mkQueueN 64 width

-- Specific instance for Free List (Phase 3) - 64-entry, 6-bit wide
def mkQueue64x6 : QueueNCircuit := mkQueueN64 6

/-!
## Structural QueueN Implementation

Build an N-entry Queue from:
- N storage registers (each `width` bits)
- Head pointer register (ptrWidth bits)
- Tail pointer register (ptrWidth bits)
- Count register (ptrWidth+1 bits to represent 0..N)
- Decoder for write address (N-way one-hot)
- MUX for read data (N:1 selection)
- Incrementers for pointers (with wraparound)
- Comparators for empty/full detection

This is deferred to code generation as it requires complex structural composition.
For now, we define the behavioral semantics above.
-/

-- Helper: Compute log2 ceiling (number of bits needed for N values)
private def log2Ceil (n : Nat) : Nat :=
  if n <= 1 then 0
  else Nat.log2 n + (if 2^(Nat.log2 n) < n then 1 else 0)

/--
Build a structural N-entry Queue using circular buffer logic.

Components:
1. Storage: N registers, each `width` bits
2. Pointers: head, tail (log2(N) bits), count (log2(N)+1 bits)
3. Write Logic: Decoder(tail) & enq_fire
4. Read Logic: MuxTree(storage, head)
5. Pointer Logic: Adders for head, tail, count
-/
def mkQueueNStructural (depth width : Nat) : Circuit :=
  let name := s!"Queue{depth}_{width}"
  let ptrWidth := log2Ceil depth
  let countWidth := log2Ceil (depth + 1)

  -- Inputs
  let enq_data := (List.range width).map (fun i => Wire.mk s!"enq_data_{i}")
  let enq_valid := Wire.mk "enq_valid"
  let deq_ready := Wire.mk "deq_ready"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"   -- Constant 0
  let one := Wire.mk "one"     -- Constant 1

  -- Outputs
  let enq_ready := Wire.mk "enq_ready"
  let deq_data := (List.range width).map (fun i => Wire.mk s!"deq_data_{i}")
  let deq_valid := Wire.mk "deq_valid"

  -- Pointer Registers
  let head := (List.range ptrWidth).map (fun i => Wire.mk s!"head_{i}")
  let head_next := (List.range ptrWidth).map (fun i => Wire.mk s!"head_next_{i}")
  let tail := (List.range ptrWidth).map (fun i => Wire.mk s!"tail_{i}")
  let tail_next := (List.range ptrWidth).map (fun i => Wire.mk s!"tail_next_{i}")
  let count := (List.range countWidth).map (fun i => Wire.mk s!"count_{i}")
  let count_next := (List.range countWidth).map (fun i => Wire.mk s!"count_next_{i}")

  -- Storage Registers
  let storage := (List.range depth).map (fun i =>
    (List.range width).map (fun j => Wire.mk s!"reg{i}_b{j}"))
  let storage_next := (List.range depth).map (fun i =>
    (List.range width).map (fun j => Wire.mk s!"reg{i}_next_b{j}"))

  -- Handshaking and Control Signals
  let full := Wire.mk "full"
  let empty := Wire.mk "empty"
  let enq_fire := Wire.mk "enq_fire"
  let deq_fire := Wire.mk "deq_fire"

  -- Constant Vectors
  let _zero_vec_ptr := (List.range ptrWidth).map (fun _ => zero)
  let one_vec_ptr := one :: (List.range (ptrWidth - 1)).map (fun _ => zero)
  let _zero_vec_count := (List.range countWidth).map (fun _ => zero)
  let one_vec_count := one :: (List.range (countWidth - 1)).map (fun _ => zero)

  -- 1. Full/Empty Detection (Simplified: use count)
  -- For depth=64, full if count == 64 (binary 1000000), empty if count == 0
  -- We'll implement this using equality checks or just checking bits if depth is power of 2
  -- depth = 2^ptrWidth
  let empty_gates := (List.range countWidth).foldl (fun (gs, prev) i =>
    let bit_not := Wire.mk s!"count_not_{i}"
    let and_out := if i == countWidth - 1 then empty else Wire.mk s!"count_empty_and_{i}"
    let n_gs := gs ++ [Gate.mkNOT (count.get! i) bit_not]
    let a_gs := n_gs ++ [Gate.mkAND prev bit_not and_out]
    (a_gs, and_out)
  ) ([], one) -- Start with one for AND chain

  -- Full detection: count == depth
  -- If depth = 2^ptrWidth, then depth is 1 followed by ptrWidth zeros in countWidth-bit binary
  let full_gates := (List.range countWidth).foldl (fun (gs, prev) i =>
    let bit_val := count.get! i
    let _target_bit := if i == ptrWidth then one else zero
    let check_bit := Wire.mk s!"full_check_bit_{i}"
    let and_out := if i == countWidth - 1 then full else Wire.mk s!"full_and_{i}"
    let check_gate := if i == ptrWidth then Gate.mkBUF bit_val check_bit
                      else Gate.mkNOT bit_val check_bit
    let n_gs := gs ++ [check_gate]
    let a_gs := n_gs ++ [Gate.mkAND prev check_bit and_out]
    (a_gs, and_out)
  ) ([], one)

  let handshaking_gates := [
    Gate.mkNOT full enq_ready,
    Gate.mkNOT empty deq_valid,
    Gate.mkAND enq_valid enq_ready enq_fire,
    Gate.mkAND deq_ready deq_valid deq_fire
  ]

  -- 2. Pointer Incrementers
  let head_inc := (List.range ptrWidth).map (fun i => Wire.mk s!"head_inc_{i}")
  let head_carries := (List.range (ptrWidth + 1)).map (fun i => Wire.mk s!"head_c_{i}")
  let head_inc_gates := [Gate.mkBUF one (head_carries.get! 0)] ++
    Shoumei.Circuits.Combinational.buildFullAdderChain head one_vec_ptr head_carries head_inc "head_ptr_"

  let tail_inc := (List.range ptrWidth).map (fun i => Wire.mk s!"tail_inc_{i}")
  let tail_carries := (List.range (ptrWidth + 1)).map (fun i => Wire.mk s!"tail_c_{i}")
  let tail_inc_gates := [Gate.mkBUF one (tail_carries.get! 0)] ++
    Shoumei.Circuits.Combinational.buildFullAdderChain tail one_vec_ptr tail_carries tail_inc "tail_ptr_"

  let count_inc := (List.range countWidth).map (fun i => Wire.mk s!"count_inc_{i}")
  let count_carries := (List.range (countWidth + 1)).map (fun i => Wire.mk s!"count_inc_c_{i}")
  let count_inc_gates := [Gate.mkBUF one (count_carries.get! 0)] ++
    Shoumei.Circuits.Combinational.buildFullAdderChain count one_vec_count count_carries count_inc "count_inc_"

  let count_dec := (List.range countWidth).map (fun i => Wire.mk s!"count_dec_{i}")
  let count_dec_carries := (List.range (countWidth + 1)).map (fun i => Wire.mk s!"count_dec_c_{i}")
  -- count - 1 = count + (~1) + 1
  let one_vec_count_inv := (List.range countWidth).map (fun i => Wire.mk s!"one_vec_count_inv_{i}")
  let one_vec_count_inv_gates := (List.range countWidth).map (fun i =>
    Gate.mkNOT (one_vec_count.get! i) (one_vec_count_inv.get! i))
  let count_dec_gates := one_vec_count_inv_gates ++ [Gate.mkBUF one (count_dec_carries.get! 0)] ++
    Shoumei.Circuits.Combinational.buildFullAdderChain count one_vec_count_inv count_dec_carries count_dec "count_dec_"

  -- 3. Next Value MUXes for Pointers
  let head_next_gates := (List.range ptrWidth).map (fun i =>
    Gate.mkMUX (head.get! i) (head_inc.get! i) deq_fire (head_next.get! i))
  let tail_next_gates := (List.range ptrWidth).map (fun i =>
    Gate.mkMUX (tail.get! i) (tail_inc.get! i) enq_fire (tail_next.get! i))

  let count_hold := (List.range countWidth).map (fun i => Wire.mk s!"count_hold_{i}")
  let count_hold_gates := (List.range countWidth).map (fun i =>
    Gate.mkMUX (count.get! i) (count_inc.get! i) enq_fire (count_hold.get! i))
  let count_next_gates := (List.range countWidth).map (fun i =>
    Gate.mkMUX (count_hold.get! i) (count_dec.get! i) deq_fire (count_next.get! i))

  -- 4. Pointer DFFs
  let head_dffs := (List.range ptrWidth).map (fun i =>
    Gate.mkDFF (head_next.get! i) clock reset (head.get! i))
  let tail_dffs := (List.range ptrWidth).map (fun i =>
    Gate.mkDFF (tail_next.get! i) clock reset (tail.get! i))
  let count_dffs := (List.range countWidth).map (fun i =>
    Gate.mkDFF (count_next.get! i) clock reset (count.get! i))

  -- 5. Storage Logic
  -- Write Decoder
  let decoder := Shoumei.Circuits.Combinational.mkDecoder ptrWidth
  let write_sel := (List.range depth).map (fun i => Wire.mk s!"write_sel_{i}")
  let decoder_gates := decoder.inline (fun w =>
    if w.name.startsWith "in" then
      let i_str := w.name.drop 2
      match i_str.toNat? with
      | some idx => tail.get! idx
      | none => w
    else if w.name.startsWith "out" then
      let i_str := w.name.drop 3
      match i_str.toNat? with
      | some idx => write_sel.get! idx
      | none => w
    else
      Wire.mk s!"decoder_{w.name}"
  )

  -- Write Enables: enq_fire && write_sel[i]
  let write_en := (List.range depth).map (fun i => Wire.mk s!"write_en_{i}")
  let write_en_gates := (List.range depth).map (fun i =>
    Gate.mkAND enq_fire (write_sel.get! i) (write_en.get! i))

  -- Storage Next MUXes: storage_next[i] = write_en[i] ? enq_data : storage[i]
  let storage_next_gates := (List.flatten (List.range depth |>.map (fun i =>
    (List.range width).map (fun j =>
      Gate.mkMUX (storage.get! i |>.get! j) (enq_data.get! j) (write_en.get! i) (storage_next.get! i |>.get! j)
    )
  )))

  -- Storage DFFs
  let storage_dffs := (List.flatten (List.range depth |>.map (fun i =>
    (List.range width).map (fun j =>
      Gate.mkDFF (storage_next.get! i |>.get! j) clock reset (storage.get! i |>.get! j)
    )
  )))

  -- 6. Read MUX (MuxTree)
  let mux_tree := Shoumei.Circuits.Combinational.mkMuxTree depth width
  let read_data_internal := (List.range width).map (fun i => Wire.mk s!"read_data_int_{i}")
  let mux_gates := mux_tree.inline (fun w =>
    -- Expected names in MuxTree: in{i}_b{j}, sel{k}, out{j}
    if w.name.startsWith "in" then
      let parts := w.name.drop 2 |>.splitOn "_b"
      match parts with
      | [i_str, j_str] => match i_str.toNat?, j_str.toNat? with
                          | some idx, some bit => storage.get! idx |>.get! bit
                          | _, _ => w
      | _ => w
    else if w.name.startsWith "sel" then
      match w.name.drop 3 |>.toNat? with
      | some idx => head.get! idx
      | none => w
    else if w.name.startsWith "out" then
      match w.name.drop 3 |>.toNat? with
      | some idx => read_data_internal.get! idx
      | none => w
    else
      Wire.mk s!"muxtree_{w.name}"
  )

  -- Connect internal read data to output
  let output_connect_gates := (List.range width).map (fun i =>
    Gate.mkBUF (read_data_internal.get! i) (deq_data.get! i))

  { name := name
    inputs := enq_data ++ [enq_valid, deq_ready, clock, reset, zero, one]
    outputs := [enq_ready] ++ deq_data ++ [deq_valid]
    gates := empty_gates.1 ++ full_gates.1 ++ handshaking_gates ++
             head_inc_gates ++ tail_inc_gates ++ count_inc_gates ++ count_dec_gates ++
             head_next_gates ++ tail_next_gates ++ count_hold_gates ++ count_next_gates ++
             head_dffs ++ tail_dffs ++ count_dffs ++
             decoder_gates ++ write_en_gates ++ storage_next_gates ++ storage_dffs ++
             mux_gates ++ output_connect_gates
  }

-- TODO: Implement mkQueueNStructural similar to mkQueue1Structural
-- This will require:
-- 1. Storage register array (N × width bits)
-- 2. Pointer registers (2 × ptrWidth bits)
-- 3. Count register (ptrWidth+1 bits)
-- 4. Address decoder for write enable
-- 5. MUX tree for read data
-- 6. Increment/wraparound logic for pointers
-- 7. Control logic for ready/valid handshaking

end Shoumei.Circuits.Sequential

/-
RISCV/Memory/StoreBufferProofs.lean - Structural Proofs for StoreBuffer8

Verifies the structural properties of the StoreBuffer8 circuit:
- Correct port counts (inputs, outputs)
- Correct instance count and building block usage
- Correct gate count
-/

import Shoumei.DSL
import Shoumei.RISCV.Memory.StoreBuffer

namespace Shoumei.RISCV.Memory.StoreBufferProofs

open Shoumei
open Shoumei.RISCV.Memory

/-! ## Structural Proofs -/

/-- StoreBuffer8 has correct number of inputs:
    clock(1) + reset(1) + zero(1) + one(1) +
    enq_en(1) + enq_idx_in(3) + enq_address(32) + enq_data(64) + enq_size(2) +
    commit_en(1) +
    deq_ready(1) +
    fwd_address(32) +
    flush_en(1) = 141 -/
theorem storebuffer8_input_count : mkStoreBuffer8.inputs.length = 141 := by native_decide

/-- StoreBuffer8 has correct number of outputs:
    full(1) + empty(1) + enq_idx(3) + flush_tail(3) +
    deq_valid(1) + deq_bits(98) +
    fwd_hit(1) + fwd_committed_hit(1) + fwd_word_hit(1) + fwd_word_only_hit(1) +
    fwd_data(64) + fwd_size(2) = 177 -/
theorem storebuffer8_output_count : mkStoreBuffer8.outputs.length = 177 := by native_decide

/-- StoreBuffer8 uses 49 verified submodule instances:
    - 8 x Register98 (entry storage)
    - 1 x QueuePointer_3 (head pointer)
    - 2 x QueuePointerLoadable_3 (tail/commit pointers)
    - 1 x QueueCounterLoadable_4 (entry count)
    - 3 x Decoder3 (enqueue/head/commit one-hot decode)
    - 8 x EqualityComparator32 (address matching for forwarding)
    - 1 x Popcount8 (flush recovery)
    - 19 x DFlipFlop (16 valid/committed + 3 pending commit)
    - 2 x Mux8x64 (fwd data, deq data)
    - 1 x Mux8x32 (deq address)
    - 2 x Mux8x2 (fwd size, deq size)
    - 1 x PriorityArbiter8 (youngest-match selection) -/
theorem storebuffer8_instance_count : mkStoreBuffer8.instances.length = 49 := by native_decide

/-- StoreBuffer8 gate count: 1625 combinational gates -/
theorem storebuffer8_gate_count : mkStoreBuffer8.gates.length = 1625 := by native_decide

/-! ## Building Block Verification -/

/-- StoreBuffer8 Building Block Dependencies:
    StoreBuffer8's composition rests on these modules, each verified by its own
    proof. -/
def storebuffer8_dependencies : List String := [
  "Register98",              -- Entry storage (98-bit register x 8)
  "DFlipFlop",               -- Valid/committed bitmaps (16 DFFs)
  "QueuePointer_3",          -- Head pointer (3-bit wrapping counter)
  "QueuePointerLoadable_3",  -- Tail/commit pointers (loadable for flush)
  "QueueCounterLoadable_4",  -- Entry count (loadable for flush recovery)
  "Decoder3",                -- Enqueue/head/commit one-hot decode (3→8)
  "EqualityComparator32",    -- Address matching (32-bit equality comparator x 8)
  "Popcount8",               -- Flush recovery (count surviving entries)
  "Mux8x64",                -- Data selection (8:1 mux, 64 bits x 2)
  "Mux8x32",                -- Data selection (8:1 mux, 32 bits x 1)
  "Mux8x2",                 -- Size selection (8:1 mux, 2 bits x 2)
  "PriorityArbiter8"         -- Youngest-match priority selection
]

/-- All StoreBuffer8 instances use verified building blocks -/
theorem storebuffer8_uses_verified_blocks :
  ∀ inst ∈ mkStoreBuffer8.instances,
    storebuffer8_dependencies.contains inst.moduleName := by
  native_decide

/-- All instance names in StoreBuffer8 are unique -/
theorem storebuffer8_unique_instances :
  let names := mkStoreBuffer8.instances.map (fun inst => inst.instName)
  names.length == names.eraseDups.length := by native_decide

end Shoumei.RISCV.Memory.StoreBufferProofs

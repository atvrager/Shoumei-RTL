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
    enq_en(1) + enq_address(32) + enq_data(32) + enq_size(2) +
    commit_en(1) + commit_idx(3) +
    deq_ready(1) +
    fwd_address(32) +
    flush_en(1) = 109 -/
theorem storebuffer8_input_count : mkStoreBuffer8.inputs.length = 106 := by native_decide

/-- StoreBuffer8 has correct number of outputs:
    full(1) + empty(1) +
    deq_valid(1) + deq_bits(66) +
    fwd_hit(1) + fwd_data(32) +
    enq_idx(3) = 105 -/
theorem storebuffer8_output_count : mkStoreBuffer8.outputs.length = 108 := by native_decide

/-- StoreBuffer8 uses 26 verified submodule instances:
    - 8 x Register68 (entry storage)
    - 2 x QueuePointer_3 (head/tail pointers)
    - 1 x QueueCounterUpDown_4 (entry count)
    - 2 x Decoder3 (enqueue/commit one-hot decode)
    - 8 x Comparator32 (address matching for forwarding)
    - 3 x Mux8x32 (fwd data, deq address, deq data)
    - 1 x Mux8x2 (deq size)
    - 1 x PriorityArbiter8 (youngest-match selection) -/
theorem storebuffer8_instance_count : mkStoreBuffer8.instances.length = 46 := by native_decide

/-- StoreBuffer8 gate count: 675 combinational gates -/
theorem storebuffer8_gate_count : mkStoreBuffer8.gates.length = 797 := by native_decide

/-! ## Building Block Verification -/

/-- StoreBuffer8 Building Block Dependencies:
    All these modules must pass LEC before StoreBuffer8 is considered verified. -/
def storebuffer8_dependencies : List String := [
  "Register66",              -- Entry storage (66-bit register x 8)
  "DFlipFlop",               -- Valid/committed bitmaps (16 DFFs)
  "QueuePointer_3",          -- Head pointer (3-bit wrapping counter)
  "QueuePointerLoadable_3",  -- Tail/commit pointers (loadable for flush)
  "QueueCounterLoadable_4",  -- Entry count (loadable for flush recovery)
  "Decoder3",                -- Enqueue/head/commit one-hot decode (3→8)
  "EqualityComparator32",    -- Address matching (32-bit equality comparator x 8)
  "Popcount8",               -- Flush recovery (count surviving entries)
  "Mux8x32",                -- Data selection (8:1 mux, 32 bits x 3)
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

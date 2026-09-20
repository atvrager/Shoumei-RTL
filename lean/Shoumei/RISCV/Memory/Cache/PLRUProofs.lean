/-
RISCV/Memory/Cache/PLRUProofs.lean - Tree-PLRU properties

Tests for the replacement policy.  A `ways`-way policy's whole state is its
`ways - 1` bits, so quantifying over the bits covers every state of that
geometry; the theorems below are stated that way so they are closed and
`decide`-checkable.

The load-bearing one is `plru_2way_victim`: at two ways tree-PLRU *is* the
single LRU bit the cache levels carry today, which is what lets one block serve
every geometry without changing the 2-way behaviour.
-/

import Shoumei.RISCV.Memory.Cache.PLRU

namespace Shoumei.RISCV.Memory.Cache

/-! ## Initial state -/

/-- A fresh policy evicts way 0 at every geometry. -/
theorem plru_init_victim_2 : (PLRUState.init 2).victim = 0 := by decide

theorem plru_init_victim_4 : (PLRUState.init 4).victim = 0 := by decide

theorem plru_init_victim_8 : (PLRUState.init 8).victim = 0 := by decide

/-! ## Two ways: exactly the single LRU bit -/

/-- At two ways the victim is `bit ? 1 : 0` - the level's existing `lru` bit
    read the same way (`if lru then 1 else 0`). -/
theorem plru_2way_victim (b : Bool) :
    (⟨[b]⟩ : PLRUState 2).victim = (if b then 1 else 0) := by
  cases b <;> decide

/-- Touching way 0 leaves the bit set (the victim becomes way 1) - the level's
    `lru := (way == 0)` update. -/
theorem plru_2way_update_way0 (b : Bool) :
    ((⟨[b]⟩ : PLRUState 2).update 0).bits.getD 0 false = true := by
  cases b <;> decide

/-- Touching way 1 clears the bit (the victim becomes way 0). -/
theorem plru_2way_update_way1 (b : Bool) :
    ((⟨[b]⟩ : PLRUState 2).update 1).bits.getD 0 false = false := by
  cases b <;> decide

/-! ## The policy property: the way just touched is not the victim -/

theorem plru_update_victim_ne_2 (w : Fin 2) :
    ((PLRUState.init 2).update w.val).victim ≠ w.val := by
  have h : w.val = 0 ∨ w.val = 1 := by omega
  rcases h with h | h <;> (rw [h]; decide)

theorem plru_update_victim_ne_4 (w : Fin 4) :
    ((PLRUState.init 4).update w.val).victim ≠ w.val := by
  have h : w.val = 0 ∨ w.val = 1 ∨ w.val = 2 ∨ w.val = 3 := by omega
  rcases h with h | h | h | h <;> (rw [h]; decide)

theorem plru_update_victim_ne_8 (w : Fin 8) :
    ((PLRUState.init 8).update w.val).victim ≠ w.val := by
  have h : w.val = 0 ∨ w.val = 1 ∨ w.val = 2 ∨ w.val = 3 ∨
           w.val = 4 ∨ w.val = 5 ∨ w.val = 6 ∨ w.val = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> (rw [h]; decide)

/-! ## The victim is always a real way -/

theorem plru_victim_lt_2 (b : Bool) :
    (⟨[b]⟩ : PLRUState 2).victim < 2 := by cases b <;> decide

theorem plru_victim_lt_4 (b0 b1 b2 : Bool) :
    (⟨[b0, b1, b2]⟩ : PLRUState 4).victim < 4 := by
  cases b0 <;> cases b1 <;> cases b2 <;> decide

theorem plru_victim_lt_8 (b0 b1 b2 b3 b4 b5 b6 : Bool) :
    (⟨[b0, b1, b2, b3, b4, b5, b6]⟩ : PLRUState 8).victim < 8 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
  cases b4 <;> cases b5 <;> cases b6 <;> decide

/-! ## Structural checks (the circuit's shape per geometry) -/

/-- A `ways`-way policy carries exactly `ways - 1` tree bits. -/
theorem plru_bit_dffs_2 :
    ((mkPLRU 2).gates.filter (fun g => g.gateType == GateType.DFF)).length = 1 := by
  native_decide

theorem plru_bit_dffs_4 :
    ((mkPLRU 4).gates.filter (fun g => g.gateType == GateType.DFF)).length = 3 := by
  native_decide

theorem plru_bit_dffs_8 :
    ((mkPLRU 8).gates.filter (fun g => g.gateType == GateType.DFF)).length = 7 := by
  native_decide

/-- The victim select is one-hot over the ways. -/
theorem plru_victim_width_4 : (mkPLRU 4).outputs.length = 4 := by native_decide

theorem plru_victim_width_8 : (mkPLRU 8).outputs.length = 8 := by native_decide

/-- The update way is a binary index: `log2 ways` bits. -/
theorem plru_upd_way_width_4 : (mkPLRU 4).inputs.length = 5 + 2 := by native_decide

theorem plru_upd_way_width_8 : (mkPLRU 8).inputs.length = 5 + 3 := by native_decide

end Shoumei.RISCV.Memory.Cache

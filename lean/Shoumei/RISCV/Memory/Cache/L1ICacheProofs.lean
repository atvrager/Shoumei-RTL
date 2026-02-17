/-
RISCV/Memory/Cache/L1ICacheProofs.lean - L1I Cache Proofs

Behavioral proofs for the L1I cache model.
-/

import Shoumei.RISCV.Memory.Cache.L1ICache

namespace Shoumei.RISCV.Memory.Cache

/-! ## Behavioral Proofs -/

/-- Looking up an address after refilling that same address's line returns the correct word. -/
theorem lookup_after_refill (s : L1ICacheState) (addr : UInt32) (lineData : Fin 8 → UInt32) :
    (s.refill addr lineData).lookup addr = some (lineData (extractWordOffset addr)) := by
  simp [L1ICacheState.refill, L1ICacheState.lookup, extractL1IIndex, extractL1ITag, extractWordOffset]

/-- An empty cache always misses. -/
theorem empty_always_misses (addr : UInt32) :
    L1ICacheState.empty.lookup addr = none := by
  simp [L1ICacheState.empty, L1ICacheState.lookup, CacheLine.empty, Inhabited.default]

/-- Invalidating all lines makes all lookups miss. -/
theorem invalidate_all_misses (s : L1ICacheState) (addr : UInt32) :
    s.invalidateAll.lookup addr = none := by
  simp [L1ICacheState.invalidateAll, L1ICacheState.lookup, CacheLine.empty, Inhabited.default]

/-- Refilling one set does not affect a different set. -/
theorem refill_different_set (s : L1ICacheState) (addr1 addr2 : UInt32)
    (lineData : Fin 8 → UInt32)
    (h : extractL1IIndex addr1 ≠ extractL1IIndex addr2) :
    (s.refill addr1 lineData).lookup addr2 = s.lookup addr2 := by
  simp [L1ICacheState.refill, L1ICacheState.lookup]
  have hne : extractL1IIndex addr2 ≠ extractL1IIndex addr1 := Ne.symm h
  simp [hne]

end Shoumei.RISCV.Memory.Cache

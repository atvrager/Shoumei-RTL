/-
RISCV/Memory/Cache/L1DCacheProofs.lean - L1D Cache Proofs

Behavioral proofs for the L1D data cache model.
-/

import Shoumei.RISCV.Memory.Cache.L1DCache

namespace Shoumei.RISCV.Memory.Cache

/-! ## Behavioral Proofs -/

/-- An empty L1D cache always misses on lookup. -/
theorem l1d_empty_always_misses (addr : UInt32) :
    L1DCacheState.empty.lookupData addr = none := by
  simp [L1DCacheState.empty, L1DCacheState.lookupData, L1DCacheState.lookup,
        CacheLine.empty, Inhabited.default]

/-- LRU victim selection is deterministic. -/
theorem l1d_victim_deterministic (s : L1DCacheState) (set : Fin 4) :
    s.victimWay set = (if s.lru set then 1 else 0) := by
  simp [L1DCacheState.victimWay]

/-- Clearing all dirty bits makes no line dirty. -/
theorem l1d_clear_dirty_no_dirty (s : L1DCacheState) (w : Fin 2) (set : Fin 4) :
    (s.clearAllDirty.ways w set).dirty = false := by
  simp [L1DCacheState.clearAllDirty]

/-- Writing to a way sets the dirty bit. -/
theorem l1d_write_sets_dirty (s : L1DCacheState) (way : Fin 2) (addr : UInt32) (val : UInt32) :
    ((s.writeToWay way addr val).ways way (extractL1DIndex addr)).dirty = true := by
  simp [L1DCacheState.writeToWay]

end Shoumei.RISCV.Memory.Cache

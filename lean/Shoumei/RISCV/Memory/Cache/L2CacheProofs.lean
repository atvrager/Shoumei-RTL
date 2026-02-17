/-
RISCV/Memory/Cache/L2CacheProofs.lean - L2 Cache Proofs
-/

import Shoumei.RISCV.Memory.Cache.L2Cache

namespace Shoumei.RISCV.Memory.Cache

/-- An empty L2 cache always misses. -/
theorem l2_empty_always_misses (addr : UInt32) :
    L2CacheState.empty.lookup addr = none := by
  simp [L2CacheState.empty, L2CacheState.lookup, CacheLine.empty, Inhabited.default]

/-- LRU victim selection is deterministic. -/
theorem l2_victim_deterministic (s : L2CacheState) (set : Fin 8) :
    s.victimWay set = (if s.lru set then 1 else 0) := by
  simp [L2CacheState.victimWay]

end Shoumei.RISCV.Memory.Cache

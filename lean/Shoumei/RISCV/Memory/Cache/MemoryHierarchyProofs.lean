/-
RISCV/Memory/Cache/MemoryHierarchyProofs.lean - End-to-end Memory Hierarchy Proofs

Proves key properties across the full L1I + L1D + L2 hierarchy.
-/

import Shoumei.RISCV.Memory.Cache.MemoryHierarchy
import Shoumei.RISCV.Memory.Cache.L1ICacheProofs
import Shoumei.RISCV.Memory.Cache.L1DCacheProofs
import Shoumei.RISCV.Memory.Cache.L2CacheProofs

namespace Shoumei.RISCV.Memory.Cache

/-- After FENCE.I, all L1I lines are invalidated. -/
theorem fence_i_invalidates_l1i (s : MemHierarchyState) (addr : UInt32) :
    (s.executeFenceI).l1i.lookup addr = none := by
  simp [MemHierarchyState.executeFenceI]
  exact invalidate_all_misses _ addr

/-- After FENCE.I, no L1D lines are dirty. -/
theorem fence_i_clears_l1d_dirty (s : MemHierarchyState) (w : Fin 2) (set : Fin 4) :
    ((s.executeFenceI).l1d.ways w set).dirty = false := by
  simp [MemHierarchyState.executeFenceI]
  exact l1d_clear_dirty_no_dirty _ w set

/-- Structural: MemoryHierarchy is a pure hierarchical composition (no gates). -/
theorem memory_hierarchy_no_gates : mkMemoryHierarchy.gates.length = 0 := by native_decide

/-- Structural: MemoryHierarchy has exactly 3 instances (L1I, L1D, L2). -/
theorem memory_hierarchy_instance_count : mkMemoryHierarchy.instances.length = 3 := by native_decide

end Shoumei.RISCV.Memory.Cache

/-
RISCV/Memory/Cache/CachedCPUProofs.lean - CachedCPU Proofs
-/

import Shoumei.RISCV.Memory.Cache.CachedCPU
import Shoumei.RISCV.Config

namespace Shoumei.RISCV.Memory.Cache

open Shoumei.RISCV

/-- CachedCPU is a pure hierarchical composition; `.gates` holds only glue logic:
    5 single gates (stall/ready, ifetch valid, snoop valid, RVVI retire OR)
    + 32 store-snoop address BUFs + 32 store-snoop data BUFs = 69. -/
theorem cached_cpu_gate_count :
    (mkCachedCPU rv32imConfig).gates.length = 69 := by native_decide

/-- CachedCPU has exactly 2 instances (CPU + MemoryHierarchy). -/
theorem cached_cpu_instance_count :
    (mkCachedCPU rv32imConfig).instances.length = 2 := by native_decide

/-- CachedCPU preserves hierarchy. -/
theorem cached_cpu_keeps_hierarchy :
    (mkCachedCPU rv32imConfig).keepHierarchy = true := by native_decide

end Shoumei.RISCV.Memory.Cache

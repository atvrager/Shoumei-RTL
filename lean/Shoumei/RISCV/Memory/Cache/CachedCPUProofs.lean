/-
RISCV/Memory/Cache/CachedCPUProofs.lean - CachedCPU Proofs
-/

import Shoumei.RISCV.Memory.Cache.CachedCPU
import Shoumei.RISCV.Config

namespace Shoumei.RISCV.Memory.Cache

open Shoumei.RISCV

/-- CachedCPU is a pure hierarchical composition; `.gates` holds only glue logic:
    6 single gates (stall/ready, ifetch valid, snoop ready/valid ANDs, RVVI retire OR)
    + 32 store-snoop address BUFs + 32 store-snoop data BUFs = 70. -/
theorem cached_cpu_gate_count :
    (mkCachedCPU rv32imConfig).gates.length = 70 := by native_decide

/-- RV64G has 64-bit store snoop data, so 6 + 32 + 64 = 102 glue gates. -/
theorem cached_cpu_rv64g_gate_count :
    (mkCachedCPU rv64gConfig).gates.length = 102 := by native_decide

/-- CachedCPU has exactly 2 instances (CPU + MemoryHierarchy). -/
theorem cached_cpu_instance_count :
    (mkCachedCPU rv32imConfig).instances.length = 2 := by native_decide

/-- CachedCPU preserves hierarchy. -/
theorem cached_cpu_keeps_hierarchy :
    (mkCachedCPU rv32imConfig).keepHierarchy = true := by native_decide

end Shoumei.RISCV.Memory.Cache

import Shoumei.RISCV.CPUControl

namespace Shoumei.RISCV.Control.CPUControlProofs

open Shoumei.RISCV.Control
open Shoumei.RISCV

-- Stall properties
theorem stall_on_freelist_empty (config : CPUConfig) (op : OpType) :
    generateStall config true false false false false false false true true op = true := by
  simp [generateStall]

theorem stall_on_rob_full (config : CPUConfig) (op : OpType) :
    generateStall config false true false false false false false true true op = true := by
  simp [generateStall]

-- Stage enable properties
theorem flush_disables_all (stall : Bool) :
    generateStageEnables stall true = { fetchEnable := false, decodeEnable := false, renameEnable := false, issueEnable := false } := by
  simp [generateStageEnables]

theorem normal_enables_all :
    generateStageEnables false false = { fetchEnable := true, decodeEnable := true, renameEnable := true, issueEnable := true } := by
  simp [generateStageEnables]

-- Flush detection
theorem misprediction_priority :
    detectFlush true true = FlushReason.BranchMisprediction := by
  simp [detectFlush]

theorem no_flush_when_clear :
    detectFlush false false = FlushReason.None := by
  simp [detectFlush]

end Shoumei.RISCV.Control.CPUControlProofs

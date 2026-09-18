/-
RISCV/CSRFileProofs.lean - Structural proofs for CSRFile module
-/

import Shoumei.RISCV.CSRFile
import Shoumei.RISCV.Config

namespace Shoumei.RISCV.CSRFileProofs

open Shoumei
open Shoumei.RISCV

/-- Default CSRFile circuit definition -/
def csrFile := mkCSRFile defaultCPUConfig

/-- Verify CSRFile module name -/
theorem csrFile_name : csrFile.name = s!"CSRFile_{defaultCPUConfig.isaString}" := by
  rfl

/-- Verify CSRFile instance count (12 Register32 + 8 DFF) -/
theorem csrFile_instances : csrFile.instances.length = 20 := by
  native_decide

/-- Verify CSRFile output count -/
theorem csrFile_outputs : csrFile.outputs.length =
    32 + (if defaultCPUConfig.xlen == 64 || defaultCPUConfig.enableD then 64 else 32) + 6 + 2 + 3 + 5 + 1 := by
  native_decide

end Shoumei.RISCV.CSRFileProofs

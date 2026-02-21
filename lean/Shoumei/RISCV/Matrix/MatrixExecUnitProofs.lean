/-
RISCV/Matrix/MatrixExecUnitProofs.lean - Proofs for Matrix Execution Unit

Structural proofs for the MatrixExecUnit circuit.
-/

import Shoumei.RISCV.Matrix.MatrixExecUnit

namespace Shoumei.RISCV.Matrix

open Shoumei

-- Structural proofs
theorem matrixExecUnit_name : mkMatrixExecUnit.name = "MatrixExecUnit" := by native_decide
theorem matrixExecUnit_output_count : mkMatrixExecUnit.outputs.length = 40 := by native_decide
theorem matrixExecUnit_instance_count : mkMatrixExecUnit.instances.length = 2 := by native_decide

/-! ## Behavioral Model Proofs -/

-- Init state properties
theorem matrixExec_init_not_busy :
    (MatrixExecState.init 16 16).busy = false := by
  simp [MatrixExecState.init]

theorem matrixExec_init_sew :
    (MatrixExecState.init 16 16).sew = SEW.Int8 := by
  simp [MatrixExecState.init]

end Shoumei.RISCV.Matrix

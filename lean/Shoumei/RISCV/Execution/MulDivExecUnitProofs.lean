/-
  MulDiv Execution Unit Proofs

  Proves structural properties of the combined multiply/divide execution unit.
-/

import Shoumei.RISCV.Execution.MulDivExecUnit

namespace Shoumei.RISCV.Execution.MulDivExecUnitProofs

open Shoumei.RISCV.Execution

/-- The MulDiv execution unit has the correct name. -/
theorem muldiv_name :
    mulDivExecUnit.name = "MulDivExecUnit" := by native_decide

/-- The unit has 143 input signals. -/
theorem muldiv_input_count :
    mulDivExecUnit.inputs.length = 143 := by native_decide

/-- The unit has 72 output signals. -/
theorem muldiv_output_count :
    mulDivExecUnit.outputs.length = 72 := by native_decide

/-- The unit uses exactly 2 submodule instances (multiplier + divider). -/
theorem muldiv_instance_count :
    mulDivExecUnit.instances.length = 2 := by native_decide

end Shoumei.RISCV.Execution.MulDivExecUnitProofs

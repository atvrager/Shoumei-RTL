/-
  MulDiv Execution Unit Proofs

  Proves structural properties of the combined multiply/divide execution unit.
-/

import Shoumei.RISCV.Execution.MulDivExecUnit
import Shoumei.RISCV.Execution.ReservationStation

namespace Shoumei.RISCV.Execution.MulDivExecUnitProofs

open Shoumei.RISCV.Execution

/-- The MulDiv execution unit has the correct name. -/
theorem muldiv_name :
    mulDivExecUnit.name = "MulDivExecUnit" := by native_decide

/-- The unit has 78 input signals. -/
theorem muldiv_input_count :
    mulDivExecUnit.inputs.length = 78 := by native_decide

/-- The unit has 40 output signals. -/
theorem muldiv_output_count :
    mulDivExecUnit.outputs.length = 40 := by native_decide

/-- The unit uses exactly 2 submodule instances (multiplier + divider). -/
theorem muldiv_instance_count :
    mulDivExecUnit.instances.length = 2 := by native_decide

/-- MulDiv RS4 has the correct name. -/
theorem muldiv_rs4_name :
    mulDivRS4.name = "MulDivRS4" := by native_decide

/-- MulDiv RS4 has the same input count as regular RS4. -/
theorem muldiv_rs4_inputs :
    mulDivRS4.inputs.length = rs4.inputs.length := by native_decide

/-- MulDiv RS4 has the same output count as regular RS4. -/
theorem muldiv_rs4_outputs :
    mulDivRS4.outputs.length = rs4.outputs.length := by native_decide

/-- MulDiv RS4 has the same instance count as regular RS4. -/
theorem muldiv_rs4_instances :
    mulDivRS4.instances.length = rs4.instances.length := by native_decide

end Shoumei.RISCV.Execution.MulDivExecUnitProofs

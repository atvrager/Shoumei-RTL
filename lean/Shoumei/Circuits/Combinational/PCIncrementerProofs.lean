/-
Circuits/Combinational/PCIncrementerProofs.lean - Proofs for PC incrementers
-/

import Shoumei.Circuits.Combinational.PCIncrementer

namespace Shoumei.Circuits.Combinational

/-- PCIncrementer4 has exactly 32 inputs. -/
theorem pcIncrementer4_input_count : pcIncrementer4Circuit.inputs.length = 32 := by
  native_decide

/-- PCIncrementer4 has exactly 32 outputs. -/
theorem pcIncrementer4_output_count : pcIncrementer4Circuit.outputs.length = 32 := by
  native_decide

/-- PCIncrementer8 has exactly 32 inputs. -/
theorem pcIncrementer8_input_count : pcIncrementer8Circuit.inputs.length = 32 := by
  native_decide

/-- PCIncrementer8 has exactly 32 outputs. -/
theorem pcIncrementer8_output_count : pcIncrementer8Circuit.outputs.length = 32 := by
  native_decide

end Shoumei.Circuits.Combinational

/-
  Sequential Divider Structural Proofs

  Proves structural properties of the 32-cycle restoring divider circuit.
-/

import Shoumei.Circuits.Sequential.Divider

namespace Shoumei.Circuits.Sequential.DividerProofs

open Shoumei.Circuits.Sequential

/-- The divider circuit has the correct name. -/
theorem divider_name :
    divider32Circuit.name = "Divider32" := by native_decide

/-- The divider has 77 input signals. -/
theorem divider_input_count :
    divider32Circuit.inputs.length = 77 := by native_decide

/-- The divider has 40 output signals. -/
theorem divider_output_count :
    divider32Circuit.outputs.length = 40 := by native_decide

/-- The divider is sequential (contains DFF state registers). -/
theorem divider_sequential :
    divider32Circuit.hasSequentialElements = true := by native_decide

/-- The divider uses exactly 1 submodule instance (Subtractor32). -/
theorem divider_instance_count :
    divider32Circuit.instances.length = 1 := by native_decide

/-- Behavioral: unsigned 10 / 3 = 3 (DIVU, op=5). -/
theorem divu_10_by_3 : verifyDIVU 10 3 = true := by native_decide

/-- Behavioral: unsigned 100 / 7 = 14 (DIVU). -/
theorem divu_100_by_7 : verifyDIVU 100 7 = true := by native_decide

/-- Behavioral: unsigned 10 % 3 = 1 (REMU, op=7). -/
theorem remu_10_mod_3 : verifyREMU 10 3 = true := by native_decide

/-- Behavioral: unsigned 255 / 1 = 255 (DIVU, identity). -/
theorem divu_identity : verifyDIVU 255 1 = true := by native_decide

end Shoumei.Circuits.Sequential.DividerProofs

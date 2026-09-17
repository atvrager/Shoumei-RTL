/-
FPMiscProofs.lean - Structural proofs for FPMisc and its sub-circuits
-/

import Shoumei.Circuits.Combinational.FPMisc

namespace Shoumei.Circuits.Combinational

theorem fpMisc_name : fpMiscCircuit.name = "FPMisc" := by rfl
theorem fpMisc_inputs : fpMiscCircuit.inputs.length = 74 := by native_decide
theorem fpMisc_outputs : fpMiscCircuit.outputs.length = 37 := by native_decide
theorem fpMisc_instances : fpMiscCircuit.instances.length = 4 := by native_decide

theorem fpSgnj_name : fpSgnjCircuit.name = "FPSgnj" := by rfl
theorem fpSgnj_inputs : fpSgnjCircuit.inputs.length = 69 := by native_decide
theorem fpSgnj_outputs : fpSgnjCircuit.outputs.length = 32 := by native_decide

theorem fpCompare_name : fpCompareCircuit.name = "FPCompare" := by rfl
theorem fpCompare_inputs : fpCompareCircuit.inputs.length = 71 := by native_decide
theorem fpCompare_outputs : fpCompareCircuit.outputs.length = 33 := by native_decide

theorem fpClass_name : fpClassCircuit.name = "FPClass" := by rfl
theorem fpClass_inputs : fpClassCircuit.inputs.length = 34 := by native_decide
theorem fpClass_outputs : fpClassCircuit.outputs.length = 32 := by native_decide

theorem fpCvtInt_name : fpCvtIntCircuit.name = "FPCvtInt" := by rfl
theorem fpCvtInt_inputs : fpCvtIntCircuit.inputs.length = 39 := by native_decide
theorem fpCvtInt_outputs : fpCvtIntCircuit.outputs.length = 34 := by native_decide

end Shoumei.Circuits.Combinational

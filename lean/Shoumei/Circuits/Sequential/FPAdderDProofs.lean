/-
FPAdderDProofs.lean - Structural proofs for FPAdderD
-/

import Shoumei.Circuits.Sequential.FPAdderD

namespace Shoumei.Circuits.Sequential

theorem fpAdderD_name : fpAdderDCircuit.name = "FPAdderD" := by rfl

theorem fpAdderD_inputs : fpAdderDCircuit.inputs.length = 142 := by native_decide

theorem fpAdderD_outputs : fpAdderDCircuit.outputs.length = 76 := by native_decide

theorem fpAdderD_sequential : fpAdderDCircuit.hasSequentialElements = true := by native_decide

end Shoumei.Circuits.Sequential

/-
FPSqrtDProofs.lean - Structural proofs for FPSqrtD
-/

import Shoumei.Circuits.Sequential.FPSqrtD

namespace Shoumei.Circuits.Sequential

theorem fpSqrtD_name : fpSqrtDCircuit.name = "FPSqrtD" := by rfl

theorem fpSqrtD_inputs : fpSqrtDCircuit.inputs.length = 78 := by native_decide

theorem fpSqrtD_outputs : fpSqrtDCircuit.outputs.length = 77 := by native_decide

theorem fpSqrtD_sequential : fpSqrtDCircuit.hasSequentialElements = true := by native_decide

end Shoumei.Circuits.Sequential

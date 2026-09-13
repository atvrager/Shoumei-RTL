/-
FPMultiplierDProofs.lean - Structural proofs for FPMultiplierD
-/

import Shoumei.Circuits.Sequential.FPMultiplierD

namespace Shoumei.Circuits.Sequential

theorem fpMultiplierD_name : fpMultiplierDCircuit.name = "FPMultiplierD" := by rfl

theorem fpMultiplierD_inputs : fpMultiplierDCircuit.inputs.length = 141 := by native_decide

theorem fpMultiplierD_outputs : fpMultiplierDCircuit.outputs.length = 76 := by native_decide

theorem fpMultiplierD_sequential : fpMultiplierDCircuit.hasSequentialElements = true := by native_decide

end Shoumei.Circuits.Sequential

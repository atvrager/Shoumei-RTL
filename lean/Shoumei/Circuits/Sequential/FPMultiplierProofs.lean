/-
FPMultiplierProofs.lean - Structural proofs for FPMultiplier
-/

import Shoumei.Circuits.Sequential.FPMultiplier

namespace Shoumei.Circuits.Sequential

theorem fpMultiplier_name : fpMultiplierCircuit.name = "FPMultiplier" := by rfl

theorem fpMultiplier_inputs : fpMultiplierCircuit.inputs.length = 77 := by native_decide

theorem fpMultiplier_outputs : fpMultiplierCircuit.outputs.length = 44 := by native_decide

theorem fpMultiplier_sequential : fpMultiplierCircuit.hasSequentialElements = true := by native_decide

end Shoumei.Circuits.Sequential

/-
FPDividerDProofs.lean - Structural proofs for FPDividerD
-/

import Shoumei.Circuits.Sequential.FPDividerD

namespace Shoumei.Circuits.Sequential

theorem fpDividerD_name : fpDividerDCircuit.name = "FPDividerD" := by rfl

theorem fpDividerD_inputs : fpDividerDCircuit.inputs.length = 142 := by native_decide

theorem fpDividerD_outputs : fpDividerDCircuit.outputs.length = 77 := by native_decide

theorem fpDividerD_sequential : fpDividerDCircuit.hasSequentialElements = true := by native_decide

end Shoumei.Circuits.Sequential

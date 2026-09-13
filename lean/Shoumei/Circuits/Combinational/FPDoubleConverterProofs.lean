/-
FPDoubleConverterProofs.lean - Structural proofs for FPDoubleConverter
-/

import Shoumei.Circuits.Combinational.FPDoubleConverter

namespace Shoumei.Circuits.Combinational

theorem fpDoubleConverter_inputs : fpDoubleConverterCircuit.inputs.length = 75 := by native_decide

theorem fpDoubleConverter_outputs : fpDoubleConverterCircuit.outputs.length = 70 := by native_decide

theorem fpDoubleConverter_name : fpDoubleConverterCircuit.name = "FPDoubleConverter" := by rfl

end Shoumei.Circuits.Combinational

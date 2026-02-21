/-
Circuits/Combinational/MACUnitProofs.lean - Proofs for MAC Units

Structural proofs for MACUnit8 and MACUnit16.
-/

import Shoumei.Circuits.Combinational.MACUnit

namespace Shoumei.Circuits.Combinational

open Shoumei

-- MACUnit8 structural proofs
theorem macUnit8_name : mkMACUnit8.name = "MACUnit8" := by native_decide
theorem macUnit8_input_count : mkMACUnit8.inputs.length = 49 := by native_decide
theorem macUnit8_output_count : mkMACUnit8.outputs.length = 32 := by native_decide
theorem macUnit8_instance_count : mkMACUnit8.instances.length = 33 := by native_decide

-- MACUnit16 structural proofs
theorem macUnit16_name : mkMACUnit16.name = "MACUnit16" := by native_decide
theorem macUnit16_input_count : mkMACUnit16.inputs.length = 65 := by native_decide
theorem macUnit16_output_count : mkMACUnit16.outputs.length = 32 := by native_decide
theorem macUnit16_instance_count : mkMACUnit16.instances.length = 33 := by native_decide

end Shoumei.Circuits.Combinational

/-
Peripherals/SRAMProofs.lean - Structural proofs for SRAM
-/

import Shoumei.Peripherals.SRAM

namespace Shoumei.Peripherals

open Shoumei

theorem sram_name : sramCircuit.name = "SRAM" := by rfl

theorem sram_instances : sramCircuit.instances.length = 2 := by native_decide

theorem sram_inputs_positive : sramCircuit.inputs.length > 0 := by native_decide

theorem sram_outputs_positive : sramCircuit.outputs.length > 0 := by native_decide

theorem sram_gates_positive : sramCircuit.gates.length > 0 := by native_decide

end Shoumei.Peripherals

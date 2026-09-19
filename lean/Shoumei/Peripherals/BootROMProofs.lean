/-
Peripherals/BootROMProofs.lean - Structural proofs for BootROM
-/

import Shoumei.Peripherals.BootROM

namespace Shoumei.Peripherals

open Shoumei

theorem bootROM_name : bootROMCircuit.name = "BootROM" := by rfl

theorem bootROM_leaf : bootROMCircuit.instances.isEmpty := by native_decide

theorem bootROM_inputs_positive : bootROMCircuit.inputs.length > 0 := by native_decide

theorem bootROM_outputs_positive : bootROMCircuit.outputs.length > 0 := by native_decide

theorem bootROM_gates_positive : bootROMCircuit.gates.length > 0 := by native_decide

end Shoumei.Peripherals

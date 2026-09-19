/-
Peripherals/APLICProofs.lean - Structural proofs for AIA APLIC
-/

import Shoumei.Peripherals.APLIC

namespace Shoumei.Peripherals

open Shoumei

theorem aplic_name : aplicCircuit.name = "APLIC" := by rfl

theorem aplic_instances : aplicCircuit.instances.length = 3 := by native_decide

theorem aplic_inputs_positive : aplicCircuit.inputs.length > 0 := by native_decide

theorem aplic_outputs_positive : aplicCircuit.outputs.length > 0 := by native_decide

theorem aplic_gates_positive : aplicCircuit.gates.length > 0 := by native_decide

end Shoumei.Peripherals

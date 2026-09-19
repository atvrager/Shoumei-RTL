/-
Peripherals/ACLINTProofs.lean - Structural proofs for ACLINT
-/

import Shoumei.Peripherals.ACLINT

namespace Shoumei.Peripherals

open Shoumei

theorem aclint_name : aclintCircuit.name = "ACLINT" := by rfl

theorem aclint_instances : aclintCircuit.instances.length = 6 := by native_decide

theorem aclint_inputs_positive : aclintCircuit.inputs.length > 0 := by native_decide

theorem aclint_outputs_positive : aclintCircuit.outputs.length > 0 := by native_decide

theorem aclint_gates_positive : aclintCircuit.gates.length > 0 := by native_decide

end Shoumei.Peripherals

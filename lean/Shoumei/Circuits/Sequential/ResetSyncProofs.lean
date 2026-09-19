/-
Circuits/Sequential/ResetSyncProofs.lean - Structural proofs for ResetSync
-/

import Shoumei.Circuits.Sequential.ResetSync

namespace Shoumei.Circuits.Sequential

open Shoumei

theorem resetSync_name : resetSyncCircuit.name = "ResetSync" := by rfl

theorem resetSync_inputs : resetSyncCircuit.inputs.length = 3 := by native_decide

theorem resetSync_outputs : resetSyncCircuit.outputs.length = 1 := by native_decide

theorem resetSync_gates : resetSyncCircuit.gates.length = 4 := by native_decide

theorem resetSync_instances : resetSyncCircuit.instances.isEmpty := by native_decide

end Shoumei.Circuits.Sequential

/-
Circuits/Combinational/BranchTargetAdderProofs.lean - Structural proofs for BranchTargetAdder32
-/

import Shoumei.Circuits.Combinational.BranchTargetAdder

namespace Shoumei.Circuits.Combinational

theorem branchTargetAdder32_inputs : branchTargetAdder32Circuit.inputs.length = 58 := by native_decide

theorem branchTargetAdder32_outputs : branchTargetAdder32Circuit.outputs.length = 32 := by native_decide

theorem branchTargetAdder32_instances : branchTargetAdder32Circuit.instances.length = 0 := by native_decide

theorem branchTargetAdder32_gates : branchTargetAdder32Circuit.gates.length = 622 := by native_decide

theorem branchTargetAdder32_name : branchTargetAdder32Circuit.name = "BranchTargetAdder32" := by native_decide

end Shoumei.Circuits.Combinational

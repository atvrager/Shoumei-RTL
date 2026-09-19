/-
FPAdderProofs.lean - Structural proofs for FPAdder and its pipeline stages
-/

import Shoumei.Circuits.Sequential.FPAdder

namespace Shoumei.Circuits.Sequential

theorem fpAdder_name : fpAdderCircuit.name = "FPAdder" := by rfl
theorem fpAdder_inputs : fpAdderCircuit.inputs.length = 78 := by native_decide
theorem fpAdder_outputs : fpAdderCircuit.outputs.length = 44 := by native_decide
theorem fpAdder_sequential : fpAdderCircuit.hasSequentialElements = true := by native_decide
theorem fpAdder_instances : fpAdderCircuit.instances.length = 4 := by native_decide

theorem fpAdder_stage1_name : fpAdder_Stage1Circuit.name = "FPAdder_Stage1_Unpack" := by rfl
theorem fpAdder_stage1_inputs : fpAdder_Stage1Circuit.inputs.length = 66 := by native_decide
theorem fpAdder_stage1_outputs : fpAdder_Stage1Circuit.outputs.length = 81 := by native_decide

theorem fpAdder_stage2_name : fpAdder_Stage2Circuit.name = "FPAdder_Stage2_Align" := by rfl
theorem fpAdder_stage2_inputs : fpAdder_Stage2Circuit.inputs.length = 79 := by native_decide
theorem fpAdder_stage2_outputs : fpAdder_Stage2Circuit.outputs.length = 61 := by native_decide

theorem fpAdder_stage3_name : fpAdder_Stage3Circuit.name = "FPAdder_Stage3_AddSub" := by rfl
theorem fpAdder_stage3_inputs : fpAdder_Stage3Circuit.inputs.length = 50 := by native_decide
theorem fpAdder_stage3_outputs : fpAdder_Stage3Circuit.outputs.length = 31 := by native_decide

theorem fpAdder_stage4_name : fpAdder_Stage4Circuit.name = "FPAdder_Stage4_NormRound" := by rfl
theorem fpAdder_stage4_inputs : fpAdder_Stage4Circuit.inputs.length = 48 := by native_decide
theorem fpAdder_stage4_outputs : fpAdder_Stage4Circuit.outputs.length = 37 := by native_decide

end Shoumei.Circuits.Sequential

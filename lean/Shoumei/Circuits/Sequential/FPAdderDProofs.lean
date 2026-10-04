/-
FPAdderDProofs.lean - Structural proofs for FPAdderD and its pipeline stages
-/

import Shoumei.Circuits.Sequential.FPAdderD

namespace Shoumei.Circuits.Sequential

theorem fpAdderD_name : fpAdderDCircuit.name = "FPAdderD" := by rfl
theorem fpAdderD_inputs : fpAdderDCircuit.inputs.length = 142 := by native_decide
theorem fpAdderD_outputs : fpAdderDCircuit.outputs.length = 76 := by native_decide
theorem fpAdderD_sequential : fpAdderDCircuit.hasSequentialElements = true := by native_decide
theorem fpAdderD_instances : fpAdderDCircuit.instances.length = 5 := by native_decide

theorem fpAdderD_stage1_name : fpAdderD_Stage1Circuit.name = "FPAdderD_Stage1_Unpack" := by rfl
theorem fpAdderD_stage1_inputs : fpAdderD_Stage1Circuit.inputs.length = 130 := by native_decide
theorem fpAdderD_stage1_outputs : fpAdderD_Stage1Circuit.outputs.length = 147 := by native_decide

theorem fpAdderD_stage2_name : fpAdderD_Stage2Circuit.name = "FPAdderD_Stage2_Align" := by rfl
theorem fpAdderD_stage2_inputs : fpAdderD_Stage2Circuit.inputs.length = 145 := by native_decide
theorem fpAdderD_stage2_outputs : fpAdderD_Stage2Circuit.outputs.length = 126 := by native_decide

theorem fpAdderD_stage3_name : fpAdderD_Stage3Circuit.name = "FPAdderD_Stage3_AddSub" := by rfl
theorem fpAdderD_stage3_inputs : fpAdderD_Stage3Circuit.inputs.length = 112 := by native_decide
theorem fpAdderD_stage3_outputs : fpAdderD_Stage3Circuit.outputs.length = 64 := by native_decide

theorem fpAdderD_stage4a_name : fpAdderD_Stage4aCircuit.name = "FPAdderD_Stage4a_Norm" := by rfl
theorem fpAdderD_stage4a_inputs : fpAdderD_Stage4aCircuit.inputs.length = 87 := by native_decide
theorem fpAdderD_stage4a_outputs : fpAdderD_Stage4aCircuit.outputs.length = 82 := by native_decide

theorem fpAdderD_stage4b_name : fpAdderD_Stage4bCircuit.name = "FPAdderD_Stage4b_Round" := by rfl
theorem fpAdderD_stage4b_inputs : fpAdderD_Stage4bCircuit.inputs.length = 83 := by native_decide
theorem fpAdderD_stage4b_outputs : fpAdderD_Stage4bCircuit.outputs.length = 69 := by native_decide

end Shoumei.Circuits.Sequential

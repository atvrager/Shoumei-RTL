/-
FPAdderDProofs.lean - Structural proofs for FPAdderD and its pipeline stages
-/

import Shoumei.Circuits.Sequential.FPAdderD

namespace Shoumei.Circuits.Sequential

theorem fpAdderD_name : fpAdderDCircuit.name = "FPAdderD" := by rfl
theorem fpAdderD_inputs : fpAdderDCircuit.inputs.length = 142 := by native_decide
theorem fpAdderD_outputs : fpAdderDCircuit.outputs.length = 76 := by native_decide
theorem fpAdderD_sequential : fpAdderDCircuit.hasSequentialElements = true := by native_decide
theorem fpAdderD_instances : fpAdderDCircuit.instances.length = 4 := by native_decide

theorem fpAdderD_stage1_name : fpAdderD_Stage1Circuit.name = "FPAdderD_Stage1_Unpack" := by rfl
theorem fpAdderD_stage1_inputs : fpAdderD_Stage1Circuit.inputs.length = 130 := by native_decide
theorem fpAdderD_stage1_outputs : fpAdderD_Stage1Circuit.outputs.length = 146 := by native_decide

theorem fpAdderD_stage2_name : fpAdderD_Stage2Circuit.name = "FPAdderD_Stage2_Align" := by rfl
theorem fpAdderD_stage2_inputs : fpAdderD_Stage2Circuit.inputs.length = 145 := by native_decide
theorem fpAdderD_stage2_outputs : fpAdderD_Stage2Circuit.outputs.length = 126 := by native_decide

theorem fpAdderD_stage3_name : fpAdderD_Stage3Circuit.name = "FPAdderD_Stage3_AddSub" := by rfl
theorem fpAdderD_stage3_inputs : fpAdderD_Stage3Circuit.inputs.length = 111 := by native_decide
theorem fpAdderD_stage3_outputs : fpAdderD_Stage3Circuit.outputs.length = 64 := by native_decide

theorem fpAdderD_stage4_name : fpAdderD_Stage4Circuit.name = "FPAdderD_Stage4_NormRound" := by rfl
theorem fpAdderD_stage4_inputs : fpAdderD_Stage4Circuit.inputs.length = 85 := by native_decide
theorem fpAdderD_stage4_outputs : fpAdderD_Stage4Circuit.outputs.length = 69 := by native_decide

end Shoumei.Circuits.Sequential

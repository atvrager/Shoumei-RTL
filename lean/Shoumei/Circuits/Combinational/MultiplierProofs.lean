/-
  Pipelined Multiplier Structural Proofs

  Proves structural properties of the 3-stage pipelined multiplier circuit
  and the CSACompressor64 sub-module.
-/

import Shoumei.Circuits.Combinational.Multiplier

namespace Shoumei.Circuits.Combinational.MultiplierProofs

open Shoumei.Circuits.Combinational

/-! ## CSACompressor64 Proofs -/

/-- The CSA compressor has the correct name. -/
theorem csa_name :
    csaCompressor64.name = "CSACompressor64" := by native_decide

/-- The CSA compressor has 193 input signals (3×64 + zero). -/
theorem csa_input_count :
    csaCompressor64.inputs.length = 193 := by native_decide

/-- The CSA compressor has 128 output signals (64 sum + 64 carry). -/
theorem csa_output_count :
    csaCompressor64.outputs.length = 128 := by native_decide

/-- The CSA compressor has 512 gates. -/
theorem csa_gate_count :
    csaCompressor64.gates.length = 512 := by native_decide

/-- The CSA compressor is purely combinational (no instances). -/
theorem csa_instance_count :
    csaCompressor64.instances.length = 0 := by native_decide

/-! ## PipelinedMultiplier Proofs -/

/-- The multiplier circuit has the correct name. -/
theorem multiplier_name :
    pipelinedMultiplier.name = "PipelinedMultiplier" := by native_decide

/-- The multiplier has 77 input signals. -/
theorem multiplier_input_count :
    pipelinedMultiplier.inputs.length = 77 := by native_decide

/-- The multiplier has 39 output signals. -/
theorem multiplier_output_count :
    pipelinedMultiplier.outputs.length = 39 := by native_decide

/-- The multiplier is sequential (contains DFF pipeline registers). -/
theorem multiplier_sequential :
    pipelinedMultiplier.hasSequentialElements = true := by native_decide

/-- The multiplier uses 31 submodule instances (30 CSACompressor64 + 1 RippleCarryAdder64). -/
theorem multiplier_instance_count :
    pipelinedMultiplier.instances.length = 31 := by native_decide

/-! ## Behavioral Proofs -/

/-- Behavioral: pipeline produces correct MUL result (2 * 3 = 6). -/
theorem mul_2_times_3 : verifyMulPipeline 2 3 = true := by native_decide

/-- Behavioral: pipeline produces correct MUL result (7 * 8 = 56). -/
theorem mul_7_times_8 : verifyMulPipeline 7 8 = true := by native_decide

/-- Behavioral: pipeline handles zero correctly (0 * 42 = 0). -/
theorem mul_zero : verifyMulPipeline 0 42 = true := by native_decide

/-- Behavioral: pipeline handles identity (1 * 255 = 255). -/
theorem mul_identity : verifyMulPipeline 1 255 = true := by native_decide

end Shoumei.Circuits.Combinational.MultiplierProofs

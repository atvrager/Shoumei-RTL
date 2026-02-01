/-
DecoderProofs.lean - Structural proofs for binary decoder

Proves structural properties of the decoder:
- Gate counts are reasonable
- Port counts match specifications
- Deterministic structure

All proofs use `native_decide` for concrete instances.
-/

import Shoumei.Circuits.Combinational.Decoder

namespace Shoumei.Circuits.Combinational

open Shoumei

/-! ## Concrete Instance Proofs -/

-- Decoder2 (2→4)
theorem decoder2_structure :
  mkDecoder2.inputs.length = 2 ∧
  mkDecoder2.outputs.length = 4 := by
  native_decide

theorem decoder2_gate_count :
  mkDecoder2.gates.length = 8 := by
  native_decide

theorem decoder2_has_name :
  mkDecoder2.name = "Decoder2" := by
  native_decide

-- Decoder3 (3→8)
theorem decoder3_structure :
  mkDecoder3.inputs.length = 3 ∧
  mkDecoder3.outputs.length = 8 := by
  native_decide

theorem decoder3_gate_count :
  mkDecoder3.gates.length = 28 := by
  native_decide

theorem decoder3_has_name :
  mkDecoder3.name = "Decoder3" := by
  native_decide

-- Decoder5 (5→32) - Used for RAT
theorem decoder5_structure :
  mkDecoder5.inputs.length = 5 ∧
  mkDecoder5.outputs.length = 32 := by
  native_decide

theorem decoder5_gate_count :
  mkDecoder5.gates.length = 208 := by
  native_decide

theorem decoder5_has_name :
  mkDecoder5.name = "Decoder5" := by
  native_decide

-- Decoder6 (6→64) - Used for PhysRegFile
theorem decoder6_structure :
  mkDecoder6.inputs.length = 6 ∧
  mkDecoder6.outputs.length = 64 := by
  native_decide

theorem decoder6_gate_count :
  mkDecoder6.gates.length = 512 := by
  native_decide

theorem decoder6_has_name :
  mkDecoder6.name = "Decoder6" := by
  native_decide

/-! ## Behavioral Properties -/

-- Behavioral property: decoding is deterministic
theorem decode_deterministic {n : Nat} (input : Fin (2^n)) :
  let state1 := decode input
  let state2 := decode input
  state1.output = state2.output := by
  rfl

-- Behavioral property: output is one-hot
theorem decode_onehot {n : Nat} (input : Fin (2^n)) (i : Fin (2^n)) :
  (decode input).output i = (i == input) := by
  rfl

end Shoumei.Circuits.Combinational

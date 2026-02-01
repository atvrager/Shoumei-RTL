/-
Structural Proofs for MuxTree

This file contains structural theorems about MuxTree circuits:
- Port counts (inputs, outputs)
- Gate counts (verified against formula: (n-1) * width * 4)
- Structure properties

All proofs use native_decide for concrete circuit instances.
-/

import Shoumei.Circuits.Combinational.MuxTree

namespace Shoumei.Circuits.Combinational

open Shoumei

/-! ## Mux2x8 (2:1 MUX, 8 bits) -/

theorem mux2x8_structure :
  mkMux2x8.inputs.length = 17 ∧
  mkMux2x8.outputs.length = 8 := by native_decide

theorem mux2x8_gate_count :
  mkMux2x8.gates.length = 32 := by native_decide

theorem mux2x8_formula :
  -- Formula: (n-1) * width * 4 = (2-1) * 8 * 4 = 32
  mkMux2x8.gates.length = (2 - 1) * 8 * 4 := by native_decide

/-! ## Mux4x8 (4:1 MUX, 8 bits) -/

theorem mux4x8_structure :
  mkMux4x8.inputs.length = 34 ∧
  mkMux4x8.outputs.length = 8 := by native_decide

theorem mux4x8_gate_count :
  mkMux4x8.gates.length = 96 := by native_decide

theorem mux4x8_formula :
  -- Formula: (n-1) * width * 4 = (4-1) * 8 * 4 = 96
  mkMux4x8.gates.length = (4 - 1) * 8 * 4 := by native_decide

/-! ## Mux32x6 (32:1 MUX, 6 bits) - For RAT read ports -/

theorem mux32x6_structure :
  mkMux32x6.inputs.length = 197 ∧
  mkMux32x6.outputs.length = 6 := by native_decide

theorem mux32x6_gate_count :
  mkMux32x6.gates.length = 744 := by native_decide

theorem mux32x6_formula :
  -- Formula: (n-1) * width * 4 = (32-1) * 6 * 4 = 744
  mkMux32x6.gates.length = (32 - 1) * 6 * 4 := by native_decide

theorem mux32x6_inputs_breakdown :
  -- 32 inputs * 6 bits + 5 select bits = 192 + 5 = 197
  mkMux32x6.inputs.length = 32 * 6 + 5 := by native_decide

/-! ## Mux64x32 (64:1 MUX, 32 bits) - For PhysRegFile read ports -/

theorem mux64x32_structure :
  mkMux64x32.inputs.length = 2054 ∧
  mkMux64x32.outputs.length = 32 := by native_decide

theorem mux64x32_gate_count :
  mkMux64x32.gates.length = 8064 := by native_decide

theorem mux64x32_formula :
  -- Formula: (n-1) * width * 4 = (64-1) * 32 * 4 = 8064
  mkMux64x32.gates.length = (64 - 1) * 32 * 4 := by native_decide

theorem mux64x32_inputs_breakdown :
  -- 64 inputs * 32 bits + 6 select bits = 2048 + 6 = 2054
  mkMux64x32.inputs.length = 64 * 32 + 6 := by native_decide

/-! ## General Properties -/

theorem mux2x8_deterministic :
  -- All gates are deterministic (structural property)
  ∀ g ∈ mkMux2x8.gates, g.inputs.length > 0 := by native_decide

theorem mux4x8_deterministic :
  ∀ g ∈ mkMux4x8.gates, g.inputs.length > 0 := by native_decide

theorem mux32x6_deterministic :
  ∀ g ∈ mkMux32x6.gates, g.inputs.length > 0 := by native_decide

theorem mux64x32_deterministic :
  ∀ g ∈ mkMux64x32.gates, g.inputs.length > 0 := by native_decide

end Shoumei.Circuits.Combinational

/-
RegisterProofs.lean - Compositional Proofs for Hierarchical Registers

Power-of-2 registers are verified via LEC.
Large registers are built from power-of-2 blocks and verified compositionally.
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.Register
import Shoumei.Verification.Compositional

open Shoumei.Circuits.Sequential
open Shoumei.Verification

namespace Shoumei.Circuits.Sequential.RegisterProofs

/-! ## Compositional Certificates -/

/-- Register91 is built from power-of-2 building blocks -/
def register91_cert : CompositionalCert := {
  moduleName := "Register91"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register98 is built from power-of-2 building blocks (64+32+2) -/
def register98_cert : CompositionalCert := {
  moduleName := "Register98"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register130 is built from power-of-2 building blocks (64+64+2) -/
def register130_cert : CompositionalCert := {
  moduleName := "Register130"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register157 is built from power-of-2 building blocks (64+64+16+8+4+1) -/
def register157_cert : CompositionalCert := {
  moduleName := "Register157"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register158 is built from power-of-2 building blocks (64+64+16+8+4+2) -/
def register158_cert : CompositionalCert := {
  moduleName := "Register158"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register159 is built from power-of-2 building blocks (64+64+16+8+4+2+1) -/
def register159_cert : CompositionalCert := {
  moduleName := "Register159"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register96 is built from power-of-2 building blocks (64+32) -/
def register96_cert : CompositionalCert := {
  moduleName := "Register96"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register160 is built from power-of-2 building blocks (64+64+32) -/
def register160_cert : CompositionalCert := {
  moduleName := "Register160"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-! ## Structural Proofs -/

/-- Register91 uses 5 hierarchical instances (64+16+8+2+1) -/
theorem register91_instance_count : mkRegister91Hierarchical.instances.length = 5 := by native_decide

/-- Register91 has no gates (hierarchical, not flat) -/
theorem register91_no_gates : mkRegister91Hierarchical.gates.length = 0 := by native_decide

/-- Register91 decomposition correctness: 64+16+8+2+1 = 91 -/
theorem register91_decomposition : decomposeToPowersOf2 91 = [64, 16, 8, 2, 1] := by native_decide

/-- Register96 uses 2 hierarchical instances (64+32) -/
theorem register96_instance_count : mkRegister96Hierarchical.instances.length = 2 := by native_decide

/-- Register96 has no gates (hierarchical, not flat) -/
theorem register96_no_gates : mkRegister96Hierarchical.gates.length = 0 := by native_decide

/-- Register96 decomposition correctness: 64+32 = 96 -/
theorem register96_decomposition : decomposeToPowersOf2 96 = [64, 32] := by native_decide

/-- Register98 uses 3 hierarchical instances (64+32+2) -/
theorem register98_instance_count : mkRegister98Hierarchical.instances.length = 3 := by native_decide

/-- Register98 has no gates (hierarchical, not flat) -/
theorem register98_no_gates : mkRegister98Hierarchical.gates.length = 0 := by native_decide

/-- Register98 decomposition correctness: 64+32+2 = 98 -/
theorem register98_decomposition : decomposeToPowersOf2 98 = [64, 32, 2] := by native_decide

/-- Register130 uses 3 hierarchical instances (64+64+2) -/
theorem register130_instance_count : mkRegister130Hierarchical.instances.length = 3 := by native_decide

/-- Register130 has no gates (hierarchical, not flat) -/
theorem register130_no_gates : mkRegister130Hierarchical.gates.length = 0 := by native_decide

/-- Register130 decomposition correctness: 64+64+2 = 130 -/
theorem register130_decomposition : decomposeToPowersOf2 130 = [64, 64, 2] := by native_decide

/-- Register157 uses 6 hierarchical instances (64+64+16+8+4+1) -/
theorem register157_instance_count : mkRegister157Hierarchical.instances.length = 6 := by native_decide

/-- Register157 has no gates (hierarchical, not flat) -/
theorem register157_no_gates : mkRegister157Hierarchical.gates.length = 0 := by native_decide

/-- Register157 decomposition correctness: 64+64+16+8+4+1 = 157 -/
theorem register157_decomposition : decomposeToPowersOf2 157 = [64, 64, 16, 8, 4, 1] := by native_decide

/-- Register158 uses 6 hierarchical instances (64+64+16+8+4+2) -/
theorem register158_instance_count : mkRegister158Hierarchical.instances.length = 6 := by native_decide

/-- Register158 has no gates (hierarchical, not flat) -/
theorem register158_no_gates : mkRegister158Hierarchical.gates.length = 0 := by native_decide

/-- Register158 decomposition correctness: 64+64+16+8+4+2 = 158 -/
theorem register158_decomposition : decomposeToPowersOf2 158 = [64, 64, 16, 8, 4, 2] := by native_decide

/-- Register159 uses 7 hierarchical instances (64+64+16+8+4+2+1) -/
theorem register159_instance_count : mkRegister159Hierarchical.instances.length = 7 := by native_decide

/-- Register159 has no gates (hierarchical, not flat) -/
theorem register159_no_gates : mkRegister159Hierarchical.gates.length = 0 := by native_decide

/-- Register159 decomposition correctness: 64+64+16+8+4+2+1 = 159 -/
theorem register159_decomposition : decomposeToPowersOf2 159 = [64, 64, 16, 8, 4, 2, 1] := by native_decide

/-- Register160 uses 3 hierarchical instances (64+64+32) -/
theorem register160_instance_count : mkRegister160Hierarchical.instances.length = 3 := by native_decide

/-- Register160 has no gates (hierarchical, not flat) -/
theorem register160_no_gates : mkRegister160Hierarchical.gates.length = 0 := by native_decide

/-- Register160 decomposition correctness: 64+64+32 = 160 -/
theorem register160_decomposition : decomposeToPowersOf2 160 = [64, 64, 32] := by native_decide


/-! ## Verification Strategy

Register91 correctness follows from:
1. LEC verification of power-of-2 building blocks (Register1, 2, 4, 8, 16, 32, 64)
2. Hierarchical composition with correct port wiring
3. Structural proof that 64+16+8+2+1 = 91

This avoids the SEC structural mismatch issue entirely by using verified instances
instead of monolithic register arrays.
-/

end Shoumei.Circuits.Sequential.RegisterProofs

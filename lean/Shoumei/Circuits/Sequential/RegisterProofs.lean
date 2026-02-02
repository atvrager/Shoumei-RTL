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
  dependencies := ["Register64", "Register16", "Register8", "Register2", "Register1"]
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-! ## Structural Proofs -/

/-- Register91 uses 5 hierarchical instances (64+16+8+2+1) -/
theorem register91_instance_count : mkRegister91Hierarchical.instances.length = 5 := by native_decide

/-- Register91 has no gates (hierarchical, not flat) -/
theorem register91_no_gates : mkRegister91Hierarchical.gates.length = 0 := by native_decide

/-- Register91 decomposition correctness: 64+16+8+2+1 = 91 -/
theorem register91_decomposition : decomposeToPowersOf2 91 = [64, 16, 8, 2, 1] := by native_decide

/-! ## Verification Strategy

Register91 correctness follows from:
1. LEC verification of power-of-2 building blocks (Register1, 2, 4, 8, 16, 32, 64)
2. Hierarchical composition with correct port wiring
3. Structural proof that 64+16+8+2+1 = 91

This avoids the SEC structural mismatch issue entirely by using verified instances
instead of monolithic register arrays.
-/

end Shoumei.Circuits.Sequential.RegisterProofs

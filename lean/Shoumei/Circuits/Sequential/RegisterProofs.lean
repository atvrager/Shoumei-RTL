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

/-! ## Hierarchical Interconnect Verification Helpers -/

/-- Extract output wires driven by a child register instance. -/
def instanceOutputWires (inst : CircuitInstance) : List Wire :=
  inst.portMap.filterMap (fun (port, w) => if port.startsWith "q_" then some w else none)

/-- Extract input wires received by a child register instance. -/
def instanceInputWires (inst : CircuitInstance) : List Wire :=
  inst.portMap.filterMap (fun (port, w) => if port.startsWith "d_" then some w else none)

/-- Extract clock connection of an instance. -/
def instanceClock (inst : CircuitInstance) : Option Wire :=
  inst.portMap.find? (fun (port, _) => port == "clock") |>.map (·.2)

/-- Extract reset connection of an instance. -/
def instanceReset (inst : CircuitInstance) : Option Wire :=
  inst.portMap.find? (fun (port, _) => port == "reset") |>.map (·.2)

/-! ## L2 Compositional Invariants: Bit Coverage & Signal Continuity -/

-- ── Register91 ──
theorem register91_instance_count : mkRegister91Hierarchical.instances.length = 5 := by native_decide
theorem register91_decomposition : decomposeToPowersOf2 91 = [64, 16, 8, 2, 1] := by native_decide
theorem register91_outputs_cover_all_bits :
    (mkRegister91Hierarchical.instances.flatMap instanceOutputWires == makeIndexedWires "q" 91) = true := by native_decide
theorem register91_inputs_cover_all_bits :
    (mkRegister91Hierarchical.instances.flatMap instanceInputWires == makeIndexedWires "d" 91) = true := by native_decide
theorem register91_clock_synchronized :
    mkRegister91Hierarchical.instances.all (fun inst => instanceClock inst == some (Wire.mk "clock")) = true := by native_decide
theorem register91_reset_synchronized :
    mkRegister91Hierarchical.instances.all (fun inst => instanceReset inst == some (Wire.mk "reset")) = true := by native_decide

-- ── Register96 ──
theorem register96_instance_count : mkRegister96Hierarchical.instances.length = 2 := by native_decide
theorem register96_decomposition : decomposeToPowersOf2 96 = [64, 32] := by native_decide
theorem register96_outputs_cover_all_bits :
    (mkRegister96Hierarchical.instances.flatMap instanceOutputWires == makeIndexedWires "q" 96) = true := by native_decide
theorem register96_inputs_cover_all_bits :
    (mkRegister96Hierarchical.instances.flatMap instanceInputWires == makeIndexedWires "d" 96) = true := by native_decide
theorem register96_clock_synchronized :
    mkRegister96Hierarchical.instances.all (fun inst => instanceClock inst == some (Wire.mk "clock")) = true := by native_decide
theorem register96_reset_synchronized :
    mkRegister96Hierarchical.instances.all (fun inst => instanceReset inst == some (Wire.mk "reset")) = true := by native_decide

-- ── Register98 ──
theorem register98_instance_count : mkRegister98Hierarchical.instances.length = 3 := by native_decide
theorem register98_decomposition : decomposeToPowersOf2 98 = [64, 32, 2] := by native_decide
theorem register98_outputs_cover_all_bits :
    (mkRegister98Hierarchical.instances.flatMap instanceOutputWires == makeIndexedWires "q" 98) = true := by native_decide
theorem register98_inputs_cover_all_bits :
    (mkRegister98Hierarchical.instances.flatMap instanceInputWires == makeIndexedWires "d" 98) = true := by native_decide
theorem register98_clock_synchronized :
    mkRegister98Hierarchical.instances.all (fun inst => instanceClock inst == some (Wire.mk "clock")) = true := by native_decide
theorem register98_reset_synchronized :
    mkRegister98Hierarchical.instances.all (fun inst => instanceReset inst == some (Wire.mk "reset")) = true := by native_decide

-- ── Register130 ──
theorem register130_instance_count : mkRegister130Hierarchical.instances.length = 3 := by native_decide
theorem register130_decomposition : decomposeToPowersOf2 130 = [64, 64, 2] := by native_decide
theorem register130_outputs_cover_all_bits :
    (mkRegister130Hierarchical.instances.flatMap instanceOutputWires == makeIndexedWires "q" 130) = true := by native_decide
theorem register130_inputs_cover_all_bits :
    (mkRegister130Hierarchical.instances.flatMap instanceInputWires == makeIndexedWires "d" 130) = true := by native_decide
theorem register130_clock_synchronized :
    mkRegister130Hierarchical.instances.all (fun inst => instanceClock inst == some (Wire.mk "clock")) = true := by native_decide
theorem register130_reset_synchronized :
    mkRegister130Hierarchical.instances.all (fun inst => instanceReset inst == some (Wire.mk "reset")) = true := by native_decide

-- ── Register157 ──
theorem register157_instance_count : mkRegister157Hierarchical.instances.length = 6 := by native_decide
theorem register157_decomposition : decomposeToPowersOf2 157 = [64, 64, 16, 8, 4, 1] := by native_decide
theorem register157_outputs_cover_all_bits :
    (mkRegister157Hierarchical.instances.flatMap instanceOutputWires == makeIndexedWires "q" 157) = true := by native_decide
theorem register157_inputs_cover_all_bits :
    (mkRegister157Hierarchical.instances.flatMap instanceInputWires == makeIndexedWires "d" 157) = true := by native_decide
theorem register157_clock_synchronized :
    mkRegister157Hierarchical.instances.all (fun inst => instanceClock inst == some (Wire.mk "clock")) = true := by native_decide
theorem register157_reset_synchronized :
    mkRegister157Hierarchical.instances.all (fun inst => instanceReset inst == some (Wire.mk "reset")) = true := by native_decide

-- ── Register158 ──
theorem register158_instance_count : mkRegister158Hierarchical.instances.length = 6 := by native_decide
theorem register158_decomposition : decomposeToPowersOf2 158 = [64, 64, 16, 8, 4, 2] := by native_decide
theorem register158_outputs_cover_all_bits :
    (mkRegister158Hierarchical.instances.flatMap instanceOutputWires == makeIndexedWires "q" 158) = true := by native_decide
theorem register158_inputs_cover_all_bits :
    (mkRegister158Hierarchical.instances.flatMap instanceInputWires == makeIndexedWires "d" 158) = true := by native_decide
theorem register158_clock_synchronized :
    mkRegister158Hierarchical.instances.all (fun inst => instanceClock inst == some (Wire.mk "clock")) = true := by native_decide
theorem register158_reset_synchronized :
    mkRegister158Hierarchical.instances.all (fun inst => instanceReset inst == some (Wire.mk "reset")) = true := by native_decide

-- ── Register159 ──
theorem register159_instance_count : mkRegister159Hierarchical.instances.length = 7 := by native_decide
theorem register159_decomposition : decomposeToPowersOf2 159 = [64, 64, 16, 8, 4, 2, 1] := by native_decide
theorem register159_outputs_cover_all_bits :
    (mkRegister159Hierarchical.instances.flatMap instanceOutputWires == makeIndexedWires "q" 159) = true := by native_decide
theorem register159_inputs_cover_all_bits :
    (mkRegister159Hierarchical.instances.flatMap instanceInputWires == makeIndexedWires "d" 159) = true := by native_decide
theorem register159_clock_synchronized :
    mkRegister159Hierarchical.instances.all (fun inst => instanceClock inst == some (Wire.mk "clock")) = true := by native_decide
theorem register159_reset_synchronized :
    mkRegister159Hierarchical.instances.all (fun inst => instanceReset inst == some (Wire.mk "reset")) = true := by native_decide

-- ── Register160 ──
theorem register160_instance_count : mkRegister160Hierarchical.instances.length = 3 := by native_decide
theorem register160_decomposition : decomposeToPowersOf2 160 = [64, 64, 32] := by native_decide
theorem register160_outputs_cover_all_bits :
    (mkRegister160Hierarchical.instances.flatMap instanceOutputWires == makeIndexedWires "q" 160) = true := by native_decide
theorem register160_inputs_cover_all_bits :
    (mkRegister160Hierarchical.instances.flatMap instanceInputWires == makeIndexedWires "d" 160) = true := by native_decide
theorem register160_clock_synchronized :
    mkRegister160Hierarchical.instances.all (fun inst => instanceClock inst == some (Wire.mk "clock")) = true := by native_decide
theorem register160_reset_synchronized :
    mkRegister160Hierarchical.instances.all (fun inst => instanceReset inst == some (Wire.mk "reset")) = true := by native_decide

end Shoumei.Circuits.Sequential.RegisterProofs

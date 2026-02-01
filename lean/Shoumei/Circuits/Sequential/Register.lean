/-
Circuits/Sequential/Register.lean - Parameterized N-bit Register

A configurable-width register built from N parallel D flip-flops.
All DFFs share the same clock and reset signals.

Behavior:
- On rising edge of clock:
  - If reset is high: all bits become 0
  - Otherwise: each output q[i] captures its input d[i]
-/

import Shoumei.DSL

namespace Shoumei.Circuits.Sequential

open Shoumei

-- Helper: Create a list of wires with indexed names
def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}{i}")

-- Build an N-bit register
-- Creates N parallel DFFs with shared clock and reset
def mkRegisterN (n : Nat) : Circuit :=
  let d_wires := makeIndexedWires "d" n
  let q_wires := makeIndexedWires "q" n
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"

  let gates := List.zipWith (fun d q => Gate.mkDFF d clock reset q) d_wires q_wires

  { name := s!"Register{n}"
    inputs := d_wires ++ [clock, reset]
    outputs := q_wires
    gates := gates
    instances := []
  }

-- Specific widths for convenience
def mkRegister1 : Circuit := mkRegisterN 1
def mkRegister4 : Circuit := mkRegisterN 4
def mkRegister8 : Circuit := mkRegisterN 8
def mkRegister16 : Circuit := mkRegisterN 16
def mkRegister32 : Circuit := mkRegisterN 32

-- Helper: Extract the number of DFFs in a register circuit
def registerWidth (c : Circuit) : Nat :=
  c.gates.filter (fun g => g.gateType == GateType.DFF) |>.length

-- TODO: Complete proof (requires showing filter keeps all DFFs)
/-
theorem registerWidth_correct (n : Nat) :
  registerWidth (mkRegisterN n) = n := by
  simp [registerWidth, mkRegisterN]
  sorry
-/

end Shoumei.Circuits.Sequential

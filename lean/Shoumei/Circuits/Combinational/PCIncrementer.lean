/-
Circuits/Combinational/PCIncrementer.lean - 32-bit Program Counter Incrementers (+4 and +8)

Dedicated gate-level incrementers for PC+4 and PC+8 without unused inputs or constant tie-offs.
Eliminates LINT-32 (constant input) and LINT-33 (shared constant net) warnings by construction.
-/

import Shoumei.DSL

namespace Shoumei.Circuits.Combinational

open Shoumei

/-- Build a 32-bit incrementer for PC + 4 or PC + 8.
    Inputs:  pc[31:0]
    Outputs: pc_next[31:0]
    No constant inputs (zero/one/cin) - all logic is self-contained. -/
def mkPCIncrementer (name : String) (inc : Nat) : Circuit :=
  let pc := (List.range 32).map fun i => Wire.mk s!"pc_{i}"
  let pc_next := (List.range 32).map fun i => Wire.mk s!"pc_next_{i}"

  let startBit := if inc == 8 then 3 else 2

  -- Lower bits: pass through with NOT-NOT inverter pair to prevent feedthrough warnings
  let lowerGates := (List.range startBit).flatMap fun i =>
    let mid := Wire.mk s!"pci_mid_{i}"
    [Gate.mkNOT pc[i]! mid, Gate.mkNOT mid pc_next[i]!]

  -- Toggle bit: inverted bit produces sum, original bit acts as carry
  let toggleGate := Gate.mkNOT pc[startBit]! pc_next[startBit]!
  let carryStart := pc[startBit]!

  -- Upper bits: ripple half-adder carry chain
  let rec buildChain (i : Nat) (carryIn : Wire) : List Gate :=
    if i >= 32 then []
    else
      let sumGate := Gate.mkXOR pc[i]! carryIn pc_next[i]!
      if i == 31 then
        [sumGate]
      else
        let carryOut := Wire.mk s!"pci_c_{i}"
        let carryGate := Gate.mkAND pc[i]! carryIn carryOut
        sumGate :: carryGate :: buildChain (i + 1) carryOut

  let upperGates := toggleGate :: buildChain (startBit + 1) carryStart
  let allGates := lowerGates ++ upperGates

  { name := name
    inputs := pc
    outputs := pc_next
    gates := allGates
    instances := []
    signalGroups := [
      { name := "pc", width := 32, wires := pc },
      { name := "pc_next", width := 32, wires := pc_next }
    ]
    keepHierarchy := true
  }

/-- PC+4 incrementer (32-bit). -/
def pcIncrementer4Circuit : Circuit := mkPCIncrementer "PCIncrementer4" 4

/-- PC+8 incrementer (32-bit). -/
def pcIncrementer8Circuit : Circuit := mkPCIncrementer "PCIncrementer8" 8

end Shoumei.Circuits.Combinational

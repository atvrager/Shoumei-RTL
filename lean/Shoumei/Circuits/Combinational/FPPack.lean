/-
Circuits/Combinational/FPPack.lean - IEEE 754 Binary32 Packing Circuit

Assembles sign, exponent, and mantissa into a 32-bit IEEE 754 single-precision
float. Supports a special-value bypass for NaN, Inf, and Zero.

Inputs:
  - sign (1 bit)
  - exp[7:0] (8 bits) - biased exponent
  - mant[22:0] (23 bits) - mantissa (without implicit bit)
  - is_special (1 bit) - bypass to special_val when high
  - special_val[31:0] (32 bits) - value for NaN/Inf/Zero

Outputs:
  - result[31:0] (32 bits) - packed IEEE 754 SP value

Implementation:
  1. BUF gates assemble normal[31:0] from sign, exp, mant
  2. MUX gates select between normal and special_val per bit
-/

import Shoumei.DSL

namespace Shoumei.Circuits.Combinational

open Shoumei

private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

/-- IEEE 754 binary32 packing circuit. -/
def fpPackCircuit : Circuit :=
  let sign := Wire.mk "sign"
  let is_special := Wire.mk "is_special"
  let expWires := makeIndexedWires "exp" 8
  let mantWires := makeIndexedWires "mant" 23
  let specialWires := makeIndexedWires "special_val" 32
  let normalWires := makeIndexedWires "normal" 32
  let resultWires := makeIndexedWires "result" 32

  -- Step 1: Assemble normal[31:0] via BUF gates
  --   normal[22:0]  = mant[22:0]
  --   normal[30:23] = exp[7:0]
  --   normal[31]    = sign
  let mantBufs := (List.range 23).map fun i =>
    Gate.mkBUF (mantWires[i]!) (normalWires[i]!)
  let expBufs := (List.range 8).map fun i =>
    Gate.mkBUF (expWires[i]!) (normalWires[23 + i]!)
  let signBuf := Gate.mkBUF sign (normalWires[31]!)

  -- Step 2: MUX for each result bit
  --   result[i] = is_special ? special_val[i] : normal[i]
  let muxGates := (List.range 32).map fun i =>
    Gate.mkMUX (normalWires[i]!) (specialWires[i]!) is_special (resultWires[i]!)

  { name := "FPPack"
    inputs := [sign] ++ expWires ++ mantWires ++ [is_special] ++ specialWires
    outputs := resultWires
    gates := mantBufs ++ expBufs ++ [signBuf] ++ muxGates
    instances := []
    signalGroups := [
      { name := "exp",         width := 8,  wires := expWires },
      { name := "mant",        width := 23, wires := mantWires },
      { name := "special_val", width := 32, wires := specialWires },
      { name := "result",      width := 32, wires := resultWires }
    ]
  }

end Shoumei.Circuits.Combinational

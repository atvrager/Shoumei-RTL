/-
Circuits/Combinational/OneHotEncoder.lean - One-Hot to Binary Encoder

Converts a 64-bit one-hot input to a 6-bit binary output.
Used by BitmapFreeList to convert priority arbiter grant to preg index.

For output bit b (0..5): OR all input[i] where bit b of i is set.
Each output bit is a 32-input OR tree.
-/

import Shoumei.DSL

namespace Shoumei.Circuits.Combinational

open Shoumei

/--
Build a one-hot to binary encoder (64→6).

For each output bit b, OR together all inputs[i] where (i >> b) & 1 == 1.

Ports:
- Inputs: input[63:0] (one-hot)
- Outputs: output[5:0] (binary index)
-/
def mkOneHotEncoder64 : Circuit :=
  let n := 64
  let outWidth := 6
  let input := (List.range n).map (fun i => Wire.mk s!"in_{i}")
  let output := (List.range outWidth).map (fun i => Wire.mk s!"out_{i}")

  -- For each output bit b, build an OR tree of all inputs where bit b is set
  let allGates := (List.range outWidth).foldl (fun acc b =>
    -- Collect indices where bit b is set
    let indices := (List.range n).filter (fun i => (i / (2^b)) % 2 == 1)
    -- Build OR tree for these indices
    if indices.length == 0 then
      acc ++ [Gate.mkBUF (Wire.mk "zero") (output[b]!)]
    else if indices.length == 1 then
      acc ++ [Gate.mkBUF (input[indices[0]!]!) (output[b]!)]
    else
      -- Linear OR chain
      let (gates, _) := indices.tail!.enum.foldl (fun (gates, prevWire) (idx, i) =>
        let inWire := input[i]!
        let orWire := if idx == indices.tail!.length - 1
                      then output[b]!
                      else Wire.mk s!"enc_or_{b}_{idx}"
        let g := Gate.mkOR prevWire inWire orWire
        (gates ++ [g], orWire)
      ) ([], input[indices[0]!]!)
      acc ++ gates
  ) []

  { name := "OneHotEncoder64"
    inputs := input
    outputs := output
    gates := allGates
    instances := []
    signalGroups := [
      { name := "in", width := n, wires := input },
      { name := "out", width := outWidth, wires := output }
    ]
  }

end Shoumei.Circuits.Combinational

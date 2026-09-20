/-
Circuits/Combinational/CarrySelectAdder.lean - Blocked carry-select adder

Blocks of eight bits.  The low block ripples the carry in directly.  Each
upper block is built twice -- once assuming its carry-in is 0 and once
assuming 1 -- and a mux picks between the two sums and carry-outs from the
previous block's carry.  Trade area for carry depth: `width/8 + 1` levels
instead of `width`.

    a[7:0] b[7:0]          a[15:8] b[15:8]
        |                      |
     [ RCA cin ]           [ RCA | RCA ]     cin=0, cin=1
        |  c0                  |  sums0/sums1, c0', c1'
        |                      |
        +---- select ----------+  sum[15:8] = c0 ? sums1 : sums0
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.PrefixAdder

namespace Shoumei.Circuits.Combinational

open Shoumei
open Shoumei.Components

/-- Block width for the carry-select split. -/
def carrySelectBlock : Nat := 8

/-- Module name for a carry-select adder. -/
def carrySelectName (width : Nat) (cin : CinMode) : String :=
  match cin with
  | .none  => s!"CarrySelectAdder{width}NoCin"
  | .input => s!"CarrySelectAdder{width}"
  | .one   => s!"CarrySelectAdder{width}WithCin1"

/-- Build a blocked carry-select adder. -/
def mkCarrySelectAdderCircuit (width : Nat) (cin : CinMode) : Circuit :=
  let a := makeIndexedWires "a" width
  let b := makeIndexedWires "b" width
  let sum := makeIndexedWires "sum" width

  let cinWire : Wire :=
    match cin with
    | .none  => Wire.mk "zero"
    | .input => Wire.mk "cin"
    | .one   => Wire.mk "one"

  let nBlocks := (width + carrySelectBlock - 1) / carrySelectBlock

  -- Fold blocks, threading the selected carry-out of each into the next.
  let (gates, _carry) := (List.range nBlocks).foldl
    (fun (acc : List Gate × Wire) k =>
      let lo := k * carrySelectBlock
      let hi := min ((k + 1) * carrySelectBlock) width
      let n := hi - lo
      let blkA := (List.range n).map fun i => a[lo + i]!
      let blkB := (List.range n).map fun i => b[lo + i]!
      let blkSum := (List.range n).map fun i => sum[lo + i]!
      let (accG, carryIn) := acc
      if k == 0 then
        -- Low block: ripple the real carry-in.
        let (gs, cout) := mkPrefixAdd .rippleCarry blkA blkB (some carryIn) blkSum s!"cs_b{k}"
        (accG ++ gs, cout)
      else
        -- Upper block: two copies (carry-in 0 and 1), then a select mux.
        let s0 := makeIndexedWires s!"cs_b{k}_s0" n
        let s1 := makeIndexedWires s!"cs_b{k}_s1" n
        let (g0, c0) := mkPrefixAdd .rippleCarry blkA blkB (some (Wire.mk "zero")) s0 s!"cs_b{k}_c0"
        let (g1, c1) := mkPrefixAdd .rippleCarry blkA blkB (some (Wire.mk "one")) s1 s!"cs_b{k}_c1"
        let selGates := (List.range n).map fun i => Gate.mkMUX s0[i]! s1[i]! carryIn blkSum[i]!
        let cSel := Wire.mk s!"cs_b{k}_cout"
        (accG ++ g0 ++ g1 ++ selGates ++ [Gate.mkMUX c0 c1 carryIn cSel], cSel)
    ) ([], cinWire)

  let inputs := a ++ b ++ (match cin with | .input => [Wire.mk "cin"] | _ => [])
  let groups := [
    { name := "a", width := width, wires := a },
    { name := "b", width := width, wires := b },
    { name := "sum", width := width, wires := sum }
  ] ++ (match cin with
        | .input => [{ name := "cin", width := 1, wires := [Wire.mk "cin"] }]
        | _ => [])

  { name := carrySelectName width cin
    inputs := inputs
    outputs := sum
    gates := gates
    instances := []
    signalGroups := groups
    keepHierarchy := true
  }

end Shoumei.Circuits.Combinational
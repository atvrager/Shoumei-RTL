/-
Circuits/Combinational/KoggeStoneAdder.lean - 64-bit Kogge-Stone Parallel Prefix Adder

A 64-bit adder with O(log₂ n) = 6 levels of delay, replacing the O(n) ripple-carry
adder on the critical path of the pipelined multiplier.

Architecture (Kogge-Stone parallel prefix):
  Level 0: Generate initial (G, P) pairs: G_i = a_i AND b_i, P_i = a_i XOR b_i
  Levels 1-6: Parallel prefix computation with stride 1, 2, 4, 8, 16, 32
    G(i:j) = G(i:k) OR (P(i:k) AND G(k-1:j))
    P(i:j) = P(i:k) AND P(k-1:j)
  Final: sum_i = P_i XOR carry_{i-1}, where carry_i = G(i:0)

Interface:
  Inputs:  a[63:0], b[63:0], cin
  Outputs: sum[63:0]
  Gates:   ~960 (64 initial pairs + 6 levels × ~64 prefix cells × 3 gates + 64 final XORs)
  Depth:   8 gate levels (1 initial + 6 prefix + 1 final)
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.RippleCarryAdder

namespace Shoumei.Circuits.Combinational

open Shoumei

/-- Build a 64-bit Kogge-Stone parallel prefix adder.

    This is a gate-level implementation with O(log₂ 64) = 6 prefix levels,
    giving ~8 gate delays total vs 64 for ripple carry.

    Inputs:  a[63:0], b[63:0], cin
    Outputs: sum[63:0] -/
def mkKoggeStoneAdder64 : Circuit :=
  let width := 64
  let a := makeIndexedWires "a" width
  let b := makeIndexedWires "b" width
  let cin := Wire.mk "cin"
  let sum := makeIndexedWires "sum" width

  -- Level 0: Initial generate and propagate
  -- G_i = a_i AND b_i
  -- P_i = a_i XOR b_i
  let g0 := makeIndexedWires "g0" width
  let p0 := makeIndexedWires "p0" width
  let init_gates := List.flatten <| (List.range width).map fun i =>
    [ Gate.mkAND (a[i]!) (b[i]!) (g0[i]!),
      Gate.mkXOR (a[i]!) (b[i]!) (p0[i]!) ]

  -- Handle cin: merge cin into bit 0's generate
  -- g0'[0] = g0[0] OR (p0[0] AND cin)
  let p0_cin := Wire.mk "p0_cin"
  let g0_merged := Wire.mk "g0_merged"
  let cin_gates := [
    Gate.mkAND (p0[0]!) cin p0_cin,
    Gate.mkOR (g0[0]!) p0_cin g0_merged
  ]

  -- Prefix levels 1-6 (strides 1, 2, 4, 8, 16, 32)
  -- At each level, for bit i with stride s:
  --   If i >= s: G_new[i] = G_prev[i] OR (P_prev[i] AND G_prev[i-s])
  --             P_new[i] = P_prev[i] AND P_prev[i-s]
  --   Else:     G_new[i] = G_prev[i], P_new[i] = P_prev[i] (pass through)

  -- We'll build 6 levels with strides [1, 2, 4, 8, 16, 32]
  let levels := [1, 2, 4, 8, 16, 32]

  -- Accumulate gates and track current G/P wire names
  -- After level 0, g_prev[0] = g0_merged, g_prev[i>0] = g0[i], p_prev = p0
  let (all_prefix_gates, final_g, _final_p) :=
    levels.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
      let (gates_acc, g_prev, p_prev) := acc
      let level_tag := s!"l{stride}"
      let g_new := makeIndexedWires s!"g{level_tag}" width
      let p_new := makeIndexedWires s!"p{level_tag}" width

      let level_gates := List.flatten <| (List.range width).map fun i =>
        if i < stride then
          -- Pass through
          [ Gate.mkBUF (g_prev[i]!) (g_new[i]!),
            Gate.mkBUF (p_prev[i]!) (p_new[i]!) ]
        else
          -- Prefix merge
          let pg := Wire.mk s!"pg_{level_tag}_{i}"
          [ Gate.mkAND (p_prev[i]!) (g_prev[i - stride]!) pg,
            Gate.mkOR (g_prev[i]!) pg (g_new[i]!),
            Gate.mkAND (p_prev[i]!) (p_prev[i - stride]!) (p_new[i]!) ]

      (gates_acc ++ level_gates, g_new, p_new)
    )
    -- Initial state: g_prev with cin merged at bit 0
    ([], ([g0_merged] ++ (List.range (width - 1)).map fun i => g0[i + 1]!), p0)

  -- Final sum computation
  -- sum[0] = p0[0] XOR cin
  -- sum[i] = p0[i] XOR final_g[i-1]  (for i > 0)
  let sum_gates :=
    [Gate.mkXOR (p0[0]!) cin (sum[0]!)] ++
    ((List.range (width - 1)).map fun i =>
      Gate.mkXOR (p0[i + 1]!) (final_g[i]!) (sum[i + 1]!))

  { name := "KoggeStoneAdder64"
    inputs := a ++ b ++ [cin]
    outputs := sum
    gates := init_gates ++ cin_gates ++ all_prefix_gates ++ sum_gates
    instances := []
    signalGroups := [
      { name := "a", width := width, wires := a },
      { name := "b", width := width, wires := b },
      { name := "sum", width := width, wires := sum }
    ]
    keepHierarchy := true
  }

/-- Convenience alias. -/
def koggeStoneAdder64 : Circuit := mkKoggeStoneAdder64

/-- Build a 32-bit Kogge-Stone parallel prefix adder.

    This is a gate-level implementation with O(log₂ 32) = 5 prefix levels,
    giving ~7 gate delays total vs 32 for ripple carry.

    Inputs:  a[31:0], b[31:0], cin
    Outputs: sum[31:0] -/
def mkKoggeStoneAdder32 : Circuit :=
  let width := 32
  let a := makeIndexedWires "a" width
  let b := makeIndexedWires "b" width
  let cin := Wire.mk "cin"
  let sum := makeIndexedWires "sum" width

  -- Level 0: Initial generate and propagate
  let g0 := makeIndexedWires "g0" width
  let p0 := makeIndexedWires "p0" width
  let init_gates := List.flatten <| (List.range width).map fun i =>
    [ Gate.mkAND (a[i]!) (b[i]!) (g0[i]!),
      Gate.mkXOR (a[i]!) (b[i]!) (p0[i]!) ]

  -- Handle cin: merge cin into bit 0's generate
  let p0_cin := Wire.mk "p0_cin"
  let g0_merged := Wire.mk "g0_merged"
  let cin_gates := [
    Gate.mkAND (p0[0]!) cin p0_cin,
    Gate.mkOR (g0[0]!) p0_cin g0_merged
  ]

  -- Prefix levels 1-5 (strides 1, 2, 4, 8, 16)
  let levels := [1, 2, 4, 8, 16]

  let (all_prefix_gates, final_g, _final_p) :=
    levels.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
      let (gates_acc, g_prev, p_prev) := acc
      let level_tag := s!"l{stride}"
      let g_new := makeIndexedWires s!"g{level_tag}" width
      let p_new := makeIndexedWires s!"p{level_tag}" width

      let level_gates := List.flatten <| (List.range width).map fun i =>
        if i < stride then
          [ Gate.mkBUF (g_prev[i]!) (g_new[i]!),
            Gate.mkBUF (p_prev[i]!) (p_new[i]!) ]
        else
          let pg := Wire.mk s!"pg_{level_tag}_{i}"
          [ Gate.mkAND (p_prev[i]!) (g_prev[i - stride]!) pg,
            Gate.mkOR (g_prev[i]!) pg (g_new[i]!),
            Gate.mkAND (p_prev[i]!) (p_prev[i - stride]!) (p_new[i]!) ]

      (gates_acc ++ level_gates, g_new, p_new)
    )
    ([], ([g0_merged] ++ (List.range (width - 1)).map fun i => g0[i + 1]!), p0)

  -- Final sum computation
  let sum_gates :=
    [Gate.mkXOR (p0[0]!) cin (sum[0]!)] ++
    ((List.range (width - 1)).map fun i =>
      Gate.mkXOR (p0[i + 1]!) (final_g[i]!) (sum[i + 1]!))

  { name := "KoggeStoneAdder32"
    inputs := a ++ b ++ [cin]
    outputs := sum
    gates := init_gates ++ cin_gates ++ all_prefix_gates ++ sum_gates
    instances := []
    signalGroups := [
      { name := "a", width := width, wires := a },
      { name := "b", width := width, wires := b },
      { name := "sum", width := width, wires := sum }
    ]
    keepHierarchy := true
  }

/-- Convenience alias. -/
def koggeStoneAdder32 : Circuit := mkKoggeStoneAdder32

/-- Inline Kogge-Stone adder gate generator (parameterized width).

    Like `mkRippleAdd` but with O(log n) carry delay instead of O(n).
    Returns (gates, carry_out). All wire names are prefixed with `pfx`.

    a, b: n-bit inputs (LSB first). carry_in: single wire.
    sum_out: n-bit output wires (LSB first). -/
def mkKoggeStoneAdd (a b : List Wire) (carry_in : Wire)
    (sum_out : List Wire) (pfx : String) : List Gate × Wire :=
  let n := a.length
  if n == 0 then ([], carry_in)
  else
  -- Level 0: Initial generate and propagate
  let g0 := makeIndexedWires (pfx ++ "_g0") n
  let p0 := makeIndexedWires (pfx ++ "_p0") n
  let init_gates := List.flatten <| (List.range n).map fun i =>
    [ Gate.mkAND (a[i]!) (b[i]!) (g0[i]!),
      Gate.mkXOR (a[i]!) (b[i]!) (p0[i]!) ]

  -- Merge carry_in into bit 0's generate
  let p0_cin := Wire.mk (pfx ++ "_p0cin")
  let g0_merged := Wire.mk (pfx ++ "_g0m")
  let cin_gates := [
    Gate.mkAND (p0[0]!) carry_in p0_cin,
    Gate.mkOR (g0[0]!) p0_cin g0_merged
  ]

  -- Compute prefix levels: strides 1, 2, 4, ... up to n
  let strides := (List.range 20).filterMap fun k =>
    let s := 1 <<< k
    if s < n then some s else none

  let (all_prefix_gates, final_g, _final_p) :=
    strides.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
      let (gates_acc, g_prev, p_prev) := acc
      let lt := pfx ++ "_l" ++ toString stride
      let g_new := makeIndexedWires (lt ++ "_g") n
      let p_new := makeIndexedWires (lt ++ "_p") n

      let level_gates := List.flatten <| (List.range n).map fun i =>
        if i < stride then
          [ Gate.mkBUF (g_prev[i]!) (g_new[i]!),
            Gate.mkBUF (p_prev[i]!) (p_new[i]!) ]
        else
          let pg := Wire.mk (lt ++ "_pg_" ++ toString i)
          [ Gate.mkAND (p_prev[i]!) (g_prev[i - stride]!) pg,
            Gate.mkOR (g_prev[i]!) pg (g_new[i]!),
            Gate.mkAND (p_prev[i]!) (p_prev[i - stride]!) (p_new[i]!) ]

      (gates_acc ++ level_gates, g_new, p_new)
    )
    ([], ([g0_merged] ++ (List.range (n - 1)).map fun i => g0[i + 1]!), p0)

  -- Final sum: sum[0] = p0[0] XOR cin, sum[i] = p0[i] XOR final_g[i-1]
  let sum_gates :=
    [Gate.mkXOR (p0[0]!) carry_in (sum_out[0]!)] ++
    ((List.range (n - 1)).map fun i =>
      Gate.mkXOR (p0[i + 1]!) (final_g[i]!) (sum_out[i + 1]!))

  -- carry_out = final_g[n-1]
  let cout := Wire.mk (pfx ++ "_cout")
  let cout_gate := Gate.mkBUF (final_g[n - 1]!) cout

  (init_gates ++ cin_gates ++ all_prefix_gates ++ sum_gates ++ [cout_gate], cout)

/-- Inline Kogge-Stone subtractor: out = a - b = a + ~b + 1.
    Returns (gates, borrow_out) where borrow = NOT carry_out. -/
def mkKoggeStoneSub (a b : List Wire) (sum_out : List Wire)
    (pfx : String) (one_wire : Wire) : List Gate × Wire :=
  let n := b.length
  let inv_b := makeIndexedWires (pfx ++ "_invb") n
  let inv_gates := (List.range n).map fun i => Gate.mkNOT (b[i]!) (inv_b[i]!)
  let (add_gates, carry_out) := mkKoggeStoneAdd a inv_b one_wire sum_out (pfx ++ "_add")
  let borrow_wire := Wire.mk (pfx ++ "_borrow")
  let borrow_gate := Gate.mkNOT carry_out borrow_wire
  (inv_gates ++ add_gates ++ [borrow_gate], borrow_wire)

end Shoumei.Circuits.Combinational

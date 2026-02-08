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
  }

/-- Convenience alias. -/
def koggeStoneAdder64 : Circuit := mkKoggeStoneAdder64

end Shoumei.Circuits.Combinational

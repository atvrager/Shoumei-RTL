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
  let g0 := (List.range width).map (fun i => Wire.mk s!"ksag0x{i}")
  let p0 := (List.range width).map (fun i => Wire.mk s!"ksap0x{i}")
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
      let g_new := (List.range width).map (fun i => Wire.mk s!"ksag{level_tag}x{i}")
      let p_new := (List.range width).map (fun i => Wire.mk s!"ksap{level_tag}x{i}")

      let level_gates := List.flatten <| (List.range width).map fun i =>
        if i < stride then
          -- Pass through
          [ Gate.mkBUF (g_prev[i]!) (g_new[i]!),
            Gate.mkBUF (p_prev[i]!) (p_new[i]!) ]
        else
          -- Prefix merge
          let pg := Wire.mk s!"ksapg{level_tag}x{i}"
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

/-- Build a 64-bit Kogge-Stone parallel prefix adder without carry-in.
    Inputs:  a[63:0], b[63:0]
    Outputs: sum[63:0] -/
def mkKoggeStoneAdder64NoCin : Circuit :=
  let width := 64
  let a := makeIndexedWires "a" width
  let b := makeIndexedWires "b" width
  let sum := makeIndexedWires "sum" width

  let g0 := (List.range width).map (fun i => Wire.mk s!"ksag0x{i}")
  let p0 := (List.range width).map (fun i => Wire.mk s!"ksap0x{i}")
  let init_gates := List.flatten <| (List.range width).map fun i =>
    [ Gate.mkAND (a[i]!) (b[i]!) (g0[i]!),
      Gate.mkXOR (a[i]!) (b[i]!) (p0[i]!) ]

  let levels := [1, 2, 4, 8, 16, 32]

  let (all_prefix_gates, final_g, _final_p) :=
    levels.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
      let (gates_acc, g_prev, p_prev) := acc
      let level_tag := s!"l{stride}"
      let g_new := (List.range width).map (fun i => Wire.mk s!"ksag{level_tag}x{i}")
      let p_new := (List.range width).map (fun i => Wire.mk s!"ksap{level_tag}x{i}")

      let level_gates := List.flatten <| (List.range width).map fun i =>
        if i < stride then
          [ Gate.mkBUF (g_prev[i]!) (g_new[i]!),
            Gate.mkBUF (p_prev[i]!) (p_new[i]!) ]
        else
          let pg := Wire.mk s!"ksapg{level_tag}x{i}"
          [ Gate.mkAND (p_prev[i]!) (g_prev[i - stride]!) pg,
            Gate.mkOR (g_prev[i]!) pg (g_new[i]!),
            Gate.mkAND (p_prev[i]!) (p_prev[i - stride]!) (p_new[i]!) ]

      (gates_acc ++ level_gates, g_new, p_new)
    )
    ([], g0, p0)

  let sum_gates :=
    [Gate.mkBUF (p0[0]!) (sum[0]!)] ++
    ((List.range (width - 1)).map fun i =>
      Gate.mkXOR (p0[i + 1]!) (final_g[i]!) (sum[i + 1]!))

  { name := "KoggeStoneAdder64NoCin"
    inputs := a ++ b
    outputs := sum
    gates := init_gates ++ all_prefix_gates ++ sum_gates
    instances := []
    signalGroups := [
      { name := "a", width := width, wires := a },
      { name := "b", width := width, wires := b },
      { name := "sum", width := width, wires := sum }
    ]
    keepHierarchy := true
  }

def koggeStoneAdder64NoCin : Circuit := mkKoggeStoneAdder64NoCin

/-- 64-bit Adder with b[0]=0 and cin=0 for multiplier final addition.
    Inputs: a[63:0], b[63:1] (63 bits, since b[0]=0)
    Outputs: sum[63:0]
    Bit 0: sum[0] = a[0] (passed through via BUF)
    Bits 1..63: 63-bit Kogge-Stone addition of a[63:1] + b[63:1]
-/
def mkMulFinalAdder64 : Circuit :=
  let width := 64
  let a := makeIndexedWires "a" width
  let b := (List.range 63).map (fun i => Wire.mk s!"b_{i + 1}")
  let sum := makeIndexedWires "sum" width

  -- Bit 0: NOT-NOT inverter pair (prevents LINT-29 feedthrough warning)
  let mid0 := Wire.mk "mfa_mid_0"
  let bit0_gates := [
    Gate.mkNOT (a[0]!) mid0,
    Gate.mkNOT mid0 (sum[0]!)
  ]

  -- Lower block: 31 bits (bits 1..31 of sum, from a[31:1] + b[30:0])
  let width_lo := 31
  let g0_lo := (List.range width_lo).map (fun i => Wire.mk s!"mfa_g0_lo_{i}")
  let p0_lo := (List.range width_lo).map (fun i => Wire.mk s!"mfa_p0_lo_{i}")
  let init_lo := List.flatten <| (List.range width_lo).map fun i =>
    let idx := i + 1
    [ Gate.mkAND (a[idx]!) (b[i]!) (g0_lo[i]!),
      Gate.mkXOR (a[idx]!) (b[i]!) (p0_lo[i]!) ]

  let levels_lo := [1, 2, 4, 8, 16]
  let (pfx_lo, final_g_lo, _) :=
    levels_lo.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
      let (gates_acc, g_prev, p_prev) := acc
      let level_tag := s!"lol{stride}"
      let g_new := (List.range width_lo).map (fun i => Wire.mk s!"mfag{level_tag}x{i}")
      let p_new := (List.range width_lo).map (fun i => Wire.mk s!"mfap{level_tag}x{i}")
      let level_gates := List.flatten <| (List.range width_lo).map fun i =>
        if i < stride then
          [ Gate.mkBUF (g_prev[i]!) (g_new[i]!),
            Gate.mkBUF (p_prev[i]!) (p_new[i]!) ]
        else
          let pg := Wire.mk s!"mfapg{level_tag}x{i}"
          [ Gate.mkAND (p_prev[i]!) (g_prev[i - stride]!) pg,
            Gate.mkOR (g_prev[i]!) pg (g_new[i]!),
            Gate.mkAND (p_prev[i]!) (p_prev[i - stride]!) (p_new[i]!) ]
      (gates_acc ++ level_gates, g_new, p_new)
    ) ([], g0_lo, p0_lo)

  let sum_lo_gates :=
    [Gate.mkBUF (p0_lo[0]!) (sum[1]!)] ++
    ((List.range (width_lo - 1)).map fun i =>
      Gate.mkXOR (p0_lo[i + 1]!) (final_g_lo[i]!) (sum[i + 2]!))

  let c31 := final_g_lo[width_lo - 1]!
  let c31_bufs := (List.range 4).map (fun g => Wire.mk s!"mfac31_b{g}")
  let c31_buf_gates := (List.range 4).map (fun g =>
    Gate.mkBUF c31 (c31_bufs[g]!))

  -- Upper block: 32 bits (bits 32..63 of sum, from a[63:32] + b[62:31])
  let width_hi := 32
  let g0_hi := (List.range width_hi).map (fun i => Wire.mk s!"mfa_g0_hi_{i}")
  let p0_hi := (List.range width_hi).map (fun i => Wire.mk s!"mfa_p0_hi_{i}")
  let init_hi := List.flatten <| (List.range width_hi).map fun i =>
    let a_idx := 32 + i
    let b_idx := 31 + i
    [ Gate.mkAND (a[a_idx]!) (b[b_idx]!) (g0_hi[i]!),
      Gate.mkXOR (a[a_idx]!) (b[b_idx]!) (p0_hi[i]!) ]

  -- Upper block speculative tree 0 (cin = 0)
  let sum0 := makeIndexedWires "mfas0_hi" width_hi
  let (pfx_hi0, final_g_hi0, _) :=
    levels_lo.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
      let (gates_acc, g_prev, p_prev) := acc
      let level_tag := s!"hi0l{stride}"
      let g_new := (List.range width_hi).map (fun i => Wire.mk s!"mfag{level_tag}x{i}")
      let p_new := (List.range width_hi).map (fun i => Wire.mk s!"mfap{level_tag}x{i}")
      let level_gates := List.flatten <| (List.range width_hi).map fun i =>
        if i < stride then
          [ Gate.mkBUF (g_prev[i]!) (g_new[i]!),
            Gate.mkBUF (p_prev[i]!) (p_new[i]!) ]
        else
          let pg := Wire.mk s!"mfapg{level_tag}x{i}"
          [ Gate.mkAND (p_prev[i]!) (g_prev[i - stride]!) pg,
            Gate.mkOR (g_prev[i]!) pg (g_new[i]!),
            Gate.mkAND (p_prev[i]!) (p_prev[i - stride]!) (p_new[i]!) ]
      (gates_acc ++ level_gates, g_new, p_new)
    ) ([], g0_hi, p0_hi)

  let sum0_gates :=
    [Gate.mkBUF (p0_hi[0]!) (sum0[0]!)] ++
    ((List.range (width_hi - 1)).map fun i =>
      Gate.mkXOR (p0_hi[i + 1]!) (final_g_hi0[i]!) (sum0[i + 1]!))

  -- Upper block speculative tree 1 (cin = 1)
  let sum1 := makeIndexedWires "mfas1_hi" width_hi
  let g0_hi_m0 := Wire.mk "mfa_g0_hi_m0"
  let cin1_gate := Gate.mkOR (a[32]!) (b[31]!) g0_hi_m0
  let g0_hi1 := [g0_hi_m0] ++ (List.range (width_hi - 1)).map (fun i => g0_hi[i + 1]!)

  let (pfx_hi1, final_g_hi1, _) :=
    levels_lo.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
      let (gates_acc, g_prev, p_prev) := acc
      let level_tag := s!"hi1l{stride}"
      let g_new := (List.range width_hi).map (fun i => Wire.mk s!"mfag{level_tag}x{i}")
      let p_new := (List.range width_hi).map (fun i => Wire.mk s!"mfap{level_tag}x{i}")
      let level_gates := List.flatten <| (List.range width_hi).map fun i =>
        if i < stride then
          [ Gate.mkBUF (g_prev[i]!) (g_new[i]!),
            Gate.mkBUF (p_prev[i]!) (p_new[i]!) ]
        else
          let pg := Wire.mk s!"mfapg{level_tag}x{i}"
          [ Gate.mkAND (p_prev[i]!) (g_prev[i - stride]!) pg,
            Gate.mkOR (g_prev[i]!) pg (g_new[i]!),
            Gate.mkAND (p_prev[i]!) (p_prev[i - stride]!) (p_new[i]!) ]
      (gates_acc ++ level_gates, g_new, p_new)
    ) ([], g0_hi1, p0_hi)

  let sum1_gates :=
    [Gate.mkNOT (p0_hi[0]!) (sum1[0]!)] ++
    ((List.range (width_hi - 1)).map fun i =>
      Gate.mkXOR (p0_hi[i + 1]!) (final_g_hi1[i]!) (sum1[i + 1]!))

  let sel_gates := (List.range width_hi).map fun i =>
    let grp := i / 8
    Gate.mkMUX (sum0[i]!) (sum1[i]!) (c31_bufs[grp]!) (sum[32 + i]!)

  { name := "MulFinalAdder64"
    inputs := a ++ b
    outputs := sum
    gates := bit0_gates ++ init_lo ++ pfx_lo ++ sum_lo_gates ++
             c31_buf_gates ++
             init_hi ++ pfx_hi0 ++ sum0_gates ++
             [cin1_gate] ++ pfx_hi1 ++ sum1_gates ++ sel_gates
    instances := []
    signalGroups := [
      { name := "a", width := width, wires := a },
      { name := "b", width := 63, wires := b },
      { name := "sum", width := width, wires := sum }
    ]
    keepHierarchy := true
  }

def mulFinalAdder64 : Circuit := mkMulFinalAdder64

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
  let g0 := (List.range width).map (fun i => Wire.mk s!"ksag0x{i}")
  let p0 := (List.range width).map (fun i => Wire.mk s!"ksap0x{i}")
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
      let g_new := (List.range width).map (fun i => Wire.mk s!"ksag{level_tag}x{i}")
      let p_new := (List.range width).map (fun i => Wire.mk s!"ksap{level_tag}x{i}")

      let level_gates := List.flatten <| (List.range width).map fun i =>
        if i < stride then
          [ Gate.mkBUF (g_prev[i]!) (g_new[i]!),
            Gate.mkBUF (p_prev[i]!) (p_new[i]!) ]
        else
          let pg := Wire.mk s!"ksapg{level_tag}x{i}"
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

/-- Build a 32-bit Kogge-Stone parallel prefix adder without carry-in.
    Inputs:  a[31:0], b[31:0]
    Outputs: sum[31:0] -/
def mkKoggeStoneAdder32NoCin : Circuit :=
  let width := 32
  let a := makeIndexedWires "a" width
  let b := makeIndexedWires "b" width
  let sum := makeIndexedWires "sum" width

  let g0 := (List.range width).map (fun i => Wire.mk s!"ksag0x{i}")
  let p0 := (List.range width).map (fun i => Wire.mk s!"ksap0x{i}")
  let init_gates := List.flatten <| (List.range width).map fun i =>
    [ Gate.mkAND (a[i]!) (b[i]!) (g0[i]!),
      Gate.mkXOR (a[i]!) (b[i]!) (p0[i]!) ]

  let levels := [1, 2, 4, 8, 16]

  let (all_prefix_gates, final_g, _final_p) :=
    levels.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
      let (gates_acc, g_prev, p_prev) := acc
      let level_tag := s!"l{stride}"
      let g_new := (List.range width).map (fun i => Wire.mk s!"ksag{level_tag}x{i}")
      let p_new := (List.range width).map (fun i => Wire.mk s!"ksap{level_tag}x{i}")

      let level_gates := List.flatten <| (List.range width).map fun i =>
        if i < stride then
          [ Gate.mkBUF (g_prev[i]!) (g_new[i]!),
            Gate.mkBUF (p_prev[i]!) (p_new[i]!) ]
        else
          let pg := Wire.mk s!"ksapg{level_tag}x{i}"
          [ Gate.mkAND (p_prev[i]!) (g_prev[i - stride]!) pg,
            Gate.mkOR (g_prev[i]!) pg (g_new[i]!),
            Gate.mkAND (p_prev[i]!) (p_prev[i - stride]!) (p_new[i]!) ]

      (gates_acc ++ level_gates, g_new, p_new)
    )
    ([], g0, p0)

  let sum_gates :=
    [Gate.mkBUF (p0[0]!) (sum[0]!)] ++
    ((List.range (width - 1)).map fun i =>
      Gate.mkXOR (p0[i + 1]!) (final_g[i]!) (sum[i + 1]!))

  { name := "KoggeStoneAdder32NoCin"
    inputs := a ++ b
    outputs := sum
    gates := init_gates ++ all_prefix_gates ++ sum_gates
    instances := []
    signalGroups := [
      { name := "a", width := width, wires := a },
      { name := "b", width := width, wires := b },
      { name := "sum", width := width, wires := sum }
    ]
    keepHierarchy := true
  }

def koggeStoneAdder32NoCin : Circuit := mkKoggeStoneAdder32NoCin

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
  let g0 := (List.range n).map (fun i => Wire.mk s!"{pfx}g0x{i}")
  let p0 := (List.range n).map (fun i => Wire.mk s!"{pfx}p0x{i}")
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
      let g_new := (List.range n).map (fun i => Wire.mk s!"{lt}gx{i}")
      let p_new := (List.range n).map (fun i => Wire.mk s!"{lt}px{i}")

      let level_gates := List.flatten <| (List.range n).map fun i =>
        if i < stride then
          [ Gate.mkBUF (g_prev[i]!) (g_new[i]!),
            Gate.mkBUF (p_prev[i]!) (p_new[i]!) ]
        else
          let pg := Wire.mk s!"{lt}pgx{i}"
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

/-- Carry-Select Kogge-Stone adder: splits operands wider than 56 bits into two halves.
    Both halves compute with at most 6 prefix levels in parallel.
    A multiplexer selects the upper half result using the lower half carry-out. -/
def mkCarrySelectKoggeStoneAdd (a b : List Wire) (carry_in : Wire)
    (sum_out : List Wire) (pfx : String) (zero_wire one_wire : Wire) : List Gate × Wire :=
  let n := a.length
  if n <= 56 then
    mkKoggeStoneAdd a b carry_in sum_out pfx
  else
    let half := n / 2
    let a_lo := (List.range half).map fun i => a[i]!
    let b_lo := (List.range half).map fun i => b[i]!
    let sum_lo := (List.range half).map fun i => sum_out[i]!
    let a_hi := (List.range (n - half)).map fun i => a[half + i]!
    let b_hi := (List.range (n - half)).map fun i => b[half + i]!
    let sum_hi := (List.range (n - half)).map fun i => sum_out[half + i]!
    let (lo_gates, c_lo) := mkKoggeStoneAdd a_lo b_lo carry_in sum_lo (pfx ++ "_lo")
    let sum_hi0 := makeIndexedWires (pfx ++ "_s0") (n - half)
    let sum_hi1 := makeIndexedWires (pfx ++ "_s1") (n - half)
    let (hi0_gates, c_hi0) := mkKoggeStoneAdd a_hi b_hi zero_wire sum_hi0 (pfx ++ "_hi0")
    let (hi1_gates, c_hi1) := mkKoggeStoneAdd a_hi b_hi one_wire sum_hi1 (pfx ++ "_hi1")
    let mux_sum_gates := (List.range (n - half)).map fun i =>
      Gate.mkMUX (sum_hi0[i]!) (sum_hi1[i]!) c_lo (sum_hi[i]!)
    let cout := Wire.mk (pfx ++ "_cout")
    let cout_gate := Gate.mkMUX c_hi0 c_hi1 c_lo cout
    (lo_gates ++ hi0_gates ++ hi1_gates ++ mux_sum_gates ++ [cout_gate], cout)

/-- Carry-Select Kogge-Stone subtractor: out = a - b - (1 - cin).
    When cin = 1, computes a - b. When cin = 0, computes a - b - 1. -/
def mkCarrySelectKoggeStoneSub (a b : List Wire) (sum_out : List Wire)
    (pfx : String) (one_wire zero_wire : Wire) (cin : Wire) : List Gate × Wire :=
  let n := b.length
  let inv_b := makeIndexedWires (pfx ++ "_invb") n
  let inv_gates := (List.range n).map fun i => Gate.mkNOT (b[i]!) (inv_b[i]!)
  let (add_gates, carry_out) :=
    mkCarrySelectKoggeStoneAdd a inv_b cin sum_out (pfx ++ "_add") zero_wire one_wire
  let borrow_wire := Wire.mk (pfx ++ "_borrow")
  let borrow_gate := Gate.mkNOT carry_out borrow_wire
  (inv_gates ++ add_gates ++ [borrow_gate], borrow_wire)

/-- 106-bit Carry-Select Kogge-Stone adder with carry-in.
    It splits into two 53-bit Kogge-Stone blocks to eliminate the 7th prefix level.
    The lower block absorbs cin and computes sum[52:0] and carry-out bit 52.
    The upper block computes sum0 (cin=0) and sum1 (cin=1) in parallel.
    A multiplexer selects the upper sum using the lower block carry-out. -/
def mkKoggeStoneAdder106 : Circuit :=
  let width := 106
  let half := 53
  let a := makeIndexedWires "a" width
  let b := makeIndexedWires "b" width
  let cin := Wire.mk "cin"
  let sum := makeIndexedWires "sum" width

  let a_lo := (List.range half).map fun i => a[i]!
  let b_lo := (List.range half).map fun i => b[i]!
  let sum_lo := (List.range half).map fun i => sum[i]!
  let a_hi := (List.range half).map fun i => a[half + i]!
  let b_hi := (List.range half).map fun i => b[half + i]!
  let sum_hi := (List.range half).map fun i => sum[half + i]!

  let strides := [1, 2, 4, 8, 16, 32]

  let g0_lo := (List.range half).map (fun i => Wire.mk s!"ksag0_lo_x{i}")
  let p0_lo := (List.range half).map (fun i => Wire.mk s!"ksap0_lo_x{i}")
  let init_lo := List.flatten <| (List.range half).map fun i =>
    [ Gate.mkAND (a_lo[i]!) (b_lo[i]!) (g0_lo[i]!),
      Gate.mkXOR (a_lo[i]!) (b_lo[i]!) (p0_lo[i]!) ]

  let p0_cin := Wire.mk "ksa_p0_cin"
  let g0_lo_m0 := Wire.mk "ksag0_lo_m0"
  let cin_gates := [
    Gate.mkAND (p0_lo[0]!) cin p0_cin,
    Gate.mkOR (g0_lo[0]!) p0_cin g0_lo_m0
  ]
  let g0_lo_init := [g0_lo_m0] ++ (List.range (half - 1)).map fun i => g0_lo[i + 1]!

  let (pfx_lo, final_g_lo, _) :=
    strides.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
      let (gates_acc, g_prev, p_prev) := acc
      let lt := s!"lo_l{stride}"
      let g_new := (List.range half).map (fun i => Wire.mk s!"ksag_{lt}x{i}")
      let p_new := (List.range half).map (fun i => Wire.mk s!"ksap_{lt}x{i}")
      let lg := List.flatten <| (List.range half).map fun i =>
        if i < stride then
          [ Gate.mkBUF (g_prev[i]!) (g_new[i]!), Gate.mkBUF (p_prev[i]!) (p_new[i]!) ]
        else
          let pg := Wire.mk s!"ksapg_{lt}x{i}"
          [ Gate.mkAND (p_prev[i]!) (g_prev[i - stride]!) pg,
            Gate.mkOR (g_prev[i]!) pg (g_new[i]!),
            Gate.mkAND (p_prev[i]!) (p_prev[i - stride]!) (p_new[i]!) ]
      (gates_acc ++ lg, g_new, p_new)
    ) ([], g0_lo_init, p0_lo)

  let sum_lo_gates :=
    [Gate.mkXOR (p0_lo[0]!) cin (sum_lo[0]!)] ++
    ((List.range (half - 1)).map fun i =>
      Gate.mkXOR (p0_lo[i + 1]!) (final_g_lo[i]!) (sum_lo[i + 1]!))

  let c52 := final_g_lo[half - 1]!

  let g0_hi := (List.range half).map (fun i => Wire.mk s!"ksag0_hi_x{i}")
  let p0_hi := (List.range half).map (fun i => Wire.mk s!"ksap0_hi_x{i}")
  let init_hi := List.flatten <| (List.range half).map fun i =>
    [ Gate.mkAND (a_hi[i]!) (b_hi[i]!) (g0_hi[i]!),
      Gate.mkXOR (a_hi[i]!) (b_hi[i]!) (p0_hi[i]!) ]

  let sum0 := makeIndexedWires "ksas0_hi" half
  let (pfx_hi0, final_g_hi0, _) :=
    strides.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
      let (gates_acc, g_prev, p_prev) := acc
      let lt := s!"hi0_l{stride}"
      let g_new := (List.range half).map (fun i => Wire.mk s!"ksag_{lt}x{i}")
      let p_new := (List.range half).map (fun i => Wire.mk s!"ksap_{lt}x{i}")
      let lg := List.flatten <| (List.range half).map fun i =>
        if i < stride then
          [ Gate.mkBUF (g_prev[i]!) (g_new[i]!), Gate.mkBUF (p_prev[i]!) (p_new[i]!) ]
        else
          let pg := Wire.mk s!"ksapg_{lt}x{i}"
          [ Gate.mkAND (p_prev[i]!) (g_prev[i - stride]!) pg,
            Gate.mkOR (g_prev[i]!) pg (g_new[i]!),
            Gate.mkAND (p_prev[i]!) (p_prev[i - stride]!) (p_new[i]!) ]
      (gates_acc ++ lg, g_new, p_new)
    ) ([], g0_hi, p0_hi)

  let sum0_gates :=
    [Gate.mkBUF (p0_hi[0]!) (sum0[0]!)] ++
    ((List.range (half - 1)).map fun i =>
      Gate.mkXOR (p0_hi[i + 1]!) (final_g_hi0[i]!) (sum0[i + 1]!))

  let sum1 := makeIndexedWires "ksas1_hi" half
  let g0_hi_m0 := Wire.mk "ksag0_hi_m0"
  let cin1_gate := Gate.mkOR (a_hi[0]!) (b_hi[0]!) g0_hi_m0
  let g0_hi1 := [g0_hi_m0] ++ (List.range (half - 1)).map fun i => g0_hi[i + 1]!

  let (pfx_hi1, final_g_hi1, _) :=
    strides.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
      let (gates_acc, g_prev, p_prev) := acc
      let lt := s!"hi1_l{stride}"
      let g_new := (List.range half).map (fun i => Wire.mk s!"ksag_{lt}x{i}")
      let p_new := (List.range half).map (fun i => Wire.mk s!"ksap_{lt}x{i}")
      let lg := List.flatten <| (List.range half).map fun i =>
        if i < stride then
          [ Gate.mkBUF (g_prev[i]!) (g_new[i]!), Gate.mkBUF (p_prev[i]!) (p_new[i]!) ]
        else
          let pg := Wire.mk s!"ksapg_{lt}x{i}"
          [ Gate.mkAND (p_prev[i]!) (g_prev[i - stride]!) pg,
            Gate.mkOR (g_prev[i]!) pg (g_new[i]!),
            Gate.mkAND (p_prev[i]!) (p_prev[i - stride]!) (p_new[i]!) ]
      (gates_acc ++ lg, g_new, p_new)
    ) ([], g0_hi1, p0_hi)

  let sum1_gates :=
    [Gate.mkNOT (p0_hi[0]!) (sum1[0]!)] ++
    ((List.range (half - 1)).map fun i =>
      Gate.mkXOR (p0_hi[i + 1]!) (final_g_hi1[i]!) (sum1[i + 1]!))

  let sel_gates := (List.range half).map fun i =>
    Gate.mkMUX (sum0[i]!) (sum1[i]!) c52 (sum_hi[i]!)

  { name := "KoggeStoneAdder106"
    inputs := a ++ b ++ [cin]
    outputs := sum
    gates := init_lo ++ cin_gates ++ pfx_lo ++ sum_lo_gates ++
             init_hi ++ [cin1_gate] ++ pfx_hi0 ++ sum0_gates ++
             pfx_hi1 ++ sum1_gates ++ sel_gates
    instances := []
    signalGroups := [
      { name := "a", width := width, wires := a },
      { name := "b", width := width, wires := b },
      { name := "sum", width := width, wires := sum }
    ]
    keepHierarchy := true
  }

/-- Parameterized Kogge-Stone parallel prefix adder circuit. -/
def mkKoggeStoneAdder (width : Nat) : Circuit :=
  if width == 106 then mkKoggeStoneAdder106
  else
    let a := makeIndexedWires "a" width
    let b := makeIndexedWires "b" width
    let cin := Wire.mk "cin"
    let sum := makeIndexedWires "sum" width
    let (gates, _cout) := mkKoggeStoneAdd a b cin sum "ksa"
    { name := s!"KoggeStoneAdder{width}"
      inputs := a ++ b ++ [cin]
      outputs := sum
      gates := gates
      instances := []
      signalGroups := [
        { name := "a", width := width, wires := a },
        { name := "b", width := width, wires := b },
        { name := "sum", width := width, wires := sum }
      ]
      keepHierarchy := true
    }

def koggeStoneAdder106 : Circuit := mkKoggeStoneAdder 106

/-- 106-bit Carry-Select Kogge-Stone adder without carry-in (cin=0 absorbed).
    It splits into two 53-bit Kogge-Stone blocks to eliminate the 7th prefix level.
    The lower block computes sum[52:0] and carry-out bit 52.
    The upper block computes sum0 (cin=0) and sum1 (cin=1) in parallel.
    A multiplexer selects the upper sum using the lower block carry-out. -/
def mkKoggeStoneAdder106NoCin : Circuit :=
  let width := 106
  let half := 53
  let a := makeIndexedWires "a" width
  let b := makeIndexedWires "b" width
  let sum := makeIndexedWires "sum" width

  let a_lo := (List.range half).map fun i => a[i]!
  let b_lo := (List.range half).map fun i => b[i]!
  let sum_lo := (List.range half).map fun i => sum[i]!
  let a_hi := (List.range half).map fun i => a[half + i]!
  let b_hi := (List.range half).map fun i => b[half + i]!
  let sum_hi := (List.range half).map fun i => sum[half + i]!

  let strides := [1, 2, 4, 8, 16, 32]

  let g0_lo := (List.range half).map (fun i => Wire.mk s!"ksag0_lo_x{i}")
  let p0_lo := (List.range half).map (fun i => Wire.mk s!"ksap0_lo_x{i}")
  let init_lo := List.flatten <| (List.range half).map fun i =>
    [ Gate.mkAND (a_lo[i]!) (b_lo[i]!) (g0_lo[i]!),
      Gate.mkXOR (a_lo[i]!) (b_lo[i]!) (p0_lo[i]!) ]

  let (pfx_lo, final_g_lo, _) :=
    strides.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
      let (gates_acc, g_prev, p_prev) := acc
      let lt := s!"lo_l{stride}"
      let g_new := (List.range half).map (fun i => if i < stride then g_prev[i]! else Wire.mk s!"ksag_{lt}x{i}")
      let p_new := (List.range half).map (fun i => if i < stride then p_prev[i]! else Wire.mk s!"ksap_{lt}x{i}")
      let lg := List.flatten <| ((List.range half).filter (· >= stride)).map fun i =>
        let pg := Wire.mk s!"ksapg_{lt}x{i}"
        [ Gate.mkAND (p_prev[i]!) (g_prev[i - stride]!) pg,
          Gate.mkOR (g_prev[i]!) pg (g_new[i]!),
          Gate.mkAND (p_prev[i]!) (p_prev[i - stride]!) (p_new[i]!) ]
      (gates_acc ++ lg, g_new, p_new)
    ) ([], g0_lo, p0_lo)

  let sum_lo_gates :=
    [Gate.mkBUF (p0_lo[0]!) (sum_lo[0]!)] ++
    ((List.range (half - 1)).map fun i =>
      Gate.mkXOR (p0_lo[i + 1]!) (final_g_lo[i]!) (sum_lo[i + 1]!))

  let c52 := final_g_lo[half - 1]!

  let g0_hi := (List.range half).map (fun i => Wire.mk s!"ksag0_hi_x{i}")
  let p0_hi := (List.range half).map (fun i => Wire.mk s!"ksap0_hi_x{i}")
  let init_hi := List.flatten <| (List.range half).map fun i =>
    [ Gate.mkAND (a_hi[i]!) (b_hi[i]!) (g0_hi[i]!),
      Gate.mkXOR (a_hi[i]!) (b_hi[i]!) (p0_hi[i]!) ]

  let sum0 := makeIndexedWires "ksas0_hi" half
  let (pfx_hi0, final_g_hi0, _) :=
    strides.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
      let (gates_acc, g_prev, p_prev) := acc
      let lt := s!"hi0_l{stride}"
      let g_new := (List.range half).map (fun i => if i < stride then g_prev[i]! else Wire.mk s!"ksag_{lt}x{i}")
      let p_new := (List.range half).map (fun i => if i < stride then p_prev[i]! else Wire.mk s!"ksap_{lt}x{i}")
      let lg := List.flatten <| ((List.range half).filter (· >= stride)).map fun i =>
        let pg := Wire.mk s!"ksapg_{lt}x{i}"
        [ Gate.mkAND (p_prev[i]!) (g_prev[i - stride]!) pg,
          Gate.mkOR (g_prev[i]!) pg (g_new[i]!),
          Gate.mkAND (p_prev[i]!) (p_prev[i - stride]!) (p_new[i]!) ]
      (gates_acc ++ lg, g_new, p_new)
    ) ([], g0_hi, p0_hi)

  let sum0_gates :=
    [Gate.mkBUF (p0_hi[0]!) (sum0[0]!)] ++
    ((List.range (half - 1)).map fun i =>
      Gate.mkXOR (p0_hi[i + 1]!) (final_g_hi0[i]!) (sum0[i + 1]!))

  let sum1 := makeIndexedWires "ksas1_hi" half
  let g0_hi_m0 := Wire.mk "ksag0_hi_m0"
  let cin1_gate := Gate.mkOR (a_hi[0]!) (b_hi[0]!) g0_hi_m0
  let g0_hi1 := [g0_hi_m0] ++ (List.range (half - 1)).map fun i => g0_hi[i + 1]!

  let (pfx_hi1, final_g_hi1, _) :=
    strides.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
      let (gates_acc, g_prev, p_prev) := acc
      let lt := s!"hi1_l{stride}"
      let g_new := (List.range half).map (fun i => if i < stride then g_prev[i]! else Wire.mk s!"ksag_{lt}x{i}")
      let p_new := (List.range half).map (fun i => if i < stride then p_prev[i]! else Wire.mk s!"ksap_{lt}x{i}")
      let lg := List.flatten <| ((List.range half).filter (· >= stride)).map fun i =>
        let pg := Wire.mk s!"ksapg_{lt}x{i}"
        [ Gate.mkAND (p_prev[i]!) (g_prev[i - stride]!) pg,
          Gate.mkOR (g_prev[i]!) pg (g_new[i]!),
          Gate.mkAND (p_prev[i]!) (p_prev[i - stride]!) (p_new[i]!) ]
      (gates_acc ++ lg, g_new, p_new)
    ) ([], g0_hi1, p0_hi)

  let sum1_gates :=
    [Gate.mkNOT (p0_hi[0]!) (sum1[0]!)] ++
    ((List.range (half - 1)).map fun i =>
      Gate.mkXOR (p0_hi[i + 1]!) (final_g_hi1[i]!) (sum1[i + 1]!))

  let c52_bufs := (List.range 8).map (fun g => Wire.mk s!"ksac52_b{g}")
  let c52_buf_gates := (List.range 8).map (fun g =>
    Gate.mkBUF c52 (c52_bufs[g]!))

  let sel_gates := (List.range half).map fun i =>
    let grp := min (i / 7) 7
    Gate.mkMUX (sum0[i]!) (sum1[i]!) (c52_bufs[grp]!) (sum_hi[i]!)

  { name := "KoggeStoneAdder106NoCin"
    inputs := a ++ b
    outputs := sum
    gates := init_lo ++ pfx_lo ++ sum_lo_gates ++ c52_buf_gates ++
             init_hi ++ [cin1_gate] ++ pfx_hi0 ++ sum0_gates ++
             pfx_hi1 ++ sum1_gates ++ sel_gates
    instances := []
    signalGroups := [
      { name := "a", width := width, wires := a },
      { name := "b", width := width, wires := b },
      { name := "sum", width := width, wires := sum }
    ]
    keepHierarchy := true
  }

/-- Parameterized Kogge-Stone parallel prefix adder circuit without cin (cin=0 absorbed). -/
def mkKoggeStoneAdderNoCin (width : Nat) : Circuit :=
  if width == 106 then mkKoggeStoneAdder106NoCin
  else
    let a := makeIndexedWires "a" width
    let b := makeIndexedWires "b" width
    let sum := makeIndexedWires "sum" width

    let g0 := (List.range width).map (fun i => Wire.mk s!"ksag0x{i}")
    let p0 := (List.range width).map (fun i => Wire.mk s!"ksap0x{i}")
    let init_gates := List.flatten <| (List.range width).map fun i =>
      [ Gate.mkAND (a[i]!) (b[i]!) (g0[i]!),
        Gate.mkXOR (a[i]!) (b[i]!) (p0[i]!) ]

    let strides := (List.range 20).filterMap fun k =>
      let s := 1 <<< k
      if s < width then some s else none

    let (all_prefix_gates, final_g, _final_p) :=
      strides.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
        let (gates_acc, g_prev, p_prev) := acc
        let level_tag := s!"l{stride}"
        let g_new := (List.range width).map (fun i => Wire.mk s!"ksag{level_tag}x{i}")
        let p_new := (List.range width).map (fun i => Wire.mk s!"ksap{level_tag}x{i}")

        let level_gates := List.flatten <| (List.range width).map fun i =>
          if i < stride then
            [ Gate.mkBUF (g_prev[i]!) (g_new[i]!),
              Gate.mkBUF (p_prev[i]!) (p_new[i]!) ]
          else
            let pg := Wire.mk s!"ksapg{level_tag}x{i}"
            [ Gate.mkAND (p_prev[i]!) (g_prev[i - stride]!) pg,
              Gate.mkOR (g_prev[i]!) pg (g_new[i]!),
              Gate.mkAND (p_prev[i]!) (p_prev[i - stride]!) (p_new[i]!) ]

        (gates_acc ++ level_gates, g_new, p_new)
      )
      ([], g0, p0)

    let sum_gates :=
      [Gate.mkBUF (p0[0]!) (sum[0]!)] ++
      ((List.range (width - 1)).map fun i =>
        Gate.mkXOR (p0[i + 1]!) (final_g[i]!) (sum[i + 1]!))

    { name := s!"KoggeStoneAdder{width}NoCin"
      inputs := a ++ b
      outputs := sum
      gates := init_gates ++ all_prefix_gates ++ sum_gates
      instances := []
      signalGroups := [
        { name := "a", width := width, wires := a },
        { name := "b", width := width, wires := b },
        { name := "sum", width := width, wires := sum }
      ]
      keepHierarchy := true
    }

def koggeStoneAdder106NoCin : Circuit := mkKoggeStoneAdderNoCin 106

/-- 64-bit Kogge-Stone adder with cin=1 absorbed (computes a + b + 1 without cin input pin). -/
def mkKoggeStoneAdder64WithCin1 : Circuit :=
  let width := 64
  let a := makeIndexedWires "a" width
  let b := makeIndexedWires "b" width
  let sum := makeIndexedWires "sum" width

  let g0 := (List.range width).map (fun i => Wire.mk s!"ksag0x{i}")
  let p0 := (List.range width).map (fun i => Wire.mk s!"ksap0x{i}")
  let init_gates := List.flatten <| (List.range width).map fun i =>
    [ Gate.mkAND (a[i]!) (b[i]!) (g0[i]!),
      Gate.mkXOR (a[i]!) (b[i]!) (p0[i]!) ]

  -- With cin=1, bit 0 generate is g0[0] | (p0[0] & 1) = a[0] | b[0]
  let g0_m0 := Wire.mk "g0_m0"
  let cin1_gate := Gate.mkOR (a[0]!) (b[0]!) g0_m0
  let g0_init := [g0_m0] ++ (List.range (width - 1)).map fun i => g0[i + 1]!

  let strides := [1, 2, 4, 8, 16, 32]
  let (all_prefix_gates, final_g, _final_p) :=
    strides.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
      let (gates_acc, g_prev, p_prev) := acc
      let level_tag := s!"l{stride}"
      let g_new := (List.range width).map (fun i => Wire.mk s!"ksag{level_tag}x{i}")
      let p_new := (List.range width).map (fun i => Wire.mk s!"ksap{level_tag}x{i}")

      let level_gates := List.flatten <| (List.range width).map fun i =>
        if i < stride then
          [ Gate.mkBUF (g_prev[i]!) (g_new[i]!),
            Gate.mkBUF (p_prev[i]!) (p_new[i]!) ]
        else
          let pg := Wire.mk s!"ksapg{level_tag}x{i}"
          [ Gate.mkAND (p_prev[i]!) (g_prev[i - stride]!) pg,
            Gate.mkOR (g_prev[i]!) pg (g_new[i]!),
            Gate.mkAND (p_prev[i]!) (p_prev[i - stride]!) (p_new[i]!) ]

      (gates_acc ++ level_gates, g_new, p_new)
    )
    ([], g0_init, p0)

  -- sum[0] = p0[0] ^ 1 = ~p0[0]
  let sum0_gate := Gate.mkNOT (p0[0]!) (sum[0]!)
  let sum_rest := (List.range (width - 1)).map fun i =>
    Gate.mkXOR (p0[i + 1]!) (final_g[i]!) (sum[i + 1]!)

  { name := "KoggeStoneAdder64WithCin1"
    inputs := a ++ b
    outputs := sum
    gates := init_gates ++ [cin1_gate] ++ all_prefix_gates ++ [sum0_gate] ++ sum_rest
    instances := []
    signalGroups := [
      { name := "a", width := width, wires := a },
      { name := "b", width := width, wires := b },
      { name := "sum", width := width, wires := sum }
    ]
    keepHierarchy := true
  }

def koggeStoneAdder64WithCin1 : Circuit := mkKoggeStoneAdder64WithCin1

end Shoumei.Circuits.Combinational

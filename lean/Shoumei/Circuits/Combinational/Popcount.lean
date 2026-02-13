/-
Circuits/Combinational/Popcount.lean - Population Count Circuits

Popcount8: counts the number of 1-bits in an 8-bit input.
Uses a full-adder tree to produce a 4-bit result (0..8).

Tree structure:
  Level 0: 4× half-adders on pairs (in[0]+in[1], in[2]+in[3], in[4]+in[5], in[6]+in[7])
           → 4× 2-bit sums (s0, s1, s2, s3)
  Level 1: 2× 2-bit ripple-carry adders (s0+s1, s2+s3)
           → 2× 3-bit sums (t0, t1)
  Level 2: 1× 3-bit ripple-carry adder (t0+t1)
           → 1× 4-bit result
-/

import Shoumei.DSL

namespace Shoumei.Circuits.Combinational

open Shoumei

/-- 8-bit population count circuit.
    Inputs: in_0..in_7
    Outputs: count_0..count_3 (4-bit result, 0..8)
-/
def mkPopcount8 : Circuit :=
  let inputs := (List.range 8).map (fun i => Wire.mk s!"in_{i}")
  let count := (List.range 4).map (fun i => Wire.mk s!"count_{i}")

  -- Level 0: 4 half-adders (XOR for sum, AND for carry)
  -- HA0: in[0] + in[1] → (l0_s0, l0_c0)
  -- HA1: in[2] + in[3] → (l0_s1, l0_c1)
  -- HA2: in[4] + in[5] → (l0_s2, l0_c2)
  -- HA3: in[6] + in[7] → (l0_s3, l0_c3)
  let l0_s := (List.range 4).map (fun i => Wire.mk s!"l0_s_{i}")
  let l0_c := (List.range 4).map (fun i => Wire.mk s!"l0_c_{i}")
  let l0_gates := (List.range 4).map (fun i =>
    [Gate.mkXOR inputs[2*i]! inputs[2*i+1]! l0_s[i]!,
     Gate.mkAND inputs[2*i]! inputs[2*i+1]! l0_c[i]!]
  ) |>.flatten

  -- Level 1: 2× 2-bit adders
  -- Add0: (l0_c0, l0_s0) + (l0_c1, l0_s1) → 3-bit result (l1_0[2:0])
  -- Add1: (l0_c2, l0_s2) + (l0_c3, l0_s3) → 3-bit result (l1_1[2:0])
  let l1_0 := (List.range 3).map (fun i => Wire.mk s!"la0b{i}")
  let l1_1 := (List.range 3).map (fun i => Wire.mk s!"la1b{i}")

  -- 2-bit adder: a[1:0] + b[1:0] = sum[2:0]
  -- Bit 0: XOR(a0, b0), carry0 = AND(a0, b0)
  -- Bit 1: XOR(XOR(a1,b1), carry0), carry1 = MAJ(a1,b1,carry0)
  -- Bit 2: carry1
  let l1_c0_0 := Wire.mk "l1_c0_0"
  let l1_xor0_1 := Wire.mk "l1_xor0_1"
  let _l1_c0_1 := Wire.mk "l1_c0_1"
  let l1_t0_0 := Wire.mk "l1_t0_0"
  let l1_t0_1 := Wire.mk "l1_t0_1"
  let l1_add0_gates := [
    Gate.mkXOR l0_s[0]! l0_s[1]! l1_0[0]!,
    Gate.mkAND l0_s[0]! l0_s[1]! l1_c0_0,
    Gate.mkXOR l0_c[0]! l0_c[1]! l1_xor0_1,
    Gate.mkXOR l1_xor0_1 l1_c0_0 l1_0[1]!,
    -- carry1 = (a1 AND b1) OR (a1 AND c0) OR (b1 AND c0)
    Gate.mkAND l0_c[0]! l0_c[1]! l1_t0_0,
    Gate.mkAND l1_xor0_1 l1_c0_0 l1_t0_1,
    Gate.mkOR l1_t0_0 l1_t0_1 l1_0[2]!
  ]

  let l1_c1_0 := Wire.mk "l1_c1_0"
  let l1_xor1_1 := Wire.mk "l1_xor1_1"
  let _l1_c1_1 := Wire.mk "l1_c1_1"
  let l1_t1_0 := Wire.mk "l1_t1_0"
  let l1_t1_1 := Wire.mk "l1_t1_1"
  let l1_add1_gates := [
    Gate.mkXOR l0_s[2]! l0_s[3]! l1_1[0]!,
    Gate.mkAND l0_s[2]! l0_s[3]! l1_c1_0,
    Gate.mkXOR l0_c[2]! l0_c[3]! l1_xor1_1,
    Gate.mkXOR l1_xor1_1 l1_c1_0 l1_1[1]!,
    Gate.mkAND l0_c[2]! l0_c[3]! l1_t1_0,
    Gate.mkAND l1_xor1_1 l1_c1_0 l1_t1_1,
    Gate.mkOR l1_t1_0 l1_t1_1 l1_1[2]!
  ]

  -- Level 2: 3-bit adder: l1_0[2:0] + l1_1[2:0] → count[3:0]
  let l2_c0 := Wire.mk "l2_c0"
  let l2_xor1 := Wire.mk "l2_xor1"
  let l2_c1 := Wire.mk "l2_c1"
  let l2_t1_0 := Wire.mk "l2_t1_0"
  let l2_t1_1 := Wire.mk "l2_t1_1"
  let l2_xor2 := Wire.mk "l2_xor2"
  let _l2_c2 := Wire.mk "l2_c2"
  let l2_t2_0 := Wire.mk "l2_t2_0"
  let l2_t2_1 := Wire.mk "l2_t2_1"
  let l2_gates := [
    -- Bit 0
    Gate.mkXOR l1_0[0]! l1_1[0]! count[0]!,
    Gate.mkAND l1_0[0]! l1_1[0]! l2_c0,
    -- Bit 1
    Gate.mkXOR l1_0[1]! l1_1[1]! l2_xor1,
    Gate.mkXOR l2_xor1 l2_c0 count[1]!,
    Gate.mkAND l1_0[1]! l1_1[1]! l2_t1_0,
    Gate.mkAND l2_xor1 l2_c0 l2_t1_1,
    Gate.mkOR l2_t1_0 l2_t1_1 l2_c1,
    -- Bit 2
    Gate.mkXOR l1_0[2]! l1_1[2]! l2_xor2,
    Gate.mkXOR l2_xor2 l2_c1 count[2]!,
    Gate.mkAND l1_0[2]! l1_1[2]! l2_t2_0,
    Gate.mkAND l2_xor2 l2_c1 l2_t2_1,
    Gate.mkOR l2_t2_0 l2_t2_1 count[3]!
  ]

  { name := "Popcount8"
    inputs := inputs
    outputs := count
    gates := l0_gates ++ l1_add0_gates ++ l1_add1_gates ++ l2_gates
    instances := []
    signalGroups := [
      { name := "in", width := 8, wires := inputs },
      { name := "count", width := 4, wires := count }
    ]
  }

end Shoumei.Circuits.Combinational

/-
Circuits/Sequential/FPAdder.lean - 4-Stage Pipelined Single-Precision FP Adder/Subtractor

A pipelined floating-point adder/subtractor for IEEE 754 binary32.

Decomposed hierarchically into 4 combinational pipeline stage modules:
  Stage 1 (FPAdder_Stage1_Unpack): Unpack + Exponent difference + Swap detection + NaN/Inf detection
  Stage 2 (FPAdder_Stage2_Align): Swap operands + Alignment barrel shift with sticky tracking
  Stage 3 (FPAdder_Stage3_AddSub): Mantissa add (KSA) + Leading-zero parallel prefix detect
  Stage 4 (FPAdder_Stage4_NormRound): Normalize + Special values + Pack + Exceptions

Interface:
- Inputs: src1[31:0], src2[31:0], op_sub, rm[2:0], dest_tag[5:0], valid_in,
          clock, reset, zero
- Outputs: result[31:0], tag_out[5:0], exc[4:0], valid_out
-/

import Shoumei.DSL
import Shoumei.Components.Select
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Components
open Shoumei.Circuits.Combinational

/-! ## Helper: Indexed Wire Generation -/

private def makeIndexedWires (pfx : String) (n : Nat) : List Wire :=
  (List.range n).map fun i => Wire.mk (pfx ++ "_" ++ toString i)

/-! ## Helper: DFF Bank -/

private def mkDFFBank (d_wires q_wires : List Wire) (clock reset : Wire) : List Gate :=
  List.zipWith (fun d q => Gate.mkDFF d clock reset q) d_wires q_wires

private def mkBUFBank (src dst : List Wire) : List Gate :=
  List.zipWith (fun s d => Gate.mkBUF s d) src dst

/-! ## Arithmetic Helpers -/

/-- 5-level barrel right shifter for w-bit value. -/
private def mkBarrelShiftRight (input : List Wire) (shift_amt : List Wire)
    (output : List Wire) (zero_wire : Wire) (pfx : String) : List Gate :=
  let w := input.length
  let levels : List (List Wire) := (List.range 6).map fun level =>
    if level == 0 then input
    else (List.range w).map fun i => Wire.mk (pfx ++ "_l" ++ toString level ++ "_" ++ toString i)
  let mux_gates := (List.range 5).flatMap fun level =>
    let shift_by := 1 <<< level
    let prev := levels[level]!
    let curr := levels[level + 1]!
    let sel := shift_amt[level]!
    (List.range w).map fun i =>
      let unshifted := prev[i]!
      let shifted := if i + shift_by < w then prev[i + shift_by]! else zero_wire
      Gate.mkMUX unshifted shifted sel curr[i]!
  let copy_gates := (List.range w).map fun i =>
    Gate.mkBUF (levels[5]!)[i]! output[i]!
  mux_gates ++ copy_gates

/-- 5-level barrel left shifter for w-bit value. -/
private def mkBarrelShiftLeft (input : List Wire) (shift_amt : List Wire)
    (output : List Wire) (zero_wire : Wire) (pfx : String) : List Gate :=
  let w := input.length
  let levels : List (List Wire) := (List.range 6).map fun level =>
    if level == 0 then input
    else (List.range w).map fun i => Wire.mk (pfx ++ "_l" ++ toString level ++ "_" ++ toString i)
  let mux_gates := (List.range 5).flatMap fun level =>
    let shift_by := 1 <<< level
    let prev := levels[level]!
    let curr := levels[level + 1]!
    let sel := shift_amt[level]!
    (List.range w).map fun i =>
      let unshifted := prev[i]!
      let shifted := if i >= shift_by then prev[i - shift_by]! else zero_wire
      Gate.mkMUX unshifted shifted sel curr[i]!
  let copy_gates := (List.range w).map fun i =>
    Gate.mkBUF (levels[5]!)[i]! output[i]!
  mux_gates ++ copy_gates

/-- OR-reduce a wire list: returns the result wire and its gates. -/
private def mkOrReduce (pfx : String) (wires : List Wire) (zero_wire : Wire) : Wire × List Gate :=
  match wires with
  | [] => (zero_wire, [])
  | w0 :: rest =>
    let (last, gates) := rest.foldl (fun (acc, gs) w =>
      let o := Wire.mk s!"{pfx}_{gs.length}"
      (o, gs ++ [Gate.mkOR acc w o])) (w0, [])
    (last, gates)

/-- Barrel right shifter that also accumulates a sticky bit: every bit shifted
    below position 0 at any level is OR-ed into `sticky_out`.  That bit is the
    rounding remainder the alignment would otherwise lose, and carrying it is what
    makes correct rounding possible downstream.

    Widths come from the arguments, so the 27-bit single-precision datapath uses
    this and the 56-bit double-precision one has a specialised twin (its shift
    amount is wider than the levels this shape can express). -/
private def mkBarrelShiftRightSticky (input : List Wire) (shift_amt : List Wire)
    (output : List Wire) (sticky_out : Wire) (zero_wire : Wire) (pfx : String) : List Gate :=
  let w := input.length
  let n := shift_amt.length
  let levels : List (List Wire) := (List.range (n + 1)).map fun level =>
    if level == 0 then input
    else (List.range w).map fun i => Wire.mk (pfx ++ "_l" ++ toString level ++ "_" ++ toString i)
  let stickies : List Wire := (List.range (n + 1)).map fun level =>
    Wire.mk (pfx ++ "_stk_" ++ toString level)
  let init_stk_gate := Gate.mkBUF zero_wire stickies[0]!
  let (mux_gates, stk_gates) := (List.range n).foldl (fun (acc : List Gate × List Gate) level =>
    let shift_by := 1 <<< level
    let prev := levels[level]!
    let curr := levels[level + 1]!
    let sel := shift_amt[level]!
    let prev_stk := stickies[level]!
    let curr_stk := stickies[level + 1]!
    let m_gates := (List.range w).map fun i =>
      let unshifted := prev[i]!
      let shifted := if i + shift_by < w then prev[i + shift_by]! else zero_wire
      Gate.mkMUX unshifted shifted sel curr[i]!
    let lost_bits := (List.range (min shift_by w)).map fun i => prev[i]!
    let (lost_or, lost_or_gates) := mkOrReduce (pfx ++ "_lost_l" ++ toString level) lost_bits zero_wire
    let stk_c := Wire.mk (pfx ++ "_stk_c_" ++ toString level)
    let s_gates := lost_or_gates ++ [
      Gate.mkAND sel lost_or stk_c,
      Gate.mkOR prev_stk stk_c curr_stk
    ]
    (acc.1 ++ m_gates, acc.2 ++ s_gates)
  ) ([], [init_stk_gate])
  let copy_gates := (List.range w).map fun i =>
    Gate.mkBUF (levels[n]!)[i]! output[i]!
  let final_stk_gate := Gate.mkBUF stickies[n]! sticky_out
  mux_gates ++ stk_gates ++ copy_gates ++ [final_stk_gate]

/-! ## Pipeline Stage 1: Unpack + Exponent difference + Swap + NaN/Inf -/

def mkFPAdder_Stage1_Unpack : Circuit :=
  let src1 := makeIndexedWires "src1" 32
  let src2 := makeIndexedWires "src2" 32
  let op_sub := Wire.mk "op_sub"
  let zero := Wire.mk "zero"

  let sign_a := Wire.mk "sign_a"
  let eff_sign_b := Wire.mk "eff_sign_b"
  let exp_a := makeIndexedWires "exp_a" 8
  let exp_b := makeIndexedWires "exp_b" 8
  let mant_a := makeIndexedWires "mant_a" 24
  let mant_b := makeIndexedWires "mant_b" 24
  let exp_diff := makeIndexedWires "exp_diff" 9
  let swap := Wire.mk "swap"
  let any_nan := Wire.mk "any_nan"
  let any_special := Wire.mk "any_special"
  let both_inf := Wire.mk "both_inf"
  let a_is_inf := Wire.mk "a_is_inf"
  let b_is_inf := Wire.mk "b_is_inf"

  let one := Wire.mk "s1_one"
  let one_gate := Gate.mkNOT zero one

  -- Unpack operand A
  let not_sign_a := Wire.mk "s1_not_sign_a"
  let sign_a_gate := [Gate.mkNOT (src1[31]!) not_sign_a, Gate.mkNOT not_sign_a sign_a]
  -- The unpacked exponent field.  exp_a (below) is the *effective* exponent the
  -- datapath works with; this is the raw field, which only the implicit-bit and
  -- all-ones tests read.
  let raw_exp_a := makeIndexedWires "s1_raw_exp_a" 8
  let not_exp_a := makeIndexedWires "s1_not_exp_a" 8
  let exp_a_gates := (List.range 8).flatMap fun i =>
    [Gate.mkNOT (src1[23 + i]!) (not_exp_a[i]!),
     Gate.mkNOT (not_exp_a[i]!) (raw_exp_a[i]!)]

  let exp_a_or01 := Wire.mk "s1_exp_a_or01"
  let exp_a_or23 := Wire.mk "s1_exp_a_or23"
  let exp_a_or45 := Wire.mk "s1_exp_a_or45"
  let exp_a_or67 := Wire.mk "s1_exp_a_or67"
  let exp_a_or0123 := Wire.mk "s1_exp_a_or0123"
  let exp_a_or4567 := Wire.mk "s1_exp_a_or4567"
  let exp_a_or_all := Wire.mk "s1_exp_a_or_all"
  let exp_a_zero_gates := [
    Gate.mkOR (raw_exp_a[0]!) (raw_exp_a[1]!) exp_a_or01,
    Gate.mkOR (raw_exp_a[2]!) (raw_exp_a[3]!) exp_a_or23,
    Gate.mkOR (raw_exp_a[4]!) (raw_exp_a[5]!) exp_a_or45,
    Gate.mkOR (raw_exp_a[6]!) (raw_exp_a[7]!) exp_a_or67,
    Gate.mkOR exp_a_or01 exp_a_or23 exp_a_or0123,
    Gate.mkOR exp_a_or45 exp_a_or67 exp_a_or4567,
    Gate.mkOR exp_a_or0123 exp_a_or4567 exp_a_or_all
  ]

  let not_mant_a := makeIndexedWires "s1_not_mant_a" 23
  let mant_a_gates := (List.range 23).flatMap (fun i =>
    [Gate.mkNOT (src1[i]!) (not_mant_a[i]!),
     Gate.mkNOT (not_mant_a[i]!) (mant_a[i]!)]) ++
    [Gate.mkBUF exp_a_or_all (mant_a[23]!)]

  -- Unpack operand B
  let sign_b_raw := Wire.mk "s1_sign_b_raw"
  let sign_b_raw_gate := Gate.mkBUF (src2[31]!) sign_b_raw
  let eff_sign_b_gate := Gate.mkXOR sign_b_raw op_sub eff_sign_b

  let raw_exp_b := makeIndexedWires "s1_raw_exp_b" 8
  let not_exp_b := makeIndexedWires "s1_not_exp_b" 8
  let exp_b_gates := (List.range 8).flatMap fun i =>
    [Gate.mkNOT (src2[23 + i]!) (not_exp_b[i]!),
     Gate.mkNOT (not_exp_b[i]!) (raw_exp_b[i]!)]

  let exp_b_or01 := Wire.mk "s1_exp_b_or01"
  let exp_b_or23 := Wire.mk "s1_exp_b_or23"
  let exp_b_or45 := Wire.mk "s1_exp_b_or45"
  let exp_b_or67 := Wire.mk "s1_exp_b_or67"
  let exp_b_or0123 := Wire.mk "s1_exp_b_or0123"
  let exp_b_or4567 := Wire.mk "s1_exp_b_or4567"
  let exp_b_or_all := Wire.mk "s1_exp_b_or_all"
  let exp_b_zero_gates := [
    Gate.mkOR (raw_exp_b[0]!) (raw_exp_b[1]!) exp_b_or01,
    Gate.mkOR (raw_exp_b[2]!) (raw_exp_b[3]!) exp_b_or23,
    Gate.mkOR (raw_exp_b[4]!) (raw_exp_b[5]!) exp_b_or45,
    Gate.mkOR (raw_exp_b[6]!) (raw_exp_b[7]!) exp_b_or67,
    Gate.mkOR exp_b_or01 exp_b_or23 exp_b_or0123,
    Gate.mkOR exp_b_or45 exp_b_or67 exp_b_or4567,
    Gate.mkOR exp_b_or0123 exp_b_or4567 exp_b_or_all
  ]

  let not_mant_b := makeIndexedWires "s1_not_mant_b" 23
  let mant_b_gates := (List.range 23).flatMap (fun i =>
    [Gate.mkNOT (src2[i]!) (not_mant_b[i]!),
     Gate.mkNOT (not_mant_b[i]!) (mant_b[i]!)]) ++
    [Gate.mkBUF exp_b_or_all (mant_b[23]!)]

  -- NaN / Inf detection for A
  let a_exp_and01 := Wire.mk "s1_a_and01"
  let a_exp_and23 := Wire.mk "s1_a_and23"
  let a_exp_and45 := Wire.mk "s1_a_and45"
  let a_exp_and67 := Wire.mk "s1_a_and67"
  let a_exp_and0123 := Wire.mk "s1_a_and0123"
  let a_exp_and4567 := Wire.mk "s1_a_and4567"
  let a_exp_all_ones := Wire.mk "s1_a_exp_all_ones"
  let exp_a_and_gates := [
    Gate.mkAND (raw_exp_a[0]!) (raw_exp_a[1]!) a_exp_and01,
    Gate.mkAND (raw_exp_a[2]!) (raw_exp_a[3]!) a_exp_and23,
    Gate.mkAND (raw_exp_a[4]!) (raw_exp_a[5]!) a_exp_and45,
    Gate.mkAND (raw_exp_a[6]!) (raw_exp_a[7]!) a_exp_and67,
    Gate.mkAND a_exp_and01 a_exp_and23 a_exp_and0123,
    Gate.mkAND a_exp_and45 a_exp_and67 a_exp_and4567,
    Gate.mkAND a_exp_and0123 a_exp_and4567 a_exp_all_ones
  ]

  -- NaN / Inf detection for B
  let b_exp_and01 := Wire.mk "s1_b_and01"
  let b_exp_and23 := Wire.mk "s1_b_and23"
  let b_exp_and45 := Wire.mk "s1_b_and45"
  let b_exp_and67 := Wire.mk "s1_b_and67"
  let b_exp_and0123 := Wire.mk "s1_b_and0123"
  let b_exp_and4567 := Wire.mk "s1_b_and4567"
  let b_exp_all_ones := Wire.mk "s1_b_exp_all_ones"
  let exp_b_and_gates := [
    Gate.mkAND (raw_exp_b[0]!) (raw_exp_b[1]!) b_exp_and01,
    Gate.mkAND (raw_exp_b[2]!) (raw_exp_b[3]!) b_exp_and23,
    Gate.mkAND (raw_exp_b[4]!) (raw_exp_b[5]!) b_exp_and45,
    Gate.mkAND (raw_exp_b[6]!) (raw_exp_b[7]!) b_exp_and67,
    Gate.mkAND b_exp_and01 b_exp_and23 b_exp_and0123,
    Gate.mkAND b_exp_and45 b_exp_and67 b_exp_and4567,
    Gate.mkAND b_exp_and0123 b_exp_and4567 b_exp_all_ones
  ]

  -- Mantissa nonzero OR tree for A
  let a_mant_nonzero := Wire.mk "s1_a_mant_nonzero"
  let mant_a_or_gates :=
    let l1 := (List.range 11).map fun i =>
      let w := Wire.mk s!"s1_a_mor_l1_{i}"
      Gate.mkOR (src1[2*i]!) (src1[2*i+1]!) w
    let l1_wires := (List.range 11).map fun i => Wire.mk s!"s1_a_mor_l1_{i}"
    let l1_plus := l1_wires ++ [src1[22]!]
    let l2 := (List.range 6).map fun i =>
      let w := Wire.mk s!"s1_a_mor_l2_{i}"
      Gate.mkOR (l1_plus[2*i]!) (l1_plus[2*i+1]!) w
    let l2_wires := (List.range 6).map fun i => Wire.mk s!"s1_a_mor_l2_{i}"
    let l3 := (List.range 3).map fun i =>
      let w := Wire.mk s!"s1_a_mor_l3_{i}"
      Gate.mkOR (l2_wires[2*i]!) (l2_wires[2*i+1]!) w
    let l3_wires := (List.range 3).map fun i => Wire.mk s!"s1_a_mor_l3_{i}"
    let or_01 := Wire.mk "s1_a_mor_01"
    let l4_gates := [
      Gate.mkOR (l3_wires[0]!) (l3_wires[1]!) or_01,
      Gate.mkOR or_01 (l3_wires[2]!) a_mant_nonzero
    ]
    l1 ++ l2 ++ l3 ++ l4_gates

  let a_is_nan := Wire.mk "s1_a_is_nan"
  let not_a_mant_nonzero := Wire.mk "s1_not_a_mant_nz"
  let a_nan_inf_gates := [
    Gate.mkAND a_exp_all_ones a_mant_nonzero a_is_nan,
    Gate.mkNOT a_mant_nonzero not_a_mant_nonzero,
    Gate.mkAND a_exp_all_ones not_a_mant_nonzero a_is_inf
  ]

  -- Mantissa nonzero OR tree for B
  let b_mant_nonzero := Wire.mk "s1_b_mant_nonzero"
  let mant_b_or_gates :=
    let l1 := (List.range 11).map fun i =>
      let w := Wire.mk s!"s1_b_mor_l1_{i}"
      Gate.mkOR (src2[2*i]!) (src2[2*i+1]!) w
    let l1_wires := (List.range 11).map fun i => Wire.mk s!"s1_b_mor_l1_{i}"
    let l1_plus := l1_wires ++ [src2[22]!]
    let l2 := (List.range 6).map fun i =>
      let w := Wire.mk s!"s1_b_mor_l2_{i}"
      Gate.mkOR (l1_plus[2*i]!) (l1_plus[2*i+1]!) w
    let l2_wires := (List.range 6).map fun i => Wire.mk s!"s1_b_mor_l2_{i}"
    let l3 := (List.range 3).map fun i =>
      let w := Wire.mk s!"s1_b_mor_l3_{i}"
      Gate.mkOR (l2_wires[2*i]!) (l2_wires[2*i+1]!) w
    let l3_wires := (List.range 3).map fun i => Wire.mk s!"s1_b_mor_l3_{i}"
    let or_01 := Wire.mk "s1_b_mor_01"
    let l4_gates := [
      Gate.mkOR (l3_wires[0]!) (l3_wires[1]!) or_01,
      Gate.mkOR or_01 (l3_wires[2]!) b_mant_nonzero
    ]
    l1 ++ l2 ++ l3 ++ l4_gates

  let b_is_nan := Wire.mk "s1_b_is_nan"
  let not_b_mant_nonzero := Wire.mk "s1_not_b_mant_nz"
  let b_nan_inf_gates := [
    Gate.mkAND b_exp_all_ones b_mant_nonzero b_is_nan,
    Gate.mkNOT b_mant_nonzero not_b_mant_nonzero,
    Gate.mkAND b_exp_all_ones not_b_mant_nonzero b_is_inf
  ]

  -- NV comes from a signalling NaN operand (quiet bit clear) or from inf + -inf.
  -- Raising it for every NaN was wrong: a quiet NaN propagates without a flag.
  let a_is_snan := Wire.mk "s1_a_is_snan"
  let b_is_snan := Wire.mk "s1_b_is_snan"
  let not_a_quiet := Wire.mk "s1_not_a_quiet"
  let not_b_quiet := Wire.mk "s1_not_b_quiet"
  let any_snan := Wire.mk "any_snan"
  let snan_gates := [
    Gate.mkNOT (src1[22]!) not_a_quiet,
    Gate.mkAND a_is_nan not_a_quiet a_is_snan,
    Gate.mkNOT (src2[22]!) not_b_quiet,
    Gate.mkAND b_is_nan not_b_quiet b_is_snan,
    Gate.mkOR a_is_snan b_is_snan any_snan
  ]
  let any_nan_gate := Gate.mkOR a_is_nan b_is_nan any_nan
  let any_special_gate := Gate.mkOR a_exp_all_ones b_exp_all_ones any_special
  let both_inf_gate := Gate.mkAND a_is_inf b_is_inf both_inf

  -- Effective exponent: a nonzero subnormal operand is scaled as a normal number
  -- whose exponent field is 1, so it must align and be added at that weight.  The
  -- raw field 0 would place it one binade low.  A zero operand keeps field 0;
  -- its mantissa is zero, so the weight only has to keep the swap and the result
  -- exponent sensible.
  let a_eff_sub := Wire.mk "s1_a_eff_sub"
  let b_eff_sub := Wire.mk "s1_b_eff_sub"
  let not_exp_a_or_all := Wire.mk "s1_not_exp_a_or_all"
  let not_exp_b_or_all := Wire.mk "s1_not_exp_b_or_all"
  let eff_sub_gates := [
    Gate.mkNOT exp_a_or_all not_exp_a_or_all,
    Gate.mkAND not_exp_a_or_all a_mant_nonzero a_eff_sub,
    Gate.mkNOT exp_b_or_all not_exp_b_or_all,
    Gate.mkAND not_exp_b_or_all b_mant_nonzero b_eff_sub
  ]
  let eff_exp_a_gates := (List.range 8).map fun i =>
    Gate.mkMUX (raw_exp_a[i]!) (if i == 0 then one else zero) a_eff_sub (exp_a[i]!)
  let eff_exp_b_gates := (List.range 8).map fun i =>
    Gate.mkMUX (raw_exp_b[i]!) (if i == 0 then one else zero) b_eff_sub (exp_b[i]!)

  -- Exponent difference (9-bit): exp_a - exp_b
  let exp_a_ext := makeIndexedWires "s1_exp_a_ext" 9
  let exp_a_ext_gates := (List.range 8).map (fun i =>
    Gate.mkBUF (exp_a[i]!) (exp_a_ext[i]!)) ++
    [Gate.mkBUF zero (exp_a_ext[8]!)]

  let exp_b_ext := makeIndexedWires "s1_exp_b_ext" 9
  let exp_b_ext_gates := (List.range 8).map (fun i =>
    Gate.mkBUF (exp_b[i]!) (exp_b_ext[i]!)) ++
    [Gate.mkBUF zero (exp_b_ext[8]!)]

  let (exp_diff_gates, _exp_diff_borrow) :=
    mkKoggeStoneSub exp_a_ext exp_b_ext exp_diff "s1_expdiff" one

  let swap_gate := Gate.mkBUF _exp_diff_borrow swap

  let all_gates :=
    [one_gate] ++ sign_a_gate ++ exp_a_gates ++ exp_a_zero_gates ++ mant_a_gates ++
    [sign_b_raw_gate, eff_sign_b_gate] ++ exp_b_gates ++ exp_b_zero_gates ++ mant_b_gates ++
    exp_a_and_gates ++ exp_b_and_gates ++ mant_a_or_gates ++ a_nan_inf_gates ++
    mant_b_or_gates ++ b_nan_inf_gates ++
    snan_gates ++ [any_nan_gate, any_special_gate, both_inf_gate] ++
    eff_sub_gates ++ eff_exp_a_gates ++ eff_exp_b_gates ++
    exp_a_ext_gates ++ exp_b_ext_gates ++ exp_diff_gates ++ [swap_gate]

  { name := "FPAdder_Stage1_Unpack"
    inputs := src1 ++ src2 ++ [op_sub, zero]
    outputs := [sign_a, eff_sign_b] ++ exp_a ++ exp_b ++ mant_a ++ mant_b ++ exp_diff ++
               [swap, any_nan, any_snan, any_special, both_inf, a_is_inf, b_is_inf]
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "src1", width := 32, wires := src1 },
      { name := "src2", width := 32, wires := src2 },
      { name := "exp_a", width := 8, wires := exp_a },
      { name := "exp_b", width := 8, wires := exp_b },
      { name := "mant_a", width := 24, wires := mant_a },
      { name := "mant_b", width := 24, wires := mant_b },
      { name := "exp_diff", width := 9, wires := exp_diff }
    ] }

def fpAdder_Stage1Circuit : Circuit := mkFPAdder_Stage1_Unpack

/-! ## Pipeline Stage 2: Swap + Align + Sticky -/

def mkFPAdder_Stage2_Align : Circuit :=
  let sign_a := Wire.mk "sign_a"
  let eff_sign_b := Wire.mk "eff_sign_b"
  let exp_a := makeIndexedWires "exp_a" 8
  let exp_b := makeIndexedWires "exp_b" 8
  let mant_a := makeIndexedWires "mant_a" 24
  let mant_b := makeIndexedWires "mant_b" 24
  let exp_diff := makeIndexedWires "exp_diff" 9
  let swap := Wire.mk "swap"
  let both_inf := Wire.mk "both_inf"
  let a_is_inf := Wire.mk "a_is_inf"
  let zero := Wire.mk "zero"

  let big_sign := Wire.mk "big_sign"
  let big_exp := makeIndexedWires "big_exp" 8
  let big_mant := makeIndexedWires "big_mant" 24
  -- Three extra low bits below the mantissa carry the guard, round and sticky
  -- positions through the adder.  Without them the alignment remainder collapses
  -- to a single sticky bit and the sum cannot be rounded, so the mantissa sits at
  -- [26:3] of this datapath and is shifted by the exponent difference as before.
  let aligned := makeIndexedWires "aligned" 27
  let eff_sub := Wire.mk "eff_sub"
  let sticky := Wire.mk "sticky"
  let inf_sub_inf := Wire.mk "inf_sub_inf"
  let inf_result_sign := Wire.mk "inf_result_sign"

  let one := Wire.mk "s2_one"
  let one_gate := Gate.mkNOT zero one

  let big_sign_gate := Gate.mkMUX sign_a eff_sign_b swap big_sign

  let big_exp_gates := (List.range 8).map fun i =>
    Gate.mkMUX (exp_a[i]!) (exp_b[i]!) swap (big_exp[i]!)

  let big_mant_gates := (List.range 24).map fun i =>
    Gate.mkMUX (mant_a[i]!) (mant_b[i]!) swap (big_mant[i]!)

  let small_mant := makeIndexedWires "s2_small_mant" 24
  let small_mant_gates := (List.range 24).map fun i =>
    Gate.mkMUX (mant_b[i]!) (mant_a[i]!) swap (small_mant[i]!)

  let small_sign := Wire.mk "s2_small_sign"
  let small_sign_gate := Gate.mkMUX eff_sign_b sign_a swap small_sign

  let neg_diff := makeIndexedWires "s2_neg_diff" 8
  let inv_diff := makeIndexedWires "s2_inv_diff" 8
  let inv_diff_gates := (List.range 8).map fun i =>
    Gate.mkNOT (exp_diff[i]!) (inv_diff[i]!)

  let zeros8 := (List.range 8).map fun _ => zero
  let (neg_diff_add_gates, _neg_carry) :=
    mkKoggeStoneAdd inv_diff zeros8 one neg_diff "s2_negdiff"

  let exp_diff8_not := Wire.mk "s2_exp_diff8_not"
  let exp_diff8_zero := Wire.mk "s2_exp_diff8_zero"
  let exp_diff8_gates := [
    Gate.mkNOT (exp_diff[8]!) exp_diff8_not,
    Gate.mkAND (exp_diff[8]!) exp_diff8_not exp_diff8_zero
  ]

  let abs_diff := makeIndexedWires "s2_abs_diff" 8
  let abs_diff_pre0 := Wire.mk "s2_abs_diff_pre0"
  let abs_diff_gates :=
    [Gate.mkMUX (exp_diff[0]!) (neg_diff[0]!) swap abs_diff_pre0,
     Gate.mkOR abs_diff_pre0 exp_diff8_zero (abs_diff[0]!)] ++
    (List.range 7).map fun i =>
      Gate.mkMUX (exp_diff[i + 1]!) (neg_diff[i + 1]!) swap (abs_diff[i + 1]!)

  let clamp_or56 := Wire.mk "s2_clamp_or56"
  let clamp_or567 := Wire.mk "s2_clamp_or567"
  let clamp_gates := [
    Gate.mkOR (abs_diff[5]!) (abs_diff[6]!) clamp_or56,
    Gate.mkOR clamp_or56 (abs_diff[7]!) clamp_or567
  ]

  let shift_amt := (List.range 5).map fun i => abs_diff[i]!
  let aligned_pre := makeIndexedWires "s2_aligned_pre" 27
  let small_mant27 := (List.range 3).map (fun _ => zero) ++ small_mant
  let shift_sticky := Wire.mk "s2_shift_sticky"
  let barrel_gates :=
    mkBarrelShiftRightSticky small_mant27 shift_amt aligned_pre shift_sticky zero "s2_bsr"

  let not_clamp := Wire.mk "s2_not_clamp"
  let not_clamp_gate := Gate.mkNOT clamp_or567 not_clamp
  let clamp_and_gates := (List.range 27).map fun i =>
    Gate.mkAND (aligned_pre[i]!) not_clamp (aligned[i]!)

  let small_mant_any := Wire.mk "s2_sm_any"
  let sm_or_gates :=
    let l1 := (List.range 12).map fun i =>
      let w := Wire.mk s!"s2_sm_or_l1_{i}"
      Gate.mkOR (small_mant[2*i]!) (small_mant[2*i+1]!) w
    let l1w := (List.range 12).map fun i => Wire.mk s!"s2_sm_or_l1_{i}"
    let l2 := (List.range 6).map fun i =>
      let w := Wire.mk s!"s2_sm_or_l2_{i}"
      Gate.mkOR (l1w[2*i]!) (l1w[2*i+1]!) w
    let l2w := (List.range 6).map fun i => Wire.mk s!"s2_sm_or_l2_{i}"
    let l3 := (List.range 3).map fun i =>
      let w := Wire.mk s!"s2_sm_or_l3_{i}"
      Gate.mkOR (l2w[2*i]!) (l2w[2*i+1]!) w
    let l3w := (List.range 3).map fun i => Wire.mk s!"s2_sm_or_l3_{i}"
    let l4a := Wire.mk "s2_sm_or_l4a"
    l1 ++ l2 ++ l3 ++ [
      Gate.mkOR (l3w[0]!) (l3w[1]!) l4a,
      Gate.mkOR l4a (l3w[2]!) small_mant_any
    ]

  -- Sticky: everything the alignment shifted out, taken from the barrel's own
  -- accumulation.  At an exponent difference of 32 or more the 5-bit shift amount
  -- cannot express the shift, the mantissa is zeroed instead, and every bit of it
  -- is sticky.
  let sticky_gate := Gate.mkMUX shift_sticky small_mant_any clamp_or567 sticky

  let eff_sub_gate := Gate.mkXOR big_sign small_sign eff_sub
  let inf_sub_inf_gate := Gate.mkAND both_inf eff_sub inf_sub_inf
  let inf_result_sign_gate := Gate.mkMUX eff_sign_b sign_a a_is_inf inf_result_sign

  let all_gates :=
    [one_gate, big_sign_gate] ++ big_exp_gates ++ big_mant_gates ++ small_mant_gates ++ [small_sign_gate] ++
    inv_diff_gates ++ neg_diff_add_gates ++ exp_diff8_gates ++ abs_diff_gates ++ clamp_gates ++
    barrel_gates ++ [not_clamp_gate] ++ clamp_and_gates ++
    sm_or_gates ++ [sticky_gate] ++
    [eff_sub_gate, inf_sub_inf_gate, inf_result_sign_gate]

  { name := "FPAdder_Stage2_Align"
    inputs := [sign_a, eff_sign_b] ++ exp_a ++ exp_b ++ mant_a ++ mant_b ++ exp_diff ++
              [swap, both_inf, a_is_inf, zero]
    outputs := [big_sign] ++ big_exp ++ big_mant ++ aligned ++
               [eff_sub, sticky, inf_sub_inf, inf_result_sign]
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "exp_a", width := 8, wires := exp_a },
      { name := "exp_b", width := 8, wires := exp_b },
      { name := "mant_a", width := 24, wires := mant_a },
      { name := "mant_b", width := 24, wires := mant_b },
      { name := "exp_diff", width := 9, wires := exp_diff },
      { name := "big_exp", width := 8, wires := big_exp },
      { name := "big_mant", width := 24, wires := big_mant },
      { name := "aligned", width := 27, wires := aligned }
    ] }

def fpAdder_Stage2Circuit : Circuit := mkFPAdder_Stage2_Align

/-! ## Pipeline Stage 3: Mantissa Add + Leading-Zero Detect -/

def mkFPAdder_Stage3_AddSub : Circuit :=
  let big_mant := makeIndexedWires "big_mant" 24
  let aligned := makeIndexedWires "aligned" 27
  let eff_sub := Wire.mk "eff_sub"
  let sticky := Wire.mk "sticky"
  let zero := Wire.mk "zero"

  let sum_full := makeIndexedWires "s3_sum_full" 28
  let sum := makeIndexedWires "sum" 27
  let overflow := Wire.mk "overflow"
  let lead_pos := makeIndexedWires "lead_pos" 5
  let found := Wire.mk "found"

  let one := Wire.mk "s3_one"
  let one_gate := Gate.mkNOT zero one

  -- Operands of the widened adder: the big mantissa enters at [26:3] behind three
  -- low zeros, and the already-aligned small mantissa occupies [26:0], so its own
  -- guard/round/sticky bits add in at their natural weight.
  let big_ext := makeIndexedWires "s3_big_ext" 28
  let big_ext_gates := (List.range 28).map (fun i =>
    if 3 <= i && i < 27 then Gate.mkBUF (big_mant[i - 3]!) (big_ext[i]!)
    else Gate.mkBUF zero (big_ext[i]!))

  let aligned_ext := makeIndexedWires "s3_aligned_ext" 28
  let aligned_ext_gates := (List.range 27).map (fun i =>
    Gate.mkBUF (aligned[i]!) (aligned_ext[i]!)) ++
    [Gate.mkBUF zero (aligned_ext[27]!)]

  let cond_inv_aligned := makeIndexedWires "s3_cond_inv_al" 28
  let cond_inv_gates := (List.range 28).map fun i =>
    Gate.mkXOR (aligned_ext[i]!) eff_sub (cond_inv_aligned[i]!)

  -- An effective subtraction whose subtrahend lost bits below the window must borrow
  -- one unit from bit 0: the exact difference is (A - B - 1) + (1 - epsilon).
  -- A carry-in of zero (instead of eff_sub) subtracts exactly one.
  let borrow_ulp := Wire.mk "s3_borrow"
  let borrow_gates := [
    Gate.mkAND eff_sub sticky borrow_ulp
  ]
  let eff_sub_corr_gate := [Gate.mkXOR eff_sub borrow_ulp (Wire.mk "s3_eff_sub_final")]
  let eff_sub_final := Wire.mk "s3_eff_sub_final"

  let (sum_add_gates, _sum_carry) :=
    mkKoggeStoneAdd big_ext cond_inv_aligned eff_sub_final sum_full "s3_mantadd"

  -- Parallel prefix leading zero count over the full 28-bit sum_full: the carry
  -- bit is significant, and `found` (whether the sum is non-zero) is derived from
  -- the same scan.
  let lz_v := makeIndexedWires "s3_lz_v" 28
  let lz_p := (List.range 28).map fun i => makeIndexedWires ("s3_lz_p_" ++ toString i) 5
  let lz_leaf_gates := (List.range 28).flatMap fun i =>
    [Gate.mkBUF (sum_full[i]!) (lz_v[i]!)] ++
    (List.range 5).map fun k =>
      let bit_val := if (i >>> k) &&& 1 == 1 then one else zero
      Gate.mkBUF bit_val ((lz_p[i]!)[k]!)

  let strides := [1, 2, 4, 8, 16]
  let (lz_prefix_gates, lz_final_v, lz_final_p) :=
    strides.foldl (fun (acc : List Gate × List Wire × List (List Wire)) stride =>
      let (gates_acc, v_prev, p_prev) := acc
      let lt := "s3_lz_s" ++ toString stride
      let v_new := makeIndexedWires (lt ++ "_v") 28
      let p_new := (List.range 28).map fun i => makeIndexedWires (lt ++ "_p_" ++ toString i) 5

      let level_gates := (List.range 28).flatMap fun i =>
        if i + stride < 28 then
          let merge_v := Wire.mk (lt ++ "_mv_" ++ toString i)
          [Gate.mkOR (v_prev[i + stride]!) (v_prev[i]!) merge_v,
           Gate.mkBUF merge_v (v_new[i]!)] ++
          (List.range 5).map fun k =>
            Gate.mkMUX ((p_prev[i]!)[k]!) ((p_prev[i + stride]!)[k]!) (v_prev[i + stride]!) ((p_new[i]!)[k]!)
        else
          [Gate.mkBUF (v_prev[i]!) (v_new[i]!)] ++
          (List.range 5).map fun k =>
            Gate.mkBUF ((p_prev[i]!)[k]!) ((p_new[i]!)[k]!)

      (gates_acc ++ level_gates, v_new, p_new)
    ) ([], lz_v, lz_p)

  let lead_pos_gates := (List.range 5).map fun k =>
    Gate.mkBUF ((lz_final_p[0]!)[k]!) (lead_pos[k]!)
  let found_gate := Gate.mkBUF (lz_final_v[0]!) found
  let sum_out_gates := (List.range 27).map fun i =>
    Gate.mkBUF (sum_full[i]!) (sum[i]!)
  let overflow_gate := Gate.mkBUF (sum_full[27]!) overflow

  let all_gates :=
    [one_gate] ++ big_ext_gates ++ aligned_ext_gates ++ cond_inv_gates ++ borrow_gates ++
    eff_sub_corr_gate ++ sum_add_gates ++
    lz_leaf_gates ++ lz_prefix_gates ++ lead_pos_gates ++ sum_out_gates ++ [found_gate, overflow_gate]

  { name := "FPAdder_Stage3_AddSub"
    inputs := big_mant ++ aligned ++ [eff_sub, sticky, zero]
    outputs := sum ++ [overflow] ++ lead_pos ++ [found]
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "big_mant", width := 24, wires := big_mant },
      { name := "aligned", width := 27, wires := aligned },
      { name := "sum", width := 27, wires := sum },
      { name := "lead_pos", width := 5, wires := lead_pos }
    ] }

def fpAdder_Stage3Circuit : Circuit := mkFPAdder_Stage3_AddSub

/-! ## Pipeline Stage 4: Normalize + Special values + Pack + Exceptions -/

def mkFPAdder_Stage4_NormRound : Circuit :=
  let big_sign := Wire.mk "big_sign"
  let eff_sub := Wire.mk "eff_sub"
  let big_exp := makeIndexedWires "big_exp" 8
  let sum := makeIndexedWires "sum" 27
  let lead_pos := makeIndexedWires "lead_pos" 5
  let overflow := Wire.mk "overflow"
  let found := Wire.mk "found"
  let sticky := Wire.mk "sticky"
  let any_nan := Wire.mk "any_nan"
  let any_snan := Wire.mk "any_snan"
  let any_special := Wire.mk "any_special"
  let inf_sub_inf := Wire.mk "inf_sub_inf"
  let inf_result_sign := Wire.mk "inf_result_sign"
  let a_is_inf := Wire.mk "a_is_inf"
  let b_is_inf := Wire.mk "b_is_inf"
  let rm := makeIndexedWires "rm" 3
  let zero := Wire.mk "zero"

  let result := makeIndexedWires "result" 32
  let exc := makeIndexedWires "exc" 5

  let one := Wire.mk "s4_one"
  let one_gate := Gate.mkNOT zero one

  -- Overflow case: a carry out of the mantissa adder widens the exponent.
  let ovf_exp := makeIndexedWires "s4_ovf_exp" 8
  let ovf_exp_one := makeIndexedWires "s4_ovf_exp_one" 8
  let ovf_exp_one_gates := [Gate.mkBUF one (ovf_exp_one[0]!)] ++
    (List.range 7).map (fun i => Gate.mkBUF zero (ovf_exp_one[i+1]!))
  let (ovf_exp_add_gates, _ovf_exp_carry) :=
    mkAddFor (AdderSpec.minArea big_exp.length .none) big_exp ovf_exp_one zero ovf_exp "s4_ovfexp"

  -- If the widened exponent has saturated, the magnitude is unrepresentable and
  -- IEEE 754 requires +/-inf.  Shifting the mantissa down instead (the carry
  -- renorm, which is right on its own) would leave exp=all-ones with a non-zero
  -- mantissa, i.e. a NaN, so the mantissa must be cleared on this path.
  let ovf_ones_l1 := (List.range 4).map fun i => Wire.mk s!"s4_ovf_ones_l1_{i}"
  let ovf_ones_l2 := (List.range 2).map fun i => Wire.mk s!"s4_ovf_ones_l2_{i}"
  let ovf_exp_all_ones := Wire.mk "s4_ovf_exp_all_ones"
  let ovf_ones_gates :=
    (List.range 4).map (fun i =>
      Gate.mkAND (ovf_exp[2 * i]!) (ovf_exp[2 * i + 1]!) (ovf_ones_l1[i]!)) ++
    [ Gate.mkAND (ovf_ones_l1[0]!) (ovf_ones_l1[1]!) (ovf_ones_l2[0]!),
      Gate.mkAND (ovf_ones_l1[2]!) (ovf_ones_l1[3]!) (ovf_ones_l2[1]!),
      Gate.mkAND (ovf_ones_l2[0]!) (ovf_ones_l2[1]!) ovf_exp_all_ones ]

  let inf_ovf := Wire.mk "s4_inf_ovf"
  let not_inf_ovf := Wire.mk "s4_not_inf_ovf"
  let ovf_any := Wire.mk "s4_ovf_any"
  let sat_ovf := Wire.mk "s4_sat_ovf"
  let to_inf := Wire.mk "s4_to_inf"
  let rm_rtz := Wire.mk "s4_rm_rtz"
  let rm_rdn := Wire.mk "s4_rm_rdn"
  let rm_rup := Wire.mk "s4_rm_rup"
  let inf_ovf_gates := [
    Gate.mkAND overflow ovf_exp_all_ones ovf_any,
    -- rm as the instruction gives it: 001 rtz, 010 rdn, 011 rup
    Gate.mkNOT (rm[2]!) (Wire.mk "s4_nrm2"),
    Gate.mkNOT (rm[1]!) (Wire.mk "s4_nrm1"),
    Gate.mkNOT (rm[0]!) (Wire.mk "s4_nrm0"),
    Gate.mkAND (Wire.mk "s4_nrm2") (Wire.mk "s4_nrm1") (Wire.mk "s4_nrm21"),
    Gate.mkAND (Wire.mk "s4_nrm21") (rm[0]!) rm_rtz,
    Gate.mkAND (Wire.mk "s4_nrm2") (rm[1]!) (Wire.mk "s4_rm10"),
    Gate.mkAND (Wire.mk "s4_rm10") (Wire.mk "s4_nrm0") rm_rdn,
    Gate.mkAND (Wire.mk "s4_rm10") (rm[0]!) rm_rup,
    -- IEEE 754 section 7.4: an overflowed sum is an infinity only when the
    -- rounding direction points away from zero for this sign.  Toward zero is
    -- rtz always, rdn for a positive sum and rup for a negative one; round to
    -- nearest counts as away.  The other modes give the largest finite value.
    Gate.mkNOT big_sign (Wire.mk "s4_tz_nsign"),
    Gate.mkAND rm_rdn (Wire.mk "s4_tz_nsign") (Wire.mk "s4_tz_rdn"),
    Gate.mkAND rm_rup big_sign (Wire.mk "s4_tz_rup"),
    Gate.mkOR rm_rtz (Wire.mk "s4_tz_rdn") (Wire.mk "s4_tz_a"),
    Gate.mkOR (Wire.mk "s4_tz_a") (Wire.mk "s4_tz_rup") (Wire.mk "s4_tz_any"),
    Gate.mkNOT (Wire.mk "s4_tz_any") to_inf,
    Gate.mkNOT to_inf (Wire.mk "s4_not_to_inf"),
    Gate.mkAND ovf_any to_inf inf_ovf,
    Gate.mkAND ovf_any (Wire.mk "s4_not_to_inf") sat_ovf,
    Gate.mkNOT inf_ovf not_inf_ovf
  ]

  -- Mantissa of the overflow path: the sum halved, so the fraction starts one bit
  -- higher than in the normal path.
  let ovf_mant := makeIndexedWires "s4_ovf_mant" 23
  let ovf_mant_gates := (List.range 23).map fun i =>
    Gate.mkAND (sum[i + 4]!) not_inf_ovf (ovf_mant[i]!)

  -- Non-overflow: normalize left-shift
  let const_23 := makeIndexedWires "s4_const23" 5
  -- 26: the position the implicit mantissa bit must reach after normalizing.
  let const_23_gates := [
    Gate.mkBUF zero (const_23[0]!),
    Gate.mkBUF one (const_23[1]!),
    Gate.mkBUF zero (const_23[2]!),
    Gate.mkBUF one (const_23[3]!),
    Gate.mkBUF one (const_23[4]!)
  ]

  let lshift_amt := makeIndexedWires "s4_lshift_amt" 5
  let (lshift_sub_gates, _lshift_borrow) :=
    mkSubFor (AdderSpec.minArea const_23.length .one) const_23 lead_pos lshift_amt "s4_lshamt" one

  let sum_lower := makeIndexedWires "s4_sum_lower" 27
  let sum_lower_gates := (List.range 27).map fun i =>
    Gate.mkBUF (sum[i]!) (sum_lower[i]!)

  let norm_mant_full := makeIndexedWires "s4_norm_mant_full" 27
  let lshift_gates := mkBarrelShiftLeft sum_lower lshift_amt norm_mant_full zero "s4_bsl"

  -- The fraction is the top 23 bits above the guard/round/sticky field.
  let norm_mant := makeIndexedWires "s4_norm_mant" 23
  let norm_mant_gates := (List.range 23).map fun i =>
    Gate.mkBUF (norm_mant_full[i + 3]!) (norm_mant[i]!)

  let lshift_ext := makeIndexedWires "s4_lshift_ext" 8
  let lshift_ext_gates := (List.range 5).map (fun i =>
    Gate.mkBUF (lshift_amt[i]!) (lshift_ext[i]!)) ++
    (List.range 3).map (fun i => Gate.mkBUF zero (lshift_ext[i + 5]!))

  let norm_exp := makeIndexedWires "s4_norm_exp" 8
  let (norm_exp_sub_gates, norm_exp_borrow) :=
    mkSubFor (AdderSpec.minArea big_exp.length .one) big_exp lshift_ext norm_exp "s4_normexp" one

  -- Subnormal result: exponent field 0, mantissa counted in multiples of 2^-149.
  -- The normalizing shift put the leading 1 of the sum at bit 26, whose weight is
  -- 2^(norm_exp-127); a subnormal needs that weight at 2^norm_exp, i.e. the
  -- mantissa is the normalized sum shifted down by (4 - norm_exp).  The shift
  -- range is 4..26 because every operand is a multiple of the quantum, so a
  -- nonzero subnormal result carries its leading 1 no lower than bit 4 of the
  -- normalized sum.
  --
  -- No rounding is needed here: the sum of two multiples of 2^-149 is a multiple
  -- of 2^-149, so a subnormal result is exact and round_up is forced low below.
  let norm_exp_zero := Wire.mk "s4_nexp_zero"
  let (norm_exp_any, norm_exp_or_gates) :=
    mkOrReduce "s4_nexp_orbit" ((List.range 8).map fun i => norm_exp[i]!) zero
  -- norm_exp = big_exp - shift on a full exponent field, so bit 7 is a value bit,
  -- not a sign: the subtractor's borrow is what says the exponent went negative.
  let norm_exp_le_zero := Wire.mk "s4_nexp_le0"
  let subnormal_res := Wire.mk "s4_subnormal"
  let not_overflow_pre := Wire.mk "s4_not_ovf_pre"
  let subnormal_gates := [
    Gate.mkNOT norm_exp_any norm_exp_zero,
    Gate.mkOR norm_exp_zero norm_exp_borrow norm_exp_le_zero,
    Gate.mkNOT overflow not_overflow_pre,
    Gate.mkAND norm_exp_le_zero not_overflow_pre subnormal_res
  ]

  let sub_shift := makeIndexedWires "s4_sub_shift" 5
  let four5 := makeIndexedWires "s4_four5" 5
  let four5_gates := [
    Gate.mkBUF zero (four5[0]!), Gate.mkBUF zero (four5[1]!),
    Gate.mkBUF one (four5[2]!), Gate.mkBUF zero (four5[3]!),
    Gate.mkBUF zero (four5[4]!)
  ]
  let (sub_shift_gates, _sub_shift_borrow) :=
    mkSubFor (AdderSpec.minArea 5 .one) four5
      ((List.range 5).map fun i => norm_exp[i]!) sub_shift "s4_subsh" one

  let sub_mant_full := makeIndexedWires "s4_sub_mant_full" 27
  let sub_shift_barrel_gates :=
    mkBarrelShiftRight norm_mant_full sub_shift sub_mant_full zero "s4_bsr_sub"
  let sub_mant := (List.range 23).map fun i => sub_mant_full[i]!

  let norm_or_sub_mant := makeIndexedWires "s4_ns_mant" 23
  let ns_mant_gates := (List.range 23).map fun i =>
    Gate.mkMUX (norm_mant[i]!) (sub_mant[i]!) subnormal_res (norm_or_sub_mant[i]!)
  let result_mant := makeIndexedWires "s4_res_mant" 23
  let result_mant_gates := (List.range 23).map fun i =>
    Gate.mkMUX (norm_or_sub_mant[i]!) (ovf_mant[i]!) overflow (result_mant[i]!)

  let norm_or_sub_exp := makeIndexedWires "s4_ns_exp" 8
  let ns_exp_gates := (List.range 8).map fun i =>
    Gate.mkMUX (norm_exp[i]!) zero subnormal_res (norm_or_sub_exp[i]!)
  let result_exp := makeIndexedWires "s4_res_exp" 8
  let result_exp_gates := (List.range 8).map fun i =>
    Gate.mkMUX (norm_or_sub_exp[i]!) (ovf_exp[i]!) overflow (result_exp[i]!)

  -- Guard, round and sticky.  The normal path reads them from the top of the
  -- normalize shift; the overflow path halves the sum, so its three bits sit one
  -- position higher.
  let ovf_G := Wire.mk "s4_ovf_G"
  let ovf_R := Wire.mk "s4_ovf_R"
  let ovf_S := Wire.mk "s4_ovf_S"
  let ovf_s_or := Wire.mk "s4_ovf_s_or"
  let ovf_s_pre := Wire.mk "s4_ovf_s_pre"
  let ovf_grs_gates := [
    Gate.mkAND (sum[3]!) not_inf_ovf ovf_G,
    Gate.mkAND (sum[2]!) not_inf_ovf ovf_R,
    Gate.mkOR (sum[1]!) (sum[0]!) ovf_s_or,
    Gate.mkOR ovf_s_or sticky ovf_s_pre,
    Gate.mkAND ovf_s_pre not_inf_ovf ovf_S
  ]

  let norm_G := norm_mant_full[2]!
  let norm_R := norm_mant_full[1]!
  let norm_S := Wire.mk "s4_norm_S"
  let norm_s_gate := Gate.mkOR (norm_mant_full[0]!) sticky norm_S

  let g_bit := Wire.mk "s4_g_bit"
  let r_bit := Wire.mk "s4_r_bit"
  let s_bit := Wire.mk "s4_s_bit"
  let grs_mux_gates := [
    Gate.mkMUX norm_G ovf_G overflow g_bit,
    Gate.mkMUX norm_R ovf_R overflow r_bit,
    Gate.mkMUX norm_S ovf_S overflow s_bit
  ]

  -- Rounding modes: RISC-V rm is 000 RNE, 001 RTZ, 010 RDN, 011 RUP, 100 RMM,
  -- 101..111 reserved and behaving as RNE.  The magnitude moves by at most one
  -- ulp, so a mode is characterised by when it rounds away from zero.
  let rs_or := Wire.mk "s4_rs_or"
  let rsl_or := Wire.mk "s4_rsl_or"
  let any_rem := Wire.mk "s4_any_rem"
  let rne_up := Wire.mk "s4_rne_up"
  let rdn_up := Wire.mk "s4_rdn_up"
  let rup_up := Wire.mk "s4_rup_up"
  let not_sign := Wire.mk "s4_not_sign"
  let not_rm0 := Wire.mk "s4_not_rm0"
  let not_rm1 := Wire.mk "s4_not_rm1"
  let not_rm2 := Wire.mk "s4_not_rm2"
  let is_rtz := Wire.mk "s4_is_rtz"
  let is_rdn := Wire.mk "s4_is_rdn"
  let is_rup := Wire.mk "s4_is_rup"
  let is_rmm := Wire.mk "s4_is_rmm"
  let grp_n2n1 := Wire.mk "s4_grp_n2n1"
  let grp_n2p1 := Wire.mk "s4_grp_n2p1"
  let grp_p2n1 := Wire.mk "s4_grp_p2n1"
  let up_rdn := Wire.mk "s4_up_rdn"
  let up_rup := Wire.mk "s4_up_rup"
  let up_rmm := Wire.mk "s4_up_rmm"
  let round_up_pre := Wire.mk "s4_round_up_pre"
  let round_up := Wire.mk "s4_round_up"
  let rnd_ctrl_gates := [
    Gate.mkOR r_bit s_bit rs_or,
    Gate.mkOR rs_or (result_mant[0]!) rsl_or,
    Gate.mkAND g_bit rsl_or rne_up,
    Gate.mkOR g_bit rs_or any_rem,
    Gate.mkNOT big_sign not_sign,
    Gate.mkAND any_rem big_sign rdn_up,
    Gate.mkAND any_rem not_sign rup_up,
    Gate.mkNOT (rm[0]!) not_rm0,
    Gate.mkNOT (rm[1]!) not_rm1,
    Gate.mkNOT (rm[2]!) not_rm2,
    Gate.mkAND not_rm2 not_rm1 grp_n2n1,
    Gate.mkAND grp_n2n1 (rm[0]!) is_rtz,
    Gate.mkAND not_rm2 (rm[1]!) grp_n2p1,
    Gate.mkAND grp_n2p1 not_rm0 is_rdn,
    Gate.mkAND grp_n2p1 (rm[0]!) is_rup,
    Gate.mkAND (rm[2]!) not_rm1 grp_p2n1,
    Gate.mkAND grp_p2n1 not_rm0 is_rmm,
    Gate.mkMUX rne_up rdn_up is_rdn up_rdn,
    Gate.mkMUX up_rdn rup_up is_rup up_rup,
    Gate.mkMUX up_rup g_bit is_rmm up_rmm,
    Gate.mkMUX up_rmm zero is_rtz round_up_pre
  ]
  -- A subnormal result is exact, so no mode may round it.
  let not_subnormal_res := Wire.mk "s4_not_subnormal"
  let round_gate := [
    Gate.mkNOT subnormal_res not_subnormal_res,
    Gate.mkAND round_up_pre not_subnormal_res round_up
  ]

  let mant_inc := makeIndexedWires "s4_m_inc" 23
  let mant_inc_c := makeIndexedWires "s4_m_inc_c" 24
  let mant_inc_gates := [Gate.mkBUF round_up (mant_inc_c[0]!)] ++ (List.range 23).flatMap fun i =>
    [Gate.mkXOR (result_mant[i]!) (mant_inc_c[i]!) (mant_inc[i]!),
     Gate.mkAND (result_mant[i]!) (mant_inc_c[i]!) (mant_inc_c[i + 1]!)]
  let mant_rollover := mant_inc_c[23]!

  let exp_post_rnd := makeIndexedWires "s4_exp_post_rnd" 8
  let exp_pr_c := makeIndexedWires "s4_epr_c" 9
  let exp_pr_gates := [Gate.mkBUF mant_rollover (exp_pr_c[0]!)] ++ (List.range 8).flatMap fun i =>
    [Gate.mkXOR (result_exp[i]!) (exp_pr_c[i]!) (exp_post_rnd[i]!),
     Gate.mkAND (result_exp[i]!) (exp_pr_c[i]!) (exp_pr_c[i + 1]!)]

  let rounded_mant := makeIndexedWires "s4_rnd_mant" 23
  let not_rollover := Wire.mk "s4_not_rollover"
  let rnd_mant_gates := [Gate.mkNOT mant_rollover not_rollover] ++
    (List.range 23).map fun i =>
      Gate.mkAND (mant_inc[i]!) not_rollover (rounded_mant[i]!)

  -- A mantissa carry is not the only way past the maximum.  A sum just above
  -- FLT_MAX whose rounding direction points away from zero has a mantissa that
  -- rolls over, and the increment then saturates an exponent that was already
  -- at the top: the result is an infinity.  IEEE 754 section 7.4 compares the
  -- larger finite value against the result rounded with an unbounded exponent,
  -- so this case raises OF too.  `ovf_any` above sees only the carry.
  let prnd_l1 := (List.range 4).map fun i => Wire.mk s!"s4_prnd_l1_{i}"
  let prnd_l2 := (List.range 2).map fun i => Wire.mk s!"s4_prnd_l2_{i}"
  let exp_sat := Wire.mk "s4_exp_sat"
  let ovf_rnd := Wire.mk "s4_ovf_rnd"
  let ovf_rnd_gates :=
    (List.range 4).map (fun i =>
      Gate.mkAND (exp_post_rnd[2 * i]!) (exp_post_rnd[2 * i + 1]!) (prnd_l1[i]!)) ++
    [ Gate.mkAND (prnd_l1[0]!) (prnd_l1[1]!) (prnd_l2[0]!),
      Gate.mkAND (prnd_l1[2]!) (prnd_l1[3]!) (prnd_l2[1]!),
      Gate.mkAND (prnd_l2[0]!) (prnd_l2[1]!) exp_sat,
      Gate.mkAND mant_rollover exp_sat ovf_rnd ]

  let not_found := Wire.mk "s4_not_found"
  let not_sum_is_zero := Wire.mk "s4_not_siz"
  let zero_det_gates := [
    Gate.mkNOT found not_found,
    Gate.mkNOT not_found not_sum_is_zero
  ]

  -- Sign of an exactly zero result (IEEE 754-2008 §6.3).  Like-signed addends
  -- keep that sign (-0 + -0 = -0); a cancellation of like-signed operands
  -- (x - x, -0 - +0) is +0 in every mode except RDN, which gives -0.
  -- `eff_sub` is the sign comparison of the aligned operands, so it picks the
  -- rule: differ (subtraction) selects the mode, agree selects `big_sign`.
  let same_sign := Wire.mk "s4_same_sign"
  let zero_sign := Wire.mk "s4_zero_sign"
  let result_sign := Wire.mk "s4_result_sign"
  -- `not_sum_is_zero` holds "the sum is nonzero", so it selects the ordinary
  -- sign; the zero case takes `zero_sign`.
  let result_sign_gate := [
    Gate.mkNOT eff_sub same_sign,
    Gate.mkMUX is_rdn big_sign same_sign zero_sign,
    Gate.mkMUX zero_sign big_sign not_sum_is_zero result_sign
  ]

  let result_exp_masked := makeIndexedWires "s4_res_exp_m" 8
  let result_exp_mask_gates := (List.range 8).map fun i =>
    Gate.mkAND (exp_post_rnd[i]!) not_sum_is_zero (result_exp_masked[i]!)

  let result_mant_masked := makeIndexedWires "s4_res_mant_m" 23
  let result_mant_mask_gates := (List.range 23).map fun i =>
    Gate.mkAND (rounded_mant[i]!) not_sum_is_zero (result_mant_masked[i]!)

  let normal_result := makeIndexedWires "s4_normal_res" 32
  let normal_pack_gates :=
    (List.range 23).map (fun i => Gate.mkBUF (result_mant_masked[i]!) (normal_result[i]!)) ++
    (List.range 8).map (fun i => Gate.mkBUF (result_exp_masked[i]!) (normal_result[23 + i]!)) ++
    [Gate.mkBUF result_sign (normal_result[31]!)]

  let canonical_nan := makeIndexedWires "s4_cnan" 32
  let nan_gates := (List.range 32).map fun i =>
    let bit_val := match i with
      | 22 => one
      | 23 => one | 24 => one | 25 => one | 26 => one
      | 27 => one | 28 => one | 29 => one | 30 => one
      | _ => zero
    Gate.mkBUF bit_val (canonical_nan[i]!)

  let inf_result := makeIndexedWires "s4_inf_res" 32
  let inf_result_gates := (List.range 32).map fun i =>
    let bit_val := match i with
      | 31 => inf_result_sign
      | 23 => one | 24 => one | 25 => one | 26 => one
      | 27 => one | 28 => one | 29 => one | 30 => one
      | _ => zero
    Gate.mkBUF bit_val (inf_result[i]!)

  let any_inf := Wire.mk "s4_any_inf"
  let any_inf_gate := Gate.mkOR a_is_inf b_is_inf any_inf
  let not_inf_sub_inf := Wire.mk "s4_not_inf_sub_inf"
  let not_inf_sub_inf_gate := Gate.mkNOT inf_sub_inf not_inf_sub_inf
  let inf_not_nv := Wire.mk "s4_inf_not_nv"
  let inf_not_nv_gate := Gate.mkAND any_inf not_inf_sub_inf inf_not_nv

  let is_nan_result := Wire.mk "s4_is_nan_result"
  let is_nan_result_gate := Gate.mkOR any_nan inf_sub_inf is_nan_result

  -- Saturation of an overflowing sum: the largest finite magnitude, exponent
  -- all ones minus one and fraction all ones.  It is applied after rounding,
  -- because rounding the saturated value could carry into the exponent and turn
  -- it back into an infinity.
  let sat_result := makeIndexedWires "s4_sat_res" 32
  let sat_result_gates := (List.range 32).map fun i =>
    let bit_val := match i with
      | 31 => result_sign
      | 23 => zero | 24 => one | 25 => one | 26 => one
      | 27 => one | 28 => one | 29 => one | 30 => one
      | _ => one
    Gate.mkBUF bit_val (sat_result[i]!)
  let mux0_result := makeIndexedWires "s4_mux0_res" 32
  let mux0_gates := (List.range 32).map fun i =>
    Gate.mkMUX (normal_result[i]!) (sat_result[i]!) sat_ovf (mux0_result[i]!)
  let pre_result := makeIndexedWires "s4_pre_res" 32
  let mux1_gates := (List.range 32).map fun i =>
    Gate.mkMUX (mux0_result[i]!) (inf_result[i]!) inf_not_nv (pre_result[i]!)
  let final_mux_gates := (List.range 32).map fun i =>
    Gate.mkMUX (pre_result[i]!) (canonical_nan[i]!) is_nan_result (result[i]!)

  let exc_nv := Wire.mk "s4_exc_nv"
  let exc_nv_gate := Gate.mkOR any_snan inf_sub_inf exc_nv

  let ovf_loses_bit := Wire.mk "s4_ovf_loses_bit"
  let ovf_loses_gate := Gate.mkAND overflow (sum[0]!) ovf_loses_bit
  -- NX: any remainder at all.  sticky alone is no longer sufficient now that the
  -- guard and round bits survive in the datapath instead of folding into sticky.
  let nx_pre := Wire.mk "s4_nx_pre"
  let nx_pre_gate := Gate.mkOR any_rem ovf_loses_bit nx_pre
  let nx_raw := Wire.mk "s4_nx_raw"
  -- A saturated overflow was rounded away to infinity, so it is inexact too.
  let nx_raw_gate := Gate.mkOR nx_pre ovf_any nx_raw
  let not_any_special := Wire.mk "s4_not_any_special"
  let not_any_special_gate := Gate.mkNOT any_special not_any_special
  let exc_nx := Wire.mk "s4_exc_nx"
  let exc_nx_gate := Gate.mkAND nx_raw not_any_special exc_nx
  let of_raw := Wire.mk "s4_of_raw"
  let of_raw_gate := Gate.mkOR ovf_any ovf_rnd of_raw
  let exc_of := Wire.mk "s4_exc_of"
  let exc_of_gate := Gate.mkAND of_raw not_any_special exc_of

  -- fflags: bit0=NX bit1=UF bit2=OF bit3=DZ bit4=NV.
  -- UF needs a subnormal result to exist first; the adder has no subnormal
  -- output path, so it stays 0.  DZ is structurally impossible for an adder.
  let exc_output_gates := [
    Gate.mkBUF exc_nx (exc[0]!),
    Gate.mkBUF zero (exc[1]!),
    Gate.mkBUF exc_of (exc[2]!),
    Gate.mkBUF zero (exc[3]!),
    Gate.mkBUF exc_nv (exc[4]!)
  ]

  let all_gates :=
    [one_gate] ++ ovf_exp_one_gates ++ ovf_exp_add_gates ++ ovf_ones_gates ++
    inf_ovf_gates ++ ovf_mant_gates ++
    const_23_gates ++ lshift_sub_gates ++ sum_lower_gates ++ lshift_gates ++
    norm_mant_gates ++ lshift_ext_gates ++ norm_exp_sub_gates ++
    norm_exp_or_gates ++ subnormal_gates ++ four5_gates ++ sub_shift_gates ++
    sub_shift_barrel_gates ++ ns_mant_gates ++ ns_exp_gates ++
    result_mant_gates ++ result_exp_gates ++
    ovf_grs_gates ++ [norm_s_gate] ++ grs_mux_gates ++ rnd_ctrl_gates ++ round_gate ++
    mant_inc_gates ++ exp_pr_gates ++ rnd_mant_gates ++ ovf_rnd_gates ++
    zero_det_gates ++ result_sign_gate ++
    result_exp_mask_gates ++ result_mant_mask_gates ++ normal_pack_gates ++
    nan_gates ++ inf_result_gates ++
    [any_inf_gate, not_inf_sub_inf_gate, inf_not_nv_gate, is_nan_result_gate] ++
    sat_result_gates ++ mux0_gates ++ mux1_gates ++ final_mux_gates ++
    [exc_nv_gate, ovf_loses_gate, nx_pre_gate, nx_raw_gate, not_any_special_gate, exc_nx_gate,
     of_raw_gate, exc_of_gate] ++
    exc_output_gates

  { name := "FPAdder_Stage4_NormRound"
    inputs := [big_sign, eff_sub] ++ big_exp ++ sum ++ lead_pos ++
              [overflow, found, sticky, any_nan, any_snan, any_special,
               inf_sub_inf, inf_result_sign, a_is_inf, b_is_inf] ++ rm ++ [zero]
    outputs := result ++ exc
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "big_exp", width := 8, wires := big_exp },
      { name := "sum", width := 27, wires := sum },
      { name := "lead_pos", width := 5, wires := lead_pos },
      { name := "result", width := 32, wires := result },
      { name := "exc", width := 5, wires := exc },
      { name := "rm", width := 3, wires := rm }
    ] }

def fpAdder_Stage4Circuit : Circuit := mkFPAdder_Stage4_NormRound

/-! ## Top-Level Hierarchical Circuit -/

def fpAdderCircuit : Circuit :=
  let src1       := makeIndexedWires "src1" 32
  let src2       := makeIndexedWires "src2" 32
  let op_sub     := Wire.mk "op_sub"
  let rm         := makeIndexedWires "rm" 3
  let dest_tag   := makeIndexedWires "dest_tag" 6
  let valid_in   := Wire.mk "valid_in"
  let clock      := Wire.mk "clock"
  let reset      := Wire.mk "reset"
  let zero       := Wire.mk "zero"

  let result     := makeIndexedWires "result" 32
  let tag_out    := makeIndexedWires "tag_out" 6
  let exc        := makeIndexedWires "exc" 5
  let valid_out  := Wire.mk "valid_out"

  -- Stage 1 wires
  let s1_sign_a := Wire.mk "s1_sign_a"
  let s1_eff_sign_b := Wire.mk "s1_eff_sign_b"
  let s1_exp_a := makeIndexedWires "s1_exp_a" 8
  let s1_exp_b := makeIndexedWires "s1_exp_b" 8
  let s1_mant_a := makeIndexedWires "s1_mant_a" 24
  let s1_mant_b := makeIndexedWires "s1_mant_b" 24
  let s1_exp_diff := makeIndexedWires "s1_exp_diff" 9
  let s1_swap := Wire.mk "s1_swap"
  let s1_any_nan := Wire.mk "s1_any_nan"
  let s1_any_snan := Wire.mk "s1_any_snan"
  let s1_any_special := Wire.mk "s1_any_special"
  let s1_both_inf := Wire.mk "s1_both_inf"
  let s1_a_is_inf := Wire.mk "s1_a_is_inf"
  let s1_b_is_inf := Wire.mk "s1_b_is_inf"

  let stage1_inst : CircuitInstance := {
    moduleName := "FPAdder_Stage1_Unpack"
    instName := "u_stage1"
    portMap :=
      ((List.range 32).map fun i => (s!"src1_{i}", src1[i]!)) ++
      ((List.range 32).map fun i => (s!"src2_{i}", src2[i]!)) ++
      [("op_sub", op_sub), ("zero", zero),
       ("sign_a", s1_sign_a), ("eff_sign_b", s1_eff_sign_b)] ++
      ((List.range 8).map fun i => (s!"exp_a_{i}", s1_exp_a[i]!)) ++
      ((List.range 8).map fun i => (s!"exp_b_{i}", s1_exp_b[i]!)) ++
      ((List.range 24).map fun i => (s!"mant_a_{i}", s1_mant_a[i]!)) ++
      ((List.range 24).map fun i => (s!"mant_b_{i}", s1_mant_b[i]!)) ++
      ((List.range 9).map fun i => (s!"exp_diff_{i}", s1_exp_diff[i]!)) ++
      [("swap", s1_swap), ("any_nan", s1_any_nan), ("any_snan", s1_any_snan),
       ("any_special", s1_any_special), ("both_inf", s1_both_inf),
       ("a_is_inf", s1_a_is_inf), ("b_is_inf", s1_b_is_inf)]
  }

  -- Stage 1 DFFs
  let p1_sign_a := Wire.mk "p1_sign_a"
  let p1_eff_sign_b := Wire.mk "p1_eff_sign_b"
  let p1_exp_a := makeIndexedWires "p1_exp_a" 8
  let p1_exp_b := makeIndexedWires "p1_exp_b" 8
  let p1_mant_a := makeIndexedWires "p1_mant_a" 24
  let p1_mant_b := makeIndexedWires "p1_mant_b" 24
  let p1_exp_diff := makeIndexedWires "p1_exp_diff" 9
  let p1_swap := Wire.mk "p1_swap"
  let p1_any_nan := Wire.mk "p1_any_nan"
  let p1_any_snan := Wire.mk "p1_any_snan"
  let p1_any_special := Wire.mk "p1_any_special"
  let p1_both_inf := Wire.mk "p1_both_inf"
  let p1_a_is_inf := Wire.mk "p1_a_is_inf"
  let p1_b_is_inf := Wire.mk "p1_b_is_inf"
  let p1_rm := makeIndexedWires "p1_rm" 3
  let p1_tag := makeIndexedWires "p1_tag" 6
  let p1_valid := Wire.mk "p1_valid"

  let p1_dffs :=
    [Gate.mkDFF s1_sign_a clock reset p1_sign_a,
     Gate.mkDFF s1_eff_sign_b clock reset p1_eff_sign_b,
     Gate.mkDFF s1_swap clock reset p1_swap,
     Gate.mkDFF valid_in clock reset p1_valid,
     Gate.mkDFF s1_any_nan clock reset p1_any_nan,
     Gate.mkDFF s1_any_snan clock reset p1_any_snan,
     Gate.mkDFF s1_any_special clock reset p1_any_special,
     Gate.mkDFF s1_both_inf clock reset p1_both_inf,
     Gate.mkDFF s1_a_is_inf clock reset p1_a_is_inf,
     Gate.mkDFF s1_b_is_inf clock reset p1_b_is_inf] ++
    mkDFFBank s1_exp_a p1_exp_a clock reset ++
    mkDFFBank s1_exp_b p1_exp_b clock reset ++
    mkDFFBank s1_mant_a p1_mant_a clock reset ++
    mkDFFBank s1_mant_b p1_mant_b clock reset ++
    mkDFFBank s1_exp_diff p1_exp_diff clock reset ++
    mkDFFBank rm p1_rm clock reset ++
    mkDFFBank dest_tag p1_tag clock reset

  -- Stage 2 wires
  let s2_big_sign := Wire.mk "s2_big_sign"
  let s2_big_exp := makeIndexedWires "s2_big_exp" 8
  let s2_big_mant := makeIndexedWires "s2_big_mant" 24
  let s2_aligned := makeIndexedWires "s2_aligned" 27
  let s2_eff_sub := Wire.mk "s2_eff_sub"
  let s2_sticky := Wire.mk "s2_sticky"
  let s2_inf_sub_inf := Wire.mk "s2_inf_sub_inf"
  let s2_inf_result_sign := Wire.mk "s2_inf_result_sign"

  let stage2_inst : CircuitInstance := {
    moduleName := "FPAdder_Stage2_Align"
    instName := "u_stage2"
    portMap :=
      [("sign_a", p1_sign_a), ("eff_sign_b", p1_eff_sign_b)] ++
      ((List.range 8).map fun i => (s!"exp_a_{i}", p1_exp_a[i]!)) ++
      ((List.range 8).map fun i => (s!"exp_b_{i}", p1_exp_b[i]!)) ++
      ((List.range 24).map fun i => (s!"mant_a_{i}", p1_mant_a[i]!)) ++
      ((List.range 24).map fun i => (s!"mant_b_{i}", p1_mant_b[i]!)) ++
      ((List.range 9).map fun i => (s!"exp_diff_{i}", p1_exp_diff[i]!)) ++
      [("swap", p1_swap), ("both_inf", p1_both_inf), ("a_is_inf", p1_a_is_inf), ("zero", zero),
       ("big_sign", s2_big_sign)] ++
      ((List.range 8).map fun i => (s!"big_exp_{i}", s2_big_exp[i]!)) ++
      ((List.range 24).map fun i => (s!"big_mant_{i}", s2_big_mant[i]!)) ++
      ((List.range 27).map fun i => (s!"aligned_{i}", s2_aligned[i]!)) ++
      [("eff_sub", s2_eff_sub), ("sticky", s2_sticky),
       ("inf_sub_inf", s2_inf_sub_inf), ("inf_result_sign", s2_inf_result_sign)]
  }

  -- Stage 2 DFFs
  let p2_big_sign := Wire.mk "p2_big_sign"
  let p2_big_exp := makeIndexedWires "p2_big_exp" 8
  let p2_big_mant := makeIndexedWires "p2_big_mant" 24
  let p2_aligned := makeIndexedWires "p2_aligned" 27
  let p2_eff_sub := Wire.mk "p2_eff_sub"
  let p2_rm := makeIndexedWires "p2_rm" 3
  let p2_tag := makeIndexedWires "p2_tag" 6
  let p2_valid := Wire.mk "p2_valid"
  let p2_sticky := Wire.mk "p2_sticky"
  let p2_any_nan := Wire.mk "p2_any_nan"
  let p2_any_snan := Wire.mk "p2_any_snan"
  let p2_any_special := Wire.mk "p2_any_special"
  let p2_inf_sub_inf := Wire.mk "p2_inf_sub_inf"
  let p2_inf_result_sign := Wire.mk "p2_inf_result_sign"
  let p2_a_is_inf := Wire.mk "p2_a_is_inf"
  let p2_b_is_inf := Wire.mk "p2_b_is_inf"

  let p2_dffs :=
    [Gate.mkDFF s2_big_sign clock reset p2_big_sign,
     Gate.mkDFF s2_eff_sub clock reset p2_eff_sub,
     Gate.mkDFF p1_valid clock reset p2_valid,
     Gate.mkDFF s2_sticky clock reset p2_sticky,
     Gate.mkDFF p1_any_nan clock reset p2_any_nan,
     Gate.mkDFF p1_any_snan clock reset p2_any_snan,
     Gate.mkDFF p1_any_special clock reset p2_any_special,
     Gate.mkDFF s2_inf_sub_inf clock reset p2_inf_sub_inf,
     Gate.mkDFF s2_inf_result_sign clock reset p2_inf_result_sign,
     Gate.mkDFF p1_a_is_inf clock reset p2_a_is_inf,
     Gate.mkDFF p1_b_is_inf clock reset p2_b_is_inf] ++
    mkDFFBank s2_big_exp p2_big_exp clock reset ++
    mkDFFBank s2_big_mant p2_big_mant clock reset ++
    mkDFFBank s2_aligned p2_aligned clock reset ++
    mkDFFBank p1_rm p2_rm clock reset ++
    mkDFFBank p1_tag p2_tag clock reset

  -- Stage 3 wires
  let s3_sum := makeIndexedWires "s3_sum" 27
  let s3_overflow := Wire.mk "s3_overflow"
  let s3_lead_pos := makeIndexedWires "s3_lead_pos" 5
  let s3_found := Wire.mk "s3_found"

  let stage3_inst : CircuitInstance := {
    moduleName := "FPAdder_Stage3_AddSub"
    instName := "u_stage3"
    portMap :=
      ((List.range 24).map fun i => (s!"big_mant_{i}", p2_big_mant[i]!)) ++
      ((List.range 27).map fun i => (s!"aligned_{i}", p2_aligned[i]!)) ++
      [("eff_sub", p2_eff_sub), ("sticky", p2_sticky), ("zero", zero)] ++
      ((List.range 27).map fun i => (s!"sum_{i}", s3_sum[i]!)) ++
      [("overflow", s3_overflow)] ++
      ((List.range 5).map fun i => (s!"lead_pos_{i}", s3_lead_pos[i]!)) ++
      [("found", s3_found)]
  }

  -- Stage 3 DFFs
  let p3_big_sign := Wire.mk "p3_big_sign"
  let p3_eff_sub := Wire.mk "p3_eff_sub"
  let p3_big_exp := makeIndexedWires "p3_big_exp" 8
  let p3_sum := makeIndexedWires "p3_sum" 27
  let p3_lead_pos := makeIndexedWires "p3_lead_pos" 5
  let p3_overflow := Wire.mk "p3_overflow"
  let p3_found := Wire.mk "p3_found"
  let p3_rm := makeIndexedWires "p3_rm" 3
  let p3_tag := makeIndexedWires "p3_tag" 6
  let p3_valid := Wire.mk "p3_valid"
  let p3_sticky := Wire.mk "p3_sticky"
  let p3_any_nan := Wire.mk "p3_any_nan"
  let p3_any_snan := Wire.mk "p3_any_snan"
  let p3_any_special := Wire.mk "p3_any_special"
  let p3_inf_sub_inf := Wire.mk "p3_inf_sub_inf"
  let p3_inf_result_sign := Wire.mk "p3_inf_result_sign"
  let p3_a_is_inf := Wire.mk "p3_a_is_inf"
  let p3_b_is_inf := Wire.mk "p3_b_is_inf"

  let p3_dffs :=
    [Gate.mkDFF p2_big_sign clock reset p3_big_sign,
     Gate.mkDFF p2_eff_sub clock reset p3_eff_sub,
     Gate.mkDFF s3_overflow clock reset p3_overflow,
     Gate.mkDFF s3_found clock reset p3_found,
     Gate.mkDFF p2_valid clock reset p3_valid,
     Gate.mkDFF p2_sticky clock reset p3_sticky,
     Gate.mkDFF p2_any_nan clock reset p3_any_nan,
     Gate.mkDFF p2_any_snan clock reset p3_any_snan,
     Gate.mkDFF p2_any_special clock reset p3_any_special,
     Gate.mkDFF p2_inf_sub_inf clock reset p3_inf_sub_inf,
     Gate.mkDFF p2_inf_result_sign clock reset p3_inf_result_sign,
     Gate.mkDFF p2_a_is_inf clock reset p3_a_is_inf,
     Gate.mkDFF p2_b_is_inf clock reset p3_b_is_inf] ++
    mkDFFBank p2_big_exp p3_big_exp clock reset ++
    mkDFFBank s3_sum p3_sum clock reset ++
    mkDFFBank s3_lead_pos p3_lead_pos clock reset ++
    mkDFFBank p2_rm p3_rm clock reset ++
    mkDFFBank p2_tag p3_tag clock reset

  -- Stage 4: Normalize + Special values + Pack + Exceptions
  let stage4_inst : CircuitInstance := {
    moduleName := "FPAdder_Stage4_NormRound"
    instName := "u_stage4"
    portMap :=
      [("big_sign", p3_big_sign), ("eff_sub", p3_eff_sub)] ++
      ((List.range 8).map fun i => (s!"big_exp_{i}", p3_big_exp[i]!)) ++
      ((List.range 27).map fun i => (s!"sum_{i}", p3_sum[i]!)) ++
      ((List.range 5).map fun i => (s!"lead_pos_{i}", p3_lead_pos[i]!)) ++
      [("overflow", p3_overflow), ("found", p3_found),
       ("sticky", p3_sticky), ("any_nan", p3_any_nan), ("any_snan", p3_any_snan),
       ("any_special", p3_any_special), ("inf_sub_inf", p3_inf_sub_inf),
       ("inf_result_sign", p3_inf_result_sign),
       ("a_is_inf", p3_a_is_inf), ("b_is_inf", p3_b_is_inf)] ++
      ((List.range 3).map fun i => (s!"rm_{i}", p3_rm[i]!)) ++
      [("zero", zero)] ++
      ((List.range 32).map fun i => (s!"result_{i}", result[i]!)) ++
      ((List.range 5).map fun i => (s!"exc_{i}", exc[i]!))
  }

  let tag_gates := mkBUFBank p3_tag tag_out
  let p3_rm_zero0 := Wire.mk "p3_rm_z0"
  let p3_rm_zero1 := Wire.mk "p3_rm_z1"
  let p3_rm_zero2 := Wire.mk "p3_rm_z2"
  let not_p3_rm0 := Wire.mk "not_p3_rm0"
  let not_p3_rm1 := Wire.mk "not_p3_rm1"
  let not_p3_rm2 := Wire.mk "not_p3_rm2"
  let valid_v0 := Wire.mk "valid_v0"
  let valid_v1 := Wire.mk "valid_v1"
  let rm_absorb_gates := [
    Gate.mkNOT (p3_rm[0]!) not_p3_rm0,
    Gate.mkAND (p3_rm[0]!) not_p3_rm0 p3_rm_zero0,
    Gate.mkNOT (p3_rm[1]!) not_p3_rm1,
    Gate.mkAND (p3_rm[1]!) not_p3_rm1 p3_rm_zero1,
    Gate.mkNOT (p3_rm[2]!) not_p3_rm2,
    Gate.mkAND (p3_rm[2]!) not_p3_rm2 p3_rm_zero2,
    Gate.mkOR p3_valid p3_rm_zero0 valid_v0,
    Gate.mkOR p3_rm_zero1 p3_rm_zero2 valid_v1,
    Gate.mkOR valid_v0 valid_v1 valid_out
  ]

  let all_gates := p1_dffs ++ p2_dffs ++ p3_dffs ++ tag_gates ++ rm_absorb_gates

  { name := "FPAdder"
    inputs := src1 ++ src2 ++ [op_sub] ++ rm ++ dest_tag ++ [valid_in, clock, reset, zero]
    outputs := result ++ tag_out ++ exc ++ [valid_out]
    gates := all_gates
    instances := [stage1_inst, stage2_inst, stage3_inst, stage4_inst]
    signalGroups := [
      { name := "src1",     width := 32, wires := src1 },
      { name := "src2",     width := 32, wires := src2 },
      { name := "rm",       width := 3,  wires := rm },
      { name := "dest_tag", width := 6,  wires := dest_tag },
      { name := "result",   width := 32, wires := result },
      { name := "tag_out",  width := 6,  wires := tag_out },
      { name := "exc",      width := 5,  wires := exc }
    ] }

end Shoumei.Circuits.Sequential

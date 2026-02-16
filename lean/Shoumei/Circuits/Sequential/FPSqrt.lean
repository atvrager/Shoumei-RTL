/-
Circuits/Sequential/FPSqrt.lean - 24-cycle Iterative FP Square Root

An iterative floating-point square root unit for IEEE 754 binary32.
Takes a single source operand and produces the square root over 24 cycles.

Algorithm:
  Restoring square root of mantissa. On start, detects special cases
  (±0, +inf, negative, NaN), computes result exponent as (biased_exp+127)/2,
  and sets up the radicand in Q2.46 format (conditionally shifted based on
  exponent parity). Then 24 cycles of trial-subtract produce the root bits.
  On done, normalizes the root (left-shift + exp decrement if leading bit
  is 0) and packs the result.

  Key algorithm detail: trial = 4*root + 1 (not 2*root + 1).
  The radicand is stored in a 26-bit shift register (mant_q), with 2 bits
  consumed per cycle from the top.

State registers:
- src1_q[31:0]: Latched source operand (32 DFFs)
- rm_q[2:0]: Latched rounding mode (3 DFFs)
- tag_q[5:0]: Latched destination tag (6 DFFs)
- cnt_q[4:0]: 5-bit cycle counter 0..23 (5 DFFs)
- busy_q: Busy flag (1 DFF)
- exp_q[7:0]: Result exponent (8 DFFs)
- rem_q[25:0]: Remainder accumulator (26 DFFs)
- root_q[23:0]: Root accumulator (24 DFFs)
- mant_q[25:0]: Radicand shift register (26 DFFs)
- is_special_q: Special case flag (1 DFF)
- special_result_q[31:0]: Pre-computed special result (32 DFFs)
- special_exc_q[4:0]: Pre-computed special exceptions (5 DFFs)
Total: 32+3+6+5+1+8+26+24+26+1+32+5 = 169 DFFs

Interface:
- Inputs: src1[31:0], rm[2:0], dest_tag[5:0], start, clock, reset, zero, one
- Outputs: result[31:0], tag_out[5:0], exc[4:0], valid_out, busy
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.RippleCarryAdder

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Circuits.Combinational

/-- Build the 24-cycle iterative FP square root structural circuit. -/
def mkFPSqrt : Circuit :=
  -- ══════════════════════════════════════════════
  -- Input wires
  -- ══════════════════════════════════════════════
  let src1_in := makeIndexedWires "src1" 32
  let rm_in := makeIndexedWires "rm" 3
  let dest_tag := makeIndexedWires "dest_tag" 6
  let start := Wire.mk "start"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- ══════════════════════════════════════════════
  -- Output wires
  -- ══════════════════════════════════════════════
  let result := makeIndexedWires "result" 32
  let tag_out := makeIndexedWires "tag_out" 6
  let exc := makeIndexedWires "exc" 5
  let valid_out := Wire.mk "valid_out"
  let busy_out := Wire.mk "busy"

  -- ══════════════════════════════════════════════
  -- State register wires (DFF outputs = current state)
  -- ══════════════════════════════════════════════
  let src1_q := makeIndexedWires "src1_q" 32
  let rm_q := makeIndexedWires "rm_q" 3
  let tag_q := makeIndexedWires "tag_q" 6
  let cnt_q := makeIndexedWires "cnt_q" 5
  let busy_q := Wire.mk "busy_q"

  -- Sqrt datapath state
  let exp_q := makeIndexedWires "exp_q" 8
  let rem_q := makeIndexedWires "rem_q" 26
  let root_q := makeIndexedWires "root_q" 24
  let mant_q := makeIndexedWires "mant_q" 26  -- 26-bit shift register
  let is_special_q := Wire.mk "is_special_q"
  let special_result_q := makeIndexedWires "special_result_q" 32
  let special_exc_q := makeIndexedWires "special_exc_q" 5

  -- Next-state wires (DFF inputs)
  let src1_d := makeIndexedWires "src1_d" 32
  let rm_d := makeIndexedWires "rm_d" 3
  let tag_d := makeIndexedWires "tag_d" 6
  let cnt_d := makeIndexedWires "cnt_d" 5
  let busy_d := Wire.mk "busy_d"

  let exp_d := makeIndexedWires "exp_d" 8
  let rem_d := makeIndexedWires "rem_d" 26
  let root_d := makeIndexedWires "root_d" 24
  let mant_d := makeIndexedWires "mant_d" 26
  let is_special_d := Wire.mk "is_special_d"
  let special_result_d := makeIndexedWires "special_result_d" 32
  let special_exc_d := makeIndexedWires "special_exc_d" 5

  -- ══════════════════════════════════════════════
  -- Control signals
  -- ══════════════════════════════════════════════
  let not_busy := Wire.mk "not_busy"
  let start_new := Wire.mk "start_new"
  let cnt_is_23 := Wire.mk "cnt_is_23"
  let done := Wire.mk "done"
  let not_done := Wire.mk "not_done"
  let busy_and_not_done := Wire.mk "busy_and_not_done"
  let not_cnt3 := Wire.mk "not_cnt3"

  -- cnt_is_23: cnt_q[4:0] == 5'b10111 (23 decimal)
  let ctrl_gates := [
    Gate.mkNOT busy_q not_busy,
    Gate.mkAND start not_busy start_new,
    Gate.mkNOT (cnt_q[3]!) not_cnt3,
    Gate.mkAND (cnt_q[0]!) (cnt_q[1]!) (Wire.mk "cnt_01"),
    Gate.mkAND (cnt_q[2]!) not_cnt3 (Wire.mk "cnt_2n3"),
    Gate.mkAND (Wire.mk "cnt_01") (Wire.mk "cnt_2n3") (Wire.mk "cnt_0123"),
    Gate.mkAND (Wire.mk "cnt_0123") (cnt_q[4]!) cnt_is_23,
    Gate.mkAND busy_q cnt_is_23 done,
    Gate.mkNOT done not_done,
    Gate.mkAND busy_q not_done busy_and_not_done
  ]

  -- ══════════════════════════════════════════════
  -- Busy flag next state: busy_d = start_new OR busy_and_not_done
  -- ══════════════════════════════════════════════
  let busy_gates := [
    Gate.mkOR start_new busy_and_not_done busy_d
  ]

  -- ══════════════════════════════════════════════
  -- Counter increment logic (5-bit ripple)
  -- ══════════════════════════════════════════════
  let cnt_next := makeIndexedWires "cnt_next" 5
  let inc_carry := makeIndexedWires "inc_carry" 6

  let cnt_inc_gates :=
    [Gate.mkBUF one (inc_carry[0]!)] ++
    (List.range 5).flatMap (fun i =>
      [
        Gate.mkXOR (cnt_q[i]!) (inc_carry[i]!) (cnt_next[i]!),
        Gate.mkAND (cnt_q[i]!) (inc_carry[i]!) (inc_carry[i + 1]!)
      ]
    )

  -- ══════════════════════════════════════════════
  -- Counter next-state MUX:
  --   m1 = MUX(cnt_q, cnt_next, busy_and_not_done)
  --   cnt_d = MUX(m1, zero, start_new)
  -- ══════════════════════════════════════════════
  let cnt_m1 := makeIndexedWires "cnt_m1" 5
  let cnt_mux_gates := (List.range 5).flatMap (fun i => [
    Gate.mkMUX (cnt_q[i]!) (cnt_next[i]!) busy_and_not_done (cnt_m1[i]!),
    Gate.mkMUX (cnt_m1[i]!) zero start_new (cnt_d[i]!)
  ])

  -- ══════════════════════════════════════════════
  -- Latch logic: src1_d = MUX(src1_q, src1_in, start_new)
  -- ══════════════════════════════════════════════
  let src1_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (src1_q[i]!) (src1_in[i]!) start_new (src1_d[i]!)
  )

  -- rm_d = MUX(rm_q, rm_in, start_new)
  let rm_mux_gates := (List.range 3).map (fun i =>
    Gate.mkMUX (rm_q[i]!) (rm_in[i]!) start_new (rm_d[i]!)
  )

  -- tag_d = MUX(tag_q, dest_tag, start_new)
  let tag_mux_gates := (List.range 6).map (fun i =>
    Gate.mkMUX (tag_q[i]!) (dest_tag[i]!) start_new (tag_d[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Special case detection (combinational, on src1_in)
  -- ══════════════════════════════════════════════
  -- exp_all_ones: AND of src1_in[30:23]
  let exp_ao_01 := Wire.mk "exp_ao_01"
  let exp_ao_23 := Wire.mk "exp_ao_23"
  let exp_ao_45 := Wire.mk "exp_ao_45"
  let exp_ao_67 := Wire.mk "exp_ao_67"
  let exp_ao_0123 := Wire.mk "exp_ao_0123"
  let exp_ao_4567 := Wire.mk "exp_ao_4567"
  let exp_all_ones := Wire.mk "exp_all_ones"

  -- exp_all_zeros: NOR of src1_in[30:23]
  let exp_oz_01 := Wire.mk "exp_oz_01"
  let exp_oz_23 := Wire.mk "exp_oz_23"
  let exp_oz_45 := Wire.mk "exp_oz_45"
  let exp_oz_67 := Wire.mk "exp_oz_67"
  let exp_oz_0123 := Wire.mk "exp_oz_0123"
  let exp_oz_4567 := Wire.mk "exp_oz_4567"
  let exp_oz_all := Wire.mk "exp_oz_all"
  let exp_all_zeros := Wire.mk "exp_all_zeros"

  -- mant_any_set: OR tree of src1_in[22:0]
  let mant_or_l0 := (List.range 11).map fun i =>
    let o := Wire.mk s!"mant_or_l0_{i}"
    (Gate.mkOR (src1_in[2*i]!) (src1_in[2*i+1]!) o, o)
  let mant_or_l0_extra := Wire.mk "mant_or_l0_11"
  let mant_or_l0_extra_gate := Gate.mkBUF (src1_in[22]!) mant_or_l0_extra
  let ml0_outs := mant_or_l0.map Prod.snd ++ [mant_or_l0_extra] -- 12
  let mant_or_l1 := (List.range 6).map fun i =>
    let o := Wire.mk s!"mant_or_l1_{i}"
    (Gate.mkOR ml0_outs[2*i]! ml0_outs[2*i+1]! o, o)
  let ml1_outs := mant_or_l1.map Prod.snd -- 6
  let mant_or_l2 := (List.range 3).map fun i =>
    let o := Wire.mk s!"mant_or_l2_{i}"
    (Gate.mkOR ml1_outs[2*i]! ml1_outs[2*i+1]! o, o)
  let ml2_outs := mant_or_l2.map Prod.snd -- 3
  let mant_or_l3_0 := Wire.mk "mant_or_l3_0"
  let mant_any_set := Wire.mk "mant_any_set"

  let mant_or_tree :=
    mant_or_l0.map Prod.fst ++ [mant_or_l0_extra_gate] ++
    mant_or_l1.map Prod.fst ++
    mant_or_l2.map Prod.fst ++
    [Gate.mkOR ml2_outs[0]! ml2_outs[1]! mant_or_l3_0,
     Gate.mkOR mant_or_l3_0 ml2_outs[2]! mant_any_set]

  let exp_detect_gates := [
    -- exp_all_ones
    Gate.mkAND (src1_in[23]!) (src1_in[24]!) exp_ao_01,
    Gate.mkAND (src1_in[25]!) (src1_in[26]!) exp_ao_23,
    Gate.mkAND (src1_in[27]!) (src1_in[28]!) exp_ao_45,
    Gate.mkAND (src1_in[29]!) (src1_in[30]!) exp_ao_67,
    Gate.mkAND exp_ao_01 exp_ao_23 exp_ao_0123,
    Gate.mkAND exp_ao_45 exp_ao_67 exp_ao_4567,
    Gate.mkAND exp_ao_0123 exp_ao_4567 exp_all_ones,
    -- exp_all_zeros
    Gate.mkOR (src1_in[23]!) (src1_in[24]!) exp_oz_01,
    Gate.mkOR (src1_in[25]!) (src1_in[26]!) exp_oz_23,
    Gate.mkOR (src1_in[27]!) (src1_in[28]!) exp_oz_45,
    Gate.mkOR (src1_in[29]!) (src1_in[30]!) exp_oz_67,
    Gate.mkOR exp_oz_01 exp_oz_23 exp_oz_0123,
    Gate.mkOR exp_oz_45 exp_oz_67 exp_oz_4567,
    Gate.mkOR exp_oz_0123 exp_oz_4567 exp_oz_all,
    Gate.mkNOT exp_oz_all exp_all_zeros
  ]

  -- Derived special conditions
  let sign_bit := src1_in[31]!
  let not_sign := Wire.mk "not_sign"
  let is_zero := Wire.mk "is_zero"
  let not_mant := Wire.mk "not_mant"
  let is_inf := Wire.mk "is_inf"
  let is_nan := Wire.mk "is_nan"
  let is_snan := Wire.mk "is_snan"
  let not_mant22 := Wire.mk "not_mant22"
  let is_neg_nonzero := Wire.mk "is_neg_nonzero"
  let not_is_zero := Wire.mk "not_is_zero"
  let is_special := Wire.mk "is_special"
  let is_neg_or_snan := Wire.mk "is_neg_or_snan"

  let special_detect_gates := [
    Gate.mkNOT sign_bit not_sign,
    Gate.mkNOT mant_any_set not_mant,
    Gate.mkAND exp_all_zeros not_mant is_zero,
    Gate.mkNOT is_zero not_is_zero,
    Gate.mkAND exp_all_ones not_mant (Wire.mk "exp_ff_mant_0"),
    Gate.mkAND (Wire.mk "exp_ff_mant_0") not_sign is_inf,
    Gate.mkAND exp_all_ones mant_any_set is_nan,
    Gate.mkNOT (src1_in[22]!) not_mant22,
    Gate.mkAND is_nan not_mant22 is_snan,
    Gate.mkAND sign_bit not_is_zero is_neg_nonzero,
    Gate.mkOR is_neg_nonzero is_snan is_neg_or_snan,
    Gate.mkOR is_zero is_inf (Wire.mk "sp_01"),
    Gate.mkOR is_nan is_neg_nonzero (Wire.mk "sp_23"),
    Gate.mkOR (Wire.mk "sp_01") (Wire.mk "sp_23") is_special
  ]

  -- Special result MUX chain:
  --   base = src1 (handles ±0 and qNaN passthrough)
  --   m1 = MUX(base, +inf, is_inf)
  --   m2 = MUX(m1, src1, is_nan)  -- restore qNaN passthrough
  --   m3 = MUX(m2, qNaN, is_neg_or_snan)
  let sp_result_m1 := makeIndexedWires "sp_result_m1" 32
  let sp_result_m2 := makeIndexedWires "sp_result_m2" 32
  let sp_result := makeIndexedWires "sp_result" 32

  let sp_result_gates := (List.range 32).flatMap (fun i =>
    let inf_bit := if i >= 23 && i <= 30 then one else zero
    let qnan_bit := if (i >= 23 && i <= 30) || i == 22 then one else zero
    [
      Gate.mkMUX (src1_in[i]!) inf_bit is_inf (sp_result_m1[i]!),
      Gate.mkMUX (sp_result_m1[i]!) (src1_in[i]!) is_nan (sp_result_m2[i]!),
      Gate.mkMUX (sp_result_m2[i]!) qnan_bit is_neg_or_snan (sp_result[i]!)
    ]
  )

  let sp_exc := makeIndexedWires "sp_exc" 5
  let sp_exc_gates := [
    Gate.mkBUF is_neg_or_snan (sp_exc[4]!),
    Gate.mkBUF zero (sp_exc[3]!),
    Gate.mkBUF zero (sp_exc[2]!),
    Gate.mkBUF zero (sp_exc[1]!),
    Gate.mkBUF zero (sp_exc[0]!)
  ]

  -- ══════════════════════════════════════════════
  -- Exponent computation: result_exp = (biased_exp + 127) >> 1
  -- ══════════════════════════════════════════════
  let exp_sum := makeIndexedWires "exp_sum" 9
  let exp_add_carry := makeIndexedWires "exp_add_carry" 9
  let bias_bits : List Wire := (List.range 8).map (fun i =>
    if i < 7 then one else zero
  )

  let exp_add_gates :=
    [Gate.mkBUF zero (exp_add_carry[0]!)] ++
    (List.range 8).flatMap (fun i =>
      let a := src1_in[23 + i]!
      let b := bias_bits[i]!
      let ci := exp_add_carry[i]!
      let xab := Wire.mk s!"sqrt_exp_add_xab_{i}"
      let sum_bit := exp_sum[i]!
      let t0 := Wire.mk s!"sqrt_exp_add_t0_{i}"
      let t1 := Wire.mk s!"sqrt_exp_add_t1_{i}"
      let t2 := Wire.mk s!"sqrt_exp_add_t2_{i}"
      let t01 := Wire.mk s!"sqrt_exp_add_t01_{i}"
      let co := exp_add_carry[i + 1]!
      [
        Gate.mkXOR a b xab,
        Gate.mkXOR xab ci sum_bit,
        Gate.mkAND a b t0,
        Gate.mkAND a ci t1,
        Gate.mkAND b ci t2,
        Gate.mkOR t0 t1 t01,
        Gate.mkOR t01 t2 co
      ]
    ) ++
    [Gate.mkBUF (exp_add_carry[8]!) (exp_sum[8]!)]

  -- init_exp[7:0] = exp_sum[8:1] (right shift by 1)
  let init_exp := makeIndexedWires "init_exp" 8
  let init_exp_gates := (List.range 8).map (fun i =>
    Gate.mkBUF (exp_sum[i + 1]!) (init_exp[i]!)
  )

  -- exp_odd: unbiased exponent is odd when biased exp is even
  let exp_odd := Wire.mk "exp_odd"
  let exp_odd_gate := [Gate.mkNOT (src1_in[23]!) exp_odd]

  let exp_mux_gates := (List.range 8).map (fun i =>
    Gate.mkMUX (exp_q[i]!) (init_exp[i]!) start_new (exp_d[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Mantissa initialization (26-bit shift register in Q2.46 format)
  -- Even unbiased exp (exp_odd=0): mant_init = {0, 1, src[22:0], 0}  (26 bits)
  -- Odd unbiased exp (exp_odd=1):  mant_init = {1, src[22:0], 0, 0}  (26 bits)
  -- ══════════════════════════════════════════════
  let mant_init := makeIndexedWires "mant_init" 26
  let mant_init_gates := (List.range 26).map (fun i =>
    -- Even (exp_odd=0): {0, 1, src[22], src[21], ..., src[0], 0}
    --   bit 25 = 0, bit 24 = 1, bits 23..1 = src[22..0], bit 0 = 0
    let even_bit :=
      if i == 0 then zero
      else if i >= 1 && i <= 23 then src1_in[i - 1]!
      else if i == 24 then one
      else zero  -- i == 25
    -- Odd (exp_odd=1): {1, src[22], src[21], ..., src[0], 0, 0}
    --   bit 25 = 1, bits 24..2 = src[22..0], bits 1,0 = 0
    let odd_bit :=
      if i <= 1 then zero
      else if i >= 2 && i <= 24 then src1_in[i - 2]!
      else one  -- i == 25
    Gate.mkMUX even_bit odd_bit exp_odd (mant_init[i]!)
  )

  -- mant_d: three-level MUX
  -- Level 1: shift left by 2 when busy: mant_shifted[i] = mant_q[i-2] for i>=2, 0 for i<2
  -- Level 2: MUX(mant_q, mant_shifted, busy_q)
  -- Level 3: MUX(m2, mant_init, start_new)
  let mant_shifted := makeIndexedWires "mant_shifted" 26
  let mant_shift_gates := (List.range 26).map (fun i =>
    if i < 2 then Gate.mkBUF zero (mant_shifted[i]!)
    else Gate.mkBUF (mant_q[i - 2]!) (mant_shifted[i]!)
  )

  let mant_m1 := makeIndexedWires "mant_m1" 26
  let mant_mux_gates := (List.range 26).flatMap (fun i =>
    [
      Gate.mkMUX (mant_q[i]!) (mant_shifted[i]!) busy_q (mant_m1[i]!),
      Gate.mkMUX (mant_m1[i]!) (mant_init[i]!) start_new (mant_d[i]!)
    ]
  )

  -- ══════════════════════════════════════════════
  -- Special case register MUXes (load on start_new, hold otherwise)
  -- ══════════════════════════════════════════════
  let is_special_mux := [Gate.mkMUX is_special_q is_special start_new is_special_d]

  let sp_result_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (special_result_q[i]!) (sp_result[i]!) start_new (special_result_d[i]!)
  )

  let sp_exc_mux_gates := (List.range 5).map (fun i =>
    Gate.mkMUX (special_exc_q[i]!) (sp_exc[i]!) start_new (special_exc_d[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Radicand bit extraction: top 2 bits of mant_q
  -- ══════════════════════════════════════════════
  let rad_hi := Wire.mk "rad_hi"
  let rad_lo := Wire.mk "rad_lo"
  let rad_extract_gates := [
    Gate.mkBUF (mant_q[25]!) rad_hi,
    Gate.mkBUF (mant_q[24]!) rad_lo
  ]

  -- ══════════════════════════════════════════════
  -- Iterative sqrt step
  -- ══════════════════════════════════════════════

  -- rem_shifted[25:0] = {rem_q[23:0], rad_hi, rad_lo}
  let rem_shifted := makeIndexedWires "rem_shifted" 26
  let rem_shift_gates :=
    [Gate.mkBUF rad_lo (rem_shifted[0]!),
     Gate.mkBUF rad_hi (rem_shifted[1]!)] ++
    (List.range 24).map (fun i =>
      Gate.mkBUF (rem_q[i]!) (rem_shifted[i + 2]!)
    )

  -- trial[25:0] = {root_q[23:0], 0, 1}
  -- This represents 4*root + 1 in 26-bit format
  let trial_val := makeIndexedWires "trial_val" 26
  let trial_val_gates :=
    [Gate.mkBUF one (trial_val[0]!),
     Gate.mkBUF zero (trial_val[1]!)] ++
    (List.range 24).map (fun i =>
      Gate.mkBUF (root_q[i]!) (trial_val[i + 2]!)
    )

  -- 26-bit subtractor: diff = rem_shifted - trial_val
  let diff := makeIndexedWires "diff" 26
  let sub_borrow := makeIndexedWires "sqrt_sub_borrow" 27

  let sub_gates :=
    [Gate.mkBUF zero (sub_borrow[0]!)] ++
    (List.range 26).flatMap (fun i =>
      let a := rem_shifted[i]!
      let b := trial_val[i]!
      let bi := sub_borrow[i]!
      let xab := Wire.mk s!"sqrt_sub_xab_{i}"
      let diff_bit := diff[i]!
      let not_a := Wire.mk s!"sqrt_sub_na_{i}"
      let t0 := Wire.mk s!"sqrt_sub_t0_{i}"
      let t1 := Wire.mk s!"sqrt_sub_t1_{i}"
      let t2 := Wire.mk s!"sqrt_sub_t2_{i}"
      let t01 := Wire.mk s!"sqrt_sub_t01_{i}"
      let bo := sub_borrow[i + 1]!
      [
        Gate.mkXOR a b xab,
        Gate.mkXOR xab bi diff_bit,
        Gate.mkNOT a not_a,
        Gate.mkAND not_a b t0,
        Gate.mkAND not_a bi t1,
        Gate.mkAND b bi t2,
        Gate.mkOR t0 t1 t01,
        Gate.mkOR t01 t2 bo
      ]
    )

  -- accept = NOT borrow (rem_shifted >= trial)
  let accept := Wire.mk "accept"
  let accept_gate := [Gate.mkNOT (sub_borrow[26]!) accept]

  -- new_rem[i] = MUX(rem_shifted[i], diff[i], accept)
  let new_rem := makeIndexedWires "new_rem" 26
  let new_rem_gates := (List.range 26).map (fun i =>
    Gate.mkMUX (rem_shifted[i]!) (diff[i]!) accept (new_rem[i]!)
  )

  -- new_root: shift left and insert accept bit
  let new_root := makeIndexedWires "new_root" 24
  let new_root_gates :=
    [Gate.mkBUF accept (new_root[0]!)] ++
    (List.range 23).map (fun i =>
      Gate.mkBUF (root_q[i]!) (new_root[i + 1]!)
    )

  -- ══════════════════════════════════════════════
  -- Two-level next-state MUXes for rem and root
  -- ══════════════════════════════════════════════

  -- Remainder: init = 0 on start
  let rem_m1 := makeIndexedWires "rem_m1" 26
  let rem_mux_gates := (List.range 26).flatMap (fun i =>
    [
      Gate.mkMUX (rem_q[i]!) (new_rem[i]!) busy_q (rem_m1[i]!),
      Gate.mkMUX (rem_m1[i]!) zero start_new (rem_d[i]!)
    ]
  )

  -- Root: init = 0 on start
  let root_m1 := makeIndexedWires "root_m1" 24
  let root_mux_gates := (List.range 24).flatMap (fun i =>
    [
      Gate.mkMUX (root_q[i]!) (new_root[i]!) busy_q (root_m1[i]!),
      Gate.mkMUX (root_m1[i]!) zero start_new (root_d[i]!)
    ]
  )

  -- ══════════════════════════════════════════════
  -- DFF registers
  -- ══════════════════════════════════════════════
  let src1_dffs := (List.range 32).map (fun i =>
    Gate.mkDFF (src1_d[i]!) clock reset (src1_q[i]!)
  )
  let rm_dffs := (List.range 3).map (fun i =>
    Gate.mkDFF (rm_d[i]!) clock reset (rm_q[i]!)
  )
  let tag_dffs := (List.range 6).map (fun i =>
    Gate.mkDFF (tag_d[i]!) clock reset (tag_q[i]!)
  )
  let cnt_dffs := (List.range 5).map (fun i =>
    Gate.mkDFF (cnt_d[i]!) clock reset (cnt_q[i]!)
  )
  let busy_dff := [Gate.mkDFF busy_d clock reset busy_q]

  let exp_dffs := (List.range 8).map (fun i =>
    Gate.mkDFF (exp_d[i]!) clock reset (exp_q[i]!)
  )
  let rem_dffs := (List.range 26).map (fun i =>
    Gate.mkDFF (rem_d[i]!) clock reset (rem_q[i]!)
  )
  let root_dffs := (List.range 24).map (fun i =>
    Gate.mkDFF (root_d[i]!) clock reset (root_q[i]!)
  )
  let mant_dffs := (List.range 26).map (fun i =>
    Gate.mkDFF (mant_d[i]!) clock reset (mant_q[i]!)
  )
  let is_special_dff := [Gate.mkDFF is_special_d clock reset is_special_q]
  let sp_result_dffs := (List.range 32).map (fun i =>
    Gate.mkDFF (special_result_d[i]!) clock reset (special_result_q[i]!)
  )
  let sp_exc_dffs := (List.range 5).map (fun i =>
    Gate.mkDFF (special_exc_d[i]!) clock reset (special_exc_q[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Output bypass: on done cycle, use new_root/new_rem (combinational)
  -- instead of root_q/rem_q (one cycle stale)
  -- ══════════════════════════════════════════════
  let out_root := makeIndexedWires "out_root" 24
  let out_root_gates := (List.range 24).map (fun i =>
    Gate.mkMUX (root_q[i]!) (new_root[i]!) done (out_root[i]!)
  )

  let out_rem := makeIndexedWires "out_rem" 26
  let out_rem_gates := (List.range 26).map (fun i =>
    Gate.mkMUX (rem_q[i]!) (new_rem[i]!) done (out_rem[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Output normalization and packing
  -- ══════════════════════════════════════════════

  -- norm_needed = NOT out_root[23]
  let norm_needed := Wire.mk "norm_needed"
  let norm_gate := [Gate.mkNOT (out_root[23]!) norm_needed]

  -- Normalized mantissa: if norm_needed, shift left by 1
  let norm_mant := makeIndexedWires "norm_mant" 23
  let norm_mant_gates := (List.range 23).map (fun i =>
    let shifted := if i == 0 then zero else out_root[i - 1]!
    Gate.mkMUX (out_root[i]!) shifted norm_needed (norm_mant[i]!)
  )

  -- Normalized exponent: exp_q or exp_q - 1
  let dec_exp := makeIndexedWires "dec_exp" 8
  let dec_borrow := makeIndexedWires "dec_borrow" 8
  let dec_gates :=
    [
      Gate.mkNOT (exp_q[0]!) (dec_exp[0]!),
      Gate.mkNOT (exp_q[0]!) (dec_borrow[0]!)
    ] ++
    (List.range 7).flatMap (fun j =>
      let i := j + 1
      let not_exp := Wire.mk s!"sqrt_dec_nexp_{i}"
      [
        Gate.mkXOR (exp_q[i]!) (dec_borrow[i - 1]!) (dec_exp[i]!),
        Gate.mkNOT (exp_q[i]!) not_exp,
        Gate.mkAND not_exp (dec_borrow[i - 1]!) (dec_borrow[i]!)
      ]
    )

  let final_exp := makeIndexedWires "final_exp" 8
  let final_exp_gates := (List.range 8).map (fun i =>
    Gate.mkMUX (exp_q[i]!) (dec_exp[i]!) norm_needed (final_exp[i]!)
  )

  -- Normal result: {0, final_exp[7:0], norm_mant[22:0]}
  let normal_result := makeIndexedWires "normal_result" 32
  let normal_result_gates :=
    (List.range 23).map (fun i =>
      Gate.mkBUF (norm_mant[i]!) (normal_result[i]!)
    ) ++
    (List.range 8).map (fun i =>
      Gate.mkBUF (final_exp[i]!) (normal_result[23 + i]!)
    ) ++
    [Gate.mkBUF zero (normal_result[31]!)]

  -- Final result = MUX(normal_result, special_result_q, is_special_q)
  let result_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (normal_result[i]!) (special_result_q[i]!) is_special_q (result[i]!)
  )

  -- tag_out = BUF tag_q
  let tag_out_gates := (List.range 6).map (fun i =>
    Gate.mkBUF (tag_q[i]!) (tag_out[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Exception flags
  -- ══════════════════════════════════════════════
  -- NX: OR-tree over out_rem[25:0]
  let rem_or_l0 := (List.range 13).map fun i =>
    let o := Wire.mk s!"sqrt_rem_or_l0_{i}"
    (Gate.mkOR (out_rem[2*i]!) (out_rem[2*i+1]!) o, o)
  let rl0_outs := rem_or_l0.map Prod.snd -- 13
  let rem_or_l1 := (List.range 6).map fun i =>
    let o := Wire.mk s!"sqrt_rem_or_l1_{i}"
    (Gate.mkOR rl0_outs[2*i]! rl0_outs[2*i+1]! o, o)
  let rl0_extra := Wire.mk "sqrt_rem_or_l1_6"
  let rl0_extra_gate := Gate.mkBUF rl0_outs[12]! rl0_extra
  let rl1_outs := rem_or_l1.map Prod.snd ++ [rl0_extra] -- 7
  let rem_or_l2_0 := Wire.mk "sqrt_rem_or_l2_0"
  let rem_or_l2_1 := Wire.mk "sqrt_rem_or_l2_1"
  let rem_or_l2_2 := Wire.mk "sqrt_rem_or_l2_2"
  let rem_or_l3_0 := Wire.mk "sqrt_rem_or_l3_0"
  let rem_nonzero := Wire.mk "sqrt_rem_nonzero"
  let exc_or_tree :=
    rem_or_l0.map Prod.fst ++ rem_or_l1.map Prod.fst ++ [rl0_extra_gate] ++
    [Gate.mkOR rl1_outs[0]! rl1_outs[1]! rem_or_l2_0,
     Gate.mkOR rl1_outs[2]! rl1_outs[3]! rem_or_l2_1,
     Gate.mkOR rl1_outs[4]! rl1_outs[5]! rem_or_l2_2,
     Gate.mkOR rem_or_l2_0 rem_or_l2_1 rem_or_l3_0,
     Gate.mkOR rem_or_l3_0 rem_or_l2_2 rem_nonzero]

  let exc_gates := exc_or_tree ++ [
    Gate.mkMUX rem_nonzero (special_exc_q[0]!) is_special_q (exc[0]!),
    Gate.mkBUF zero (exc[1]!),
    Gate.mkBUF zero (exc[2]!),
    Gate.mkBUF zero (exc[3]!),
    Gate.mkMUX zero (special_exc_q[4]!) is_special_q (exc[4]!)
  ]

  -- valid_out = done
  let valid_gate := [Gate.mkBUF done valid_out]

  -- busy = BUF busy_q
  let busy_gate := [Gate.mkBUF busy_q busy_out]

  -- ══════════════════════════════════════════════
  -- Assemble all gates
  -- ══════════════════════════════════════════════
  let all_gates :=
    ctrl_gates ++
    busy_gates ++
    cnt_inc_gates ++
    cnt_mux_gates ++
    src1_mux_gates ++
    rm_mux_gates ++
    tag_mux_gates ++
    -- Special case detection
    mant_or_tree ++
    exp_detect_gates ++
    special_detect_gates ++
    sp_result_gates ++
    sp_exc_gates ++
    -- Exponent computation
    exp_add_gates ++
    init_exp_gates ++
    exp_odd_gate ++
    exp_mux_gates ++
    -- Mantissa initialization + shift register
    mant_init_gates ++
    mant_shift_gates ++
    mant_mux_gates ++
    -- Special case register MUXes
    is_special_mux ++
    sp_result_mux_gates ++
    sp_exc_mux_gates ++
    -- Radicand extraction
    rad_extract_gates ++
    -- Iterative sqrt step
    rem_shift_gates ++
    trial_val_gates ++
    sub_gates ++
    accept_gate ++
    new_rem_gates ++
    new_root_gates ++
    rem_mux_gates ++
    root_mux_gates ++
    -- DFFs
    src1_dffs ++
    rm_dffs ++
    tag_dffs ++
    cnt_dffs ++
    busy_dff ++
    exp_dffs ++
    rem_dffs ++
    root_dffs ++
    mant_dffs ++
    is_special_dff ++
    sp_result_dffs ++
    sp_exc_dffs ++
    -- Output bypass
    out_root_gates ++
    out_rem_gates ++
    -- Output normalization and packing
    norm_gate ++
    norm_mant_gates ++
    dec_gates ++
    final_exp_gates ++
    normal_result_gates ++
    result_gates ++
    tag_out_gates ++
    exc_gates ++
    valid_gate ++
    busy_gate

  { name := "FPSqrt"
    inputs := src1_in ++ rm_in ++ dest_tag ++ [start, clock, reset, zero, one]
    outputs := result ++ tag_out ++ exc ++ [valid_out, busy_out]
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "src1", width := 32, wires := src1_in },
      { name := "rm", width := 3, wires := rm_in },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 32, wires := result },
      { name := "tag_out", width := 6, wires := tag_out },
      { name := "exc", width := 5, wires := exc },
      { name := "cnt_q", width := 5, wires := cnt_q },
      { name := "exp_q", width := 8, wires := exp_q },
      { name := "rem_q", width := 26, wires := rem_q },
      { name := "root_q", width := 24, wires := root_q },
      { name := "mant_q", width := 26, wires := mant_q }
    ]
  }

/-- Convenience definition for the FP square root circuit. -/
def fpSqrtCircuit : Circuit := mkFPSqrt

end Shoumei.Circuits.Sequential

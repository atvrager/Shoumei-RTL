/-
Circuits/Sequential/FPFMA.lean - Fused single-precision multiply-add

result = ±(a*b) ± c, rounded once, in three cycles:

  stage 1  unpack a and b (a subnormal operand scaled up), 24 partial products,
           CSA tree, unpack and normalize c
  stage 2  48-bit final add -> the exact product; its leading-one position and
           exponent; align the product and c into a 52-bit window whose bit 50
           carries the anchor's leading one; add or subtract, borrowing one ulp
           when an effective subtraction lost bits below the window
  stage 3  leading-zero count, normalize, guard/round/sticky, one rounding at
           the normal or subnormal position, pack, flags

Chaining FPMultiplier into FPAdder rounded the product before the add, which
loses the low product bits that decide the result, and dropped the multiplier's
flags.  Neither survives here.

Geometry and every correction below are checked in verification/fma_reference.py,
which the same 30k finite and 30k all-class cases exercise against exact
arithmetic.

Inputs (111): src1[31:0], src2[31:0], src3[31:0], rm[2:0], dest_tag[5:0],
  negate_product, subtract_addend, valid_in, clock, reset, zero
Outputs (44): result[31:0], tag_out[5:0], exc[4:0], valid_out
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.KoggeStoneAdder
import Shoumei.Circuits.Combinational.Multiplier
import Shoumei.Circuits.Sequential.FPNormalize

set_option maxRecDepth 8000

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Circuits.Combinational

private def makeIndexedWires (pfx : String) (n : Nat) : List Wire :=
  (List.range n).map fun i => Wire.mk (pfx ++ "_" ++ toString i)

private def mkDFFBank (d_wires q_wires : List Wire) (clock reset : Wire) : List Gate :=
  List.zipWith (fun d q => Gate.mkDFF d clock reset q) d_wires q_wires

private def mkOrTree (pfx : String) (inputs : List Wire) : Wire × List Gate :=
  match inputs with
  | [] => (Wire.mk s!"{pfx}_gnd", [])
  | w0 :: rest =>
    let (last, gates) := rest.foldl (fun (acc, gs) w =>
      let o := Wire.mk s!"{pfx}_{gs.length}"
      (o, gs ++ [Gate.mkOR acc w o])) (w0, [])
    (last, gates)

private def mkAndTree (pfx : String) (inputs : List Wire) : Wire × List Gate :=
  match inputs with
  | [] => (Wire.mk s!"{pfx}_gnd", [])
  | w0 :: rest =>
    let (last, gates) := rest.foldl (fun (acc, gs) w =>
      let o := Wire.mk s!"{pfx}_{gs.length}"
      (o, gs ++ [Gate.mkAND acc w o])) (w0, [])
    (last, gates)

/-- Right shift with a sticky, saturating at the width: an amount at or past it
    leaves zero and sets the sticky.  The amount word may be wider than six
    bits; only the low six reach the barrel. -/
private def mkShiftRightSat (input : List Wire) (amount : List Wire) (width : Nat)
    (shiftBits : Nat) (one_wire zero_wire : Wire) (pfx : String) : List Wire × Wire × List Gate :=
  let output := makeIndexedWires s!"{pfx}_o" width
  let sticky := Wire.mk s!"{pfx}_stk"
  let padded := input ++ (List.range (width - input.length)).map fun _ => zero_wire
  let bar := makeIndexedWires s!"{pfx}_bar" width
  let bar_stk := Wire.mk s!"{pfx}_bstk"
  let amt := (List.range shiftBits).map fun i => Wire.mk s!"{pfx}_a{i}"
  let (any, any_gates) := mkOrTree s!"{pfx}_in" input
  let (over, over_gates) :=
    mkOrTree s!"{pfx}_hi" ((List.range (amount.length - shiftBits)).map fun i => amount[i +
      shiftBits]!)
  let gates :=
    over_gates ++ any_gates ++
    (List.range shiftBits).flatMap (fun i =>
      [Gate.mkMUX (amount[i]!) one_wire over (amt[i]!)]) ++
    mkShiftRightSticky padded amt bar bar_stk zero_wire s!"{pfx}_b" ++
    (List.range width).flatMap (fun i =>
      [Gate.mkMUX (bar[i]!) zero_wire over (output[i]!)]) ++
    [Gate.mkMUX bar_stk any over sticky]
  (output, sticky, gates)

/-- Left shift of a list into a wider field, zero filled above. -/
private def mkShiftLeftInto (input : List Wire) (amount : List Wire) (width : Nat)
    (zero_wire : Wire) (pfx : String) : List Wire × List Gate :=
  let output := makeIndexedWires s!"{pfx}_o" width
  let padded := input ++ (List.range (width - input.length)).map fun _ => zero_wire
  (output, mkBarrelShiftLeft padded amount output zero_wire s!"{pfx}_b")

/-- Build the fused multiply-add circuit for a format with `P` significand bits,
    `BIAS` and a `WEXP`-bit exponent field.  Every width below follows from
    those three: the window is `2P+4` wide with the anchor's leading one at
    `2P+2`, the addend significand at `2P+2-(P-1)`. -/
def mkFPFMAFusedP (nm : String) (P BIAS WEXP : Nat) : Circuit :=
  let FRAC := P - 1                     -- fraction bits
  let MSB := WEXP + FRAC                -- sign bit position
  let EFFW := WEXP + 3                  -- effective-exponent width
  let WINDOW := 2 * P + 4
  let ANCHOR := 2 * P + 2               -- window bit holding the anchor's one
  let SIG_LSB := ANCHOR - FRAC
  let SHB := Nat.log2 WINDOW + 1        -- barrel shift amount width
  let SLB := Nat.log2 SIG_LSB + 1
  let PPL := Nat.log2 FRAC + 1          -- leading-one width of the addend fraction
  let src1 := makeIndexedWires "src1" (MSB + 1)
  let src2 := makeIndexedWires "src2" (MSB + 1)
  let src3 := makeIndexedWires "src3" (MSB + 1)
  let rm := makeIndexedWires "rm" 3
  let dest_tag := makeIndexedWires "dest_tag" 6
  let negate_product := Wire.mk "negate_product"
  let subtract_addend := Wire.mk "subtract_addend"
  let valid_in := Wire.mk "valid_in"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"

  let result := makeIndexedWires "result" (MSB + 1)
  let tag_out := makeIndexedWires "tag_out" 6
  let exc := makeIndexedWires "exc" 5
  let valid_out := Wire.mk "valid_out"

  let one := Wire.mk "fma_one"
  -- bit pattern of a constant, least significant bit first
  let constOf (v n : Nat) : List Wire :=
    (List.range n).map fun i => if (v >>> i) &&& 1 == 1 then one else zero
  let one_gate := Gate.mkNOT zero one

  -- ══════════════════════════════════════════════════════════════════════
  -- Stage 1: unpack, partial products, CSA tree, addend normalization
  -- ══════════════════════════════════════════════════════════════════════
  let exp_a := (List.range WEXP).map fun i => src1[FRAC + i]!
  let exp_b := (List.range WEXP).map fun i => src2[FRAC + i]!
  let exp_c := (List.range WEXP).map fun i => src3[FRAC + i]!
  let frac_a := (List.range FRAC).map fun i => src1[i]!
  let frac_b := (List.range FRAC).map fun i => src2[i]!
  let frac_c := (List.range FRAC).map fun i => src3[i]!

  let (exp_a_any, exp_a_any_gates) := mkOrTree "fma_eaa" exp_a
  let (exp_b_any, exp_b_any_gates) := mkOrTree "fma_eba" exp_b
  let (exp_c_any, exp_c_any_gates) := mkOrTree "fma_eca" exp_c
  let (exp_a_all, exp_a_all_gates) := mkAndTree "fma_eao" exp_a
  let (exp_b_all, exp_b_all_gates) := mkAndTree "fma_ebo" exp_b
  let (exp_c_all, exp_c_all_gates) := mkAndTree "fma_eco" exp_c
  let (frac_a_any, frac_a_any_gates) := mkOrTree "fma_faa" frac_a
  let (frac_b_any, frac_b_any_gates) := mkOrTree "fma_fba" frac_b
  let (frac_c_any, frac_c_any_gates) := mkOrTree "fma_fca" frac_c

  let exp_a_zero := Wire.mk "fma_eaz"
  let exp_b_zero := Wire.mk "fma_ebz"
  let exp_c_zero := Wire.mk "fma_ecz"
  let frac_a_zero := Wire.mk "fma_faz"
  let frac_b_zero := Wire.mk "fma_fbz"
  let frac_c_zero := Wire.mk "fma_fcz"
  let not_quiet_a := Wire.mk "fma_nqa"
  let not_quiet_b := Wire.mk "fma_nqb"
  let not_quiet_c := Wire.mk "fma_nqc"
  let zero_det_gates := [
    Gate.mkNOT exp_a_any exp_a_zero, Gate.mkNOT exp_b_any exp_b_zero,
    Gate.mkNOT exp_c_any exp_c_zero, Gate.mkNOT frac_a_any frac_a_zero,
    Gate.mkNOT frac_b_any frac_b_zero, Gate.mkNOT frac_c_any frac_c_zero,
    Gate.mkNOT (frac_a[FRAC - 1]!) not_quiet_a, Gate.mkNOT (frac_b[FRAC - 1]!) not_quiet_b,
    Gate.mkNOT (frac_c[FRAC - 1]!) not_quiet_c
  ]

  let is_nan_a := Wire.mk "fma_na"
  let is_nan_b := Wire.mk "fma_nb"
  let is_nan_c := Wire.mk "fma_nc"
  let is_snan_a := Wire.mk "fma_sna"
  let is_snan_b := Wire.mk "fma_snb"
  let is_snan_c := Wire.mk "fma_snc"
  let is_inf_a := Wire.mk "fma_ia"
  let is_inf_b := Wire.mk "fma_ib"
  let is_inf_c := Wire.mk "fma_ic"
  let is_zero_a := Wire.mk "fma_za"
  let is_zero_b := Wire.mk "fma_zb"
  let is_zero_c := Wire.mk "fma_zc"
  let is_sub_a := Wire.mk "fma_sba"
  let is_sub_b := Wire.mk "fma_sbb"
  let is_sub_c := Wire.mk "fma_sbc"
  let prod_inf_raw := Wire.mk "fma_pir"
  let prod_zero_raw := Wire.mk "fma_pzr"
  let prod_inf := Wire.mk "fma_pinf"
  let prod_zero := Wire.mk "fma_pz"
  let inf_zero_a := Wire.mk "fma_iza"
  let inf_zero_b := Wire.mk "fma_izb"
  let inf_zero := Wire.mk "fma_iz"
  let fma_nab := Wire.mk "fma_nab"
  let fma_snab := Wire.mk "fma_snab"
  let not_nab := Wire.mk "fma_nnab"
  let not_iz := Wire.mk "fma_niz"
  let prod_valid := Wire.mk "fma_pval"
  let any_nan := Wire.mk "fma_anynan"
  let any_snan := Wire.mk "fma_anysnan"
  let class_gates := [
    Gate.mkAND exp_a_all frac_a_any is_nan_a,
    Gate.mkAND exp_b_all frac_b_any is_nan_b,
    Gate.mkAND exp_c_all frac_c_any is_nan_c,
    Gate.mkAND is_nan_a not_quiet_a is_snan_a,
    Gate.mkAND is_nan_b not_quiet_b is_snan_b,
    Gate.mkAND is_nan_c not_quiet_c is_snan_c,
    Gate.mkAND exp_a_all frac_a_zero is_inf_a,
    Gate.mkAND exp_b_all frac_b_zero is_inf_b,
    Gate.mkAND exp_c_all frac_c_zero is_inf_c,
    Gate.mkAND exp_a_zero frac_a_zero is_zero_a,
    Gate.mkAND exp_b_zero frac_b_zero is_zero_b,
    Gate.mkAND exp_c_zero frac_c_zero is_zero_c,
    Gate.mkAND exp_a_zero frac_a_any is_sub_a,
    Gate.mkAND exp_b_zero frac_b_any is_sub_b,
    Gate.mkAND exp_c_zero frac_c_any is_sub_c,
    Gate.mkAND is_inf_a is_zero_b inf_zero_a,
    Gate.mkAND is_zero_a is_inf_b inf_zero_b,
    Gate.mkOR inf_zero_a inf_zero_b inf_zero,
    Gate.mkOR is_nan_a is_nan_b fma_nab,
    Gate.mkOR fma_nab is_nan_c any_nan,
    Gate.mkOR is_snan_a is_snan_b fma_snab,
    Gate.mkOR fma_snab is_snan_c any_snan,
    Gate.mkNOT fma_nab not_nab,
    Gate.mkNOT inf_zero not_iz,
    Gate.mkAND not_nab not_iz prod_valid,
    Gate.mkOR is_inf_a is_inf_b prod_inf_raw,
    Gate.mkAND prod_inf_raw prod_valid prod_inf,
    Gate.mkOR is_zero_a is_zero_b prod_zero_raw,
    Gate.mkAND prod_zero_raw prod_valid prod_zero
  ]

  let eff_a := makeIndexedWires "fma_ea" WEXP
  let eff_b := makeIndexedWires "fma_eb" WEXP
  let eff_gates := (List.range WEXP).flatMap fun i =>
    let one_bit := if i == 0 then one else zero
    [Gate.mkMUX (exp_a[i]!) one_bit exp_a_zero (eff_a[i]!),
     Gate.mkMUX (exp_b[i]!) one_bit exp_b_zero (eff_b[i]!)]
  -- Mantissas with the implicit bit: 1 for a normal operand, 0 for a subnormal
  -- (whose exponent is then read as 1).  Same unpack as FPMultiplier.
  let mant_a := (List.range P).map fun i =>
    if i < FRAC then frac_a[i]! else exp_a_any
  let mant_b := (List.range P).map fun i =>
    if i < FRAC then frac_b[i]! else exp_b_any

  let pp_rows := (List.range P).map fun j =>
    let pp := makeIndexedWires s!"fma_pp{j}" (2 * P)
    (pp, (List.range (2 * P)).map fun i =>
      if i >= j && i < j + P then Gate.mkAND (mant_a[i - j]!) (mant_b[j]!) (pp[i]!)
      else Gate.mkBUF zero (pp[i]!))
  let pp_wires := pp_rows.map (·.1)
  let pp_gates := pp_rows.map (·.2) |>.flatten
  let (csa_sum, csa_carry, csa_gates, csa_instances) :=
    mkCSATreeHierarchical pp_wires zero (2 * P)

  -- addend significand, shifted up when subnormal so its leading one is at 23
  let pos_c := makeIndexedWires "fma_pc" PPL
  let (pos_c_w, lead_c_gates) := mkLeadPos "fma_lzc" frac_c zero PPL
  let pos_c_gates := (List.range PPL).map fun i => Gate.mkBUF (pos_c_w[i]!) (pos_c[i]!)
  let const23 := constOf FRAC SHB
  let pos_c_ext := (List.range SHB).map fun i => if i < PPL then pos_c[i]! else zero
  let sh_c := makeIndexedWires "fma_shc" SHB
  let (sh_c_gates, _sh_c_borrow) := mkKoggeStoneSub const23 pos_c_ext sh_c "fma_shcs" one
  let mant_c_norm := makeIndexedWires "fma_mcn" P
  let mant_c_norm_gates := mkBarrelShiftLeft (frac_c ++ [zero]) sh_c mant_c_norm zero "fma_bslc"
  let mant_c := makeIndexedWires "fma_mc" P
  let mant_c_gates := (List.range P).flatMap fun i =>
    let raw := if i == FRAC then one else frac_c[i]!
    let nz := Wire.mk s!"fma_mcnz{i}"
    [Gate.mkMUX raw (mant_c_norm[i]!) is_sub_c nz,
     Gate.mkMUX nz zero is_zero_c (mant_c[i]!)]

  -- addend exponent: the field, 1 - shift for a subnormal, or the minimum when
  -- the addend is zero, so a zero addend leaves the product as the anchor
  let one11 := constOf 1 EFFW
  let sh_c_11 := (List.range EFFW).map fun i => if i < SHB then sh_c[i]! else zero
  let eff_c_sub := makeIndexedWires "fma_ecs" EFFW
  let (eff_c_sub_gates, _eff_c_borrow) :=
    mkKoggeStoneSub one11 sh_c_11 eff_c_sub "fma_ecss" one
  let eff_c_m := makeIndexedWires "fma_ecm" EFFW
  let eff_c := makeIndexedWires "fma_ec" EFFW
  let eff_c_gates := (List.range EFFW).flatMap fun i =>
    let raw := if i < WEXP then exp_c[i]! else zero
    let mn := if i == WEXP + 2 then one else zero
    [Gate.mkMUX raw (eff_c_sub[i]!) is_sub_c (eff_c_m[i]!),
     Gate.mkMUX (eff_c_m[i]!) mn is_zero_c (eff_c[i]!)]

  let c_eff := makeIndexedWires "fma_ce" (MSB + 1)
  let c_eff_gates := (List.range (MSB + 1)).map fun i =>
    if i == MSB then Gate.mkXOR (src3[MSB]!) subtract_addend (c_eff[i]!)
    else Gate.mkBUF (src3[i]!) (c_eff[i]!)

  let prod_sign := Wire.mk "fma_ps"
  let c_sign := Wire.mk "fma_cs"
  let sign_gates := [
    Gate.mkXOR (src1[MSB]!) (src2[MSB]!) (Wire.mk "fma_ps0"),
    Gate.mkXOR (Wire.mk "fma_ps0") negate_product prod_sign,
    Gate.mkBUF (c_eff[MSB]!) c_sign
  ]

  let s1_csa_sum := makeIndexedWires "s1_cs" (2 * P)
  let s1_csa_carry := makeIndexedWires "s1_cc" (2 * P)
  let s1_eff_a := makeIndexedWires "s1_ea" WEXP
  let s1_eff_b := makeIndexedWires "s1_eb" WEXP
  let s1_mant_c := makeIndexedWires "s1_mc" P
  let s1_eff_c := makeIndexedWires "s1_ec" EFFW
  let s1_c_eff := makeIndexedWires "s1_ce" (MSB + 1)
  let s1_rm := makeIndexedWires "s1_rm" 3
  let s1_tag := makeIndexedWires "s1_tg" 6
  let s1_prod_sign := Wire.mk "s1_ps"
  let s1_c_sign := Wire.mk "s1_cs"
  let s1_any_nan := Wire.mk "s1_an"
  let s1_any_snan := Wire.mk "s1_as"
  let s1_prod_inf := Wire.mk "s1_pi"
  let s1_prod_zero := Wire.mk "s1_pz"
  let s1_inf_zero := Wire.mk "s1_iz"
  let s1_c_inf := Wire.mk "s1_ci"
  let s1_c_zero := Wire.mk "s1_cz"
  let s1_valid := Wire.mk "s1_v"
  let s1_gates :=
    [Gate.mkDFF prod_sign clock reset s1_prod_sign,
     Gate.mkDFF c_sign clock reset s1_c_sign,
     Gate.mkDFF any_nan clock reset s1_any_nan,
     Gate.mkDFF any_snan clock reset s1_any_snan,
     Gate.mkDFF prod_inf clock reset s1_prod_inf,
     Gate.mkDFF prod_zero clock reset s1_prod_zero,
     Gate.mkDFF inf_zero clock reset s1_inf_zero,
     Gate.mkDFF is_inf_c clock reset s1_c_inf,
     Gate.mkDFF is_zero_c clock reset s1_c_zero,
     Gate.mkDFF valid_in clock reset s1_valid] ++
    mkDFFBank csa_sum s1_csa_sum clock reset ++
    mkDFFBank csa_carry s1_csa_carry clock reset ++
    mkDFFBank eff_a s1_eff_a clock reset ++
    mkDFFBank eff_b s1_eff_b clock reset ++
    mkDFFBank mant_c s1_mant_c clock reset ++
    mkDFFBank eff_c s1_eff_c clock reset ++
    mkDFFBank c_eff s1_c_eff clock reset ++
    mkDFFBank rm s1_rm clock reset ++
    mkDFFBank dest_tag s1_tag clock reset

  -- ══════════════════════════════════════════════════════════════════════
  -- Stage 2: exact product, alignment into the window, add or subtract
  -- ══════════════════════════════════════════════════════════════════════
  let prod := makeIndexedWires "s2_p" (2 * P)
  let (prod_add_gates, _prod_carry) :=
    mkKoggeStoneAdd s1_csa_sum s1_csa_carry zero prod "s2_padd"
  let pos_p := makeIndexedWires "s2_pp" SHB
  let (pos_p_w, lead_p_gates) := mkLeadPos "s2_lzp" prod zero SHB
  let pos_p_gates := (List.range SHB).map fun i => Gate.mkBUF (pos_p_w[i]!) (pos_p[i]!)
  let const47 := constOf (2 * P - 1) SHB
  let s_h := makeIndexedWires "s2_sh" SHB
  let (s_h_gates, _s_h_borrow) := mkKoggeStoneSub const47 pos_p s_h "s2_shs" one
  let prod_n := makeIndexedWires "s2_pn" (2 * P)
  let prod_n_gates := mkBarrelShiftLeft prod s_h prod_n zero "s2_bslp"

  let eff_a_11 := (List.range EFFW).map fun i => if i < WEXP then s1_eff_a[i]! else zero
  let eff_b_11 := (List.range EFFW).map fun i => if i < WEXP then s1_eff_b[i]! else zero
  let exp_sum := makeIndexedWires "s2_es" EFFW
  let (exp_sum_gates, _es_carry) := mkKoggeStoneAdd eff_a_11 eff_b_11 zero exp_sum "s2_esa"
  let const126 := constOf (BIAS - 1) EFFW
  let exp_t1 := makeIndexedWires "s2_et1" EFFW
  let (exp_t1_gates, _et1_borrow) := mkKoggeStoneSub exp_sum const126 exp_t1 "s2_et1s" one
  let s_h_11 := (List.range EFFW).map fun i => if i < SHB then s_h[i]! else zero
  let exp_p := makeIndexedWires "s2_ep" EFFW
  let (exp_p_gates, _ep_borrow) := mkKoggeStoneSub exp_t1 s_h_11 exp_p "s2_eps" one

  let diff := makeIndexedWires "s2_d" EFFW
  let (diff_gates, diff_borrow) := mkKoggeStoneSub exp_p s1_eff_c diff "s2_ds" one
  -- Ep and Ec are signed: a subnormal or zero addend has a negative effective
  -- exponent, so the anchor is chosen by a signed comparison, not the borrow
  let c_big := Wire.mk "s2_cbig"
  let c_big_gate := [
    Gate.mkBUF (exp_p[EFFW - 1]!) (Wire.mk "s2_epsign"),
    Gate.mkBUF (s1_eff_c[EFFW - 1]!) (Wire.mk "s2_ecsign"),
    Gate.mkNOT (Wire.mk "s2_ecsign") (Wire.mk "s2_necpos"),
    Gate.mkAND (Wire.mk "s2_epsign") (Wire.mk "s2_necpos") (Wire.mk "s2_cbig1"),
    Gate.mkXOR (Wire.mk "s2_epsign") (Wire.mk "s2_ecsign") (Wire.mk "s2_sdiff0"),
    Gate.mkNOT (Wire.mk "s2_sdiff0") (Wire.mk "s2_same0"),
    Gate.mkAND (Wire.mk "s2_same0") diff_borrow (Wire.mk "s2_cbig2"),
    Gate.mkOR (Wire.mk "s2_cbig1") (Wire.mk "s2_cbig2") c_big
  ]

  -- the product sits at the top of the window; the addend starts at SIG_LSB;
  -- whichever is not the anchor shifts down by the exponent gap
  let diff_low6 := (List.range SHB).map fun i => diff[i]!
  let const3_6 := constOf (ANCHOR - (2 * P - 1)) SHB
  let p_up_amt := makeIndexedWires "s2_pua" SHB
  let (p_up_amt_gates, _pua_carry) := mkKoggeStoneAdd const3_6 diff_low6 zero p_up_amt "s2_puaa"
  let p_left_amt := makeIndexedWires "s2_pla" SHB
  let p_left_amt_gates := (List.range SHB).map fun i =>
    Gate.mkMUX (const3_6[i]!) (p_up_amt[i]!) c_big (p_left_amt[i]!)
  let p_down_amt := makeIndexedWires "s2_pda" EFFW
  -- The addend is anchored with its leading one at window bit ANCHOR, so the
  -- product's leading one belongs at ANCHOR - (Ec - Ep).  It starts at bit
  -- 2P-1, so the shift is (ANCHOR - (2P-1)) + diff to the left, and the
  -- negation of that to the right.  Computing (2P-1 - ANCHOR) - diff gets the
  -- sign of the constant wrong and lands the product six bits low whenever the
  -- addend outweighs the product.
  let const3_e := constOf (ANCHOR - (2 * P - 1)) EFFW
  let p_up_amt_e := makeIndexedWires "s2_puae" EFFW
  let (p_up_amt_e_gates, _puae_carry) :=
    mkKoggeStoneAdd const3_e diff zero p_up_amt_e "s2_puaea"
  let (p_down_amt_gates, _pda_borrow) :=
    mkKoggeStoneSub (constOf 0 EFFW) p_up_amt_e p_down_amt "s2_pdas" one
  let c_left_amt := makeIndexedWires "s2_cla" SHB
  let const27_6 := constOf SIG_LSB SHB
  let (c_left_amt_gates, _cla_borrow) := mkKoggeStoneSub const27_6 diff_low6 c_left_amt "s2_clas"
    one
  let c_up_amt := makeIndexedWires "s2_cua" SHB
  let c_up_amt_gates := (List.range SHB).map fun i =>
    Gate.mkMUX (c_left_amt[i]!) (const27_6[i]!) c_big (c_up_amt[i]!)
  let c_down_amt := makeIndexedWires "s2_cda" EFFW
  let (c_down_amt_gates, _cda_borrow) :=
    mkKoggeStoneSub diff (const27_6 ++ (List.range (EFFW - SHB)).map (fun _ => zero)) c_down_amt
      "s2_cdas" one

  let (p_up, p_up_gates) := mkShiftLeftInto prod_n const3_6 WINDOW zero "s2_pup"
  let (p_left, p_left_gates) := mkShiftLeftInto prod_n p_left_amt WINDOW zero "s2_pl"
  let (p_down, p_down_stk, p_down_gates) := mkShiftRightSat prod_n p_down_amt WINDOW SHB one zero
    "s2_pdn"
  let (p_down_any, p_down_any_gates) := mkOrTree "s2_pdany" p_down_amt
  let p_dir := Wire.mk "s2_pdir"
  let p_dir_gate := [
    Gate.mkNOT (p_down_amt[EFFW - 1]!) (Wire.mk "s2_pdpos"),
    Gate.mkAND (Wire.mk "s2_pdpos") p_down_any (Wire.mk "s2_pdp1"),
    Gate.mkAND c_big (Wire.mk "s2_pdp1") p_dir
  ]
  let q_win := makeIndexedWires "s2_qw" WINDOW
  let q_win_gates := (List.range WINDOW).map fun i =>
    Gate.mkMUX (p_up[i]!) (Wire.mk s!"s2_pq{i}") c_big (q_win[i]!)
  let q_win_gates' := (List.range WINDOW).map fun i =>
    Gate.mkMUX (p_left[i]!) (p_down[i]!) p_dir (Wire.mk s!"s2_pq{i}")

  let (c_up, c_up_gates) := mkShiftLeftInto s1_mant_c const27_6 WINDOW zero "s2_cup"
  let (c_left, c_left_gates) := mkShiftLeftInto s1_mant_c c_left_amt WINDOW zero "s2_cl"
  let (c_down, c_down_stk, c_down_gates) := mkShiftRightSat s1_mant_c c_down_amt WINDOW SHB one zero
    "s2_cdn"
  let (c_down_any, c_down_any_gates) := mkOrTree "s2_cdany" c_down_amt
  let c_dir := Wire.mk "s2_cdir"
  let c_dir_gate := [
    Gate.mkNOT c_big (Wire.mk "s2_ncbig"),
    -- EFFW - 1, not a literal: the effective-exponent width follows WEXP, so a
    -- literal is only the sign bit at one precision.  A literal 10 here is
    -- correct for the single-precision build and wrong for double.
    Gate.mkNOT (c_down_amt[EFFW - 1]!) (Wire.mk "s2_cdpos"),
    Gate.mkAND (Wire.mk "s2_ncbig") (Wire.mk "s2_cdpos") (Wire.mk "s2_cdp1"),
    Gate.mkAND (Wire.mk "s2_cdp1") c_down_any c_dir
  ]
  let c_win := makeIndexedWires "s2_cw" WINDOW
  let c_win_gates := (List.range WINDOW).map fun i =>
    Gate.mkMUX (Wire.mk s!"s2_cc{i}") (c_up[i]!) c_big (c_win[i]!)
  let c_win_gates' := (List.range WINDOW).map fun i =>
    Gate.mkMUX (c_left[i]!) (c_down[i]!) c_dir (Wire.mk s!"s2_cc{i}")
  -- only a right shift loses bits, and only one operand ever shifts right
  let stk := Wire.mk "s2_stk"
  let stk_gates := [
    Gate.mkMUX zero c_down_stk c_dir (Wire.mk "s2_stkc"),
    Gate.mkMUX (Wire.mk "s2_stkc") p_down_stk p_dir stk
  ]

  let same := Wire.mk "s2_same"
  let not_same := Wire.mk "s2_nsame"
  let same_gate := [
    Gate.mkXOR s1_prod_sign s1_c_sign (Wire.mk "s2_xs"),
    Gate.mkNOT (Wire.mk "s2_xs") same,
    Gate.mkNOT same not_same
  ]

  let sum_win := makeIndexedWires "s2_sw" WINDOW
  let (sum_win_gates, _sw_carry) := mkKoggeStoneAdd q_win c_win zero sum_win "s2_swa"
  let diff_qc := makeIndexedWires "s2_dqc" WINDOW
  let (diff_qc_gates, dqc_borrow) := mkKoggeStoneSub q_win c_win diff_qc "s2_dqcs" one
  let diff_cq := makeIndexedWires "s2_dcq" WINDOW
  let (diff_cq_gates, _dcq_borrow) := mkKoggeStoneSub c_win q_win diff_cq "s2_dcqs" one
  let mag := makeIndexedWires "s2_mag" WINDOW
  let mag_gates := (List.range WINDOW).map fun i =>
    Gate.mkMUX (diff_qc[i]!) (diff_cq[i]!) dqc_borrow (mag[i]!)
  let res_sign := Wire.mk "s2_rs"
  let res_sign_gate := [Gate.mkMUX s1_prod_sign s1_c_sign dqc_borrow res_sign]

  -- An effective subtraction whose subtrahend lost bits below the window must borrow
  -- one unit from bit 0: the exact difference is (A - B - 1) + (1 - epsilon).
  let ulp_borrow_ok := Wire.mk "s2_ubok"
  let ulp_borrow_gates := [
    Gate.mkAND not_same stk ulp_borrow_ok
  ]
  let mag_c := makeIndexedWires "s2_magc" WINDOW
  let minus_one := (List.range WINDOW).map fun i => if i == 0 then one else zero
  let (mag_c_gates, _mag_c_borrow) := mkKoggeStoneSub mag minus_one mag_c "s2_magcs" one
  let small_win_gates : List Gate := []
  let mag_sel := makeIndexedWires "s2_magsel" WINDOW
  let mag_sel_gates := (List.range WINDOW).map fun i =>
    Gate.mkMUX (mag[i]!) (mag_c[i]!) ulp_borrow_ok (mag_sel[i]!)
  let win := makeIndexedWires "s2_w" WINDOW
  let win_gates := (List.range WINDOW).map fun i =>
    Gate.mkMUX (mag_sel[i]!) (sum_win[i]!) same (win[i]!)

  let e_hi := makeIndexedWires "s2_eh" EFFW
  let e_hi_gates := (List.range EFFW).map fun i =>
    Gate.mkMUX (exp_p[i]!) (s1_eff_c[i]!) c_big (e_hi[i]!)

  let s2_win := makeIndexedWires "s2r_w" WINDOW
  let s2_stk := Wire.mk "s2r_stk"
  let s2_sign := Wire.mk "s2r_rs"
  let s2_e_hi := makeIndexedWires "s2r_eh" EFFW
  let s2_c_eff := makeIndexedWires "s2r_ce" (MSB + 1)
  let s2_rm := makeIndexedWires "s2r_rm" 3
  let s2_tag := makeIndexedWires "s2r_tg" 6
  let s2_any_nan := Wire.mk "s2r_an"
  let s2_any_snan := Wire.mk "s2r_as"
  let s2_prod_inf := Wire.mk "s2r_pi"
  let s2_prod_zero := Wire.mk "s2r_pz"
  let s2_inf_zero := Wire.mk "s2r_iz"
  let s2_c_inf := Wire.mk "s2r_ci"
  let s2_c_zero := Wire.mk "s2r_cz"
  let s2_prod_sign := Wire.mk "s2r_ps"
  let s2_c_sign := Wire.mk "s2r_cs"
  let s2_valid := Wire.mk "s2r_v"
  let s2_gates :=
    [Gate.mkDFF res_sign clock reset s2_sign,
     Gate.mkDFF stk clock reset s2_stk,
     Gate.mkDFF s1_any_nan clock reset s2_any_nan,
     Gate.mkDFF s1_any_snan clock reset s2_any_snan,
     Gate.mkDFF s1_prod_inf clock reset s2_prod_inf,
     Gate.mkDFF s1_prod_zero clock reset s2_prod_zero,
     Gate.mkDFF s1_inf_zero clock reset s2_inf_zero,
     Gate.mkDFF s1_c_inf clock reset s2_c_inf,
     Gate.mkDFF s1_c_zero clock reset s2_c_zero,
     Gate.mkDFF s1_prod_sign clock reset s2_prod_sign,
     Gate.mkDFF s1_c_sign clock reset s2_c_sign,
     Gate.mkDFF s1_valid clock reset s2_valid] ++
    mkDFFBank win s2_win clock reset ++
    mkDFFBank e_hi s2_e_hi clock reset ++
    mkDFFBank s1_c_eff s2_c_eff clock reset ++
    mkDFFBank s1_rm s2_rm clock reset ++
    mkDFFBank s1_tag s2_tag clock reset

  -- ══════════════════════════════════════════════════════════════════════
  -- Stage 3: normalize, round once, pack, flags
  -- ══════════════════════════════════════════════════════════════════════
  let (win_any, win_any_gates) := mkOrTree "s3_wany" s2_win
  let pos_v := makeIndexedWires "s3_pv" SHB
  let (pos_v_w, lead_v_gates) := mkLeadPos "s3_lzv" s2_win zero SHB
  let pos_v_gates := (List.range SHB).map fun i => Gate.mkBUF (pos_v_w[i]!) (pos_v[i]!)
  let const50 := constOf ANCHOR SHB
  let sh_v := makeIndexedWires "s3_sh" SHB
  let (sh_v_gates, sh_v_borrow) := mkKoggeStoneSub const50 pos_v sh_v "s3_shs" one
  let n_up := makeIndexedWires "s3_nu" WINDOW
  let n_up_gates := mkBarrelShiftLeft s2_win sh_v n_up zero "s3_bslu"
  let one_6 := (List.range SHB).map fun i => if i == 0 then one else zero
  let n_dn := makeIndexedWires "s3_nd" WINDOW
  let n_dn_stk := Wire.mk "s3_ndstk"
  let n_dn_gates := mkShiftRightSticky s2_win one_6 n_dn n_dn_stk zero "s3_bsld"
  let n := makeIndexedWires "s3_n" WINDOW
  let n_gates := (List.range WINDOW).map fun i =>
    Gate.mkMUX (n_up[i]!) (n_dn[i]!) sh_v_borrow (n[i]!)
  let extra := Wire.mk "s3_extra"
  let extra_gate := [Gate.mkAND sh_v_borrow (s2_win[0]!) extra]

  -- Extend sh_v with the borrow bit: const50 - pos_v is positive except when pos_v = ANCHOR + 1.
  let sh_v_11 := (List.range EFFW).map fun i => if i < SHB then sh_v[i]! else sh_v_borrow
  let e_res := makeIndexedWires "s3_e" EFFW
  let (e_res_gates, _e_res_borrow) := mkKoggeStoneSub s2_e_hi sh_v_11 e_res "s3_es" one

  let sig := (List.range P).map fun i => n[SIG_LSB + i]!
  let (st_lo, st_lo_gates) := mkOrTree "s3_stlo" ((List.range (SIG_LSB - 2)).map fun i => n[i]!)
  let st := Wire.mk "s3_st"
  let st_gates := [
    Gate.mkOR st_lo s2_stk (Wire.mk "s3_st1"),
    Gate.mkOR (Wire.mk "s3_st1") extra st
  ]

  let m_bits := makeIndexedWires "s3_m" (P + 3)
  let m_gates :=
    (List.range P).map (fun i => Gate.mkBUF (sig[i]!) (m_bits[i + 3]!)) ++
    [Gate.mkBUF n[SIG_LSB - 1]! (m_bits[2]!), Gate.mkBUF n[SIG_LSB - 2]! (m_bits[1]!),
     Gate.mkBUF st (m_bits[0]!)]

  -- rounding shift: 3 when the result is normal, 4 - E when subnormal, clamped
  -- at 27 (everything out)
  let (e_any, e_any_gates) := mkOrTree "s3_eany" e_res
  let e_ge1 := Wire.mk "s3_ege1"
  let not_e_pos := Wire.mk "s3_nepos"
  let e_ge1_gate := [
    Gate.mkNOT (e_res[EFFW - 1]!) not_e_pos,
    Gate.mkAND not_e_pos e_any e_ge1
  ]
  let four11 := constOf 4 EFFW
  let four_minus_e := makeIndexedWires "s3_4me" EFFW
  let (four_minus_e_gates, _4me_borrow) :=
    mkKoggeStoneSub four11 e_res four_minus_e "s3_4mes" one
  let const27_11 := constOf SIG_LSB EFFW
  let clamp_d := makeIndexedWires "s3_cld" EFFW
  let (clamp_d_gates, clamp_borrow) :=
    mkKoggeStoneSub four_minus_e const27_11 clamp_d "s3_clds" one
  -- the clamp applies only on the subnormal branch: there 4 - E can exceed the
  -- field and the mantissa is shifted clear
  let clamp := Wire.mk "s3_clamp"
  let clamp_gate := [
    Gate.mkNOT e_ge1 (Wire.mk "s3_nge1"),
    Gate.mkNOT clamp_borrow (Wire.mk "s3_ncb"),
    Gate.mkAND (Wire.mk "s3_nge1") (Wire.mk "s3_ncb") clamp
  ]
  let shd := makeIndexedWires "s3_shd" SLB
  let shd_clamp := constOf SIG_LSB SLB
  let shd_gates := (List.range SLB).flatMap fun i =>
    [Gate.mkMUX (four_minus_e[i]!) (if i == 0 || i == 1 then one else zero) e_ge1
       (Wire.mk s!"s3_shdm{i}"),
     Gate.mkMUX (Wire.mk s!"s3_shdm{i}") (shd_clamp[i]!) clamp (shd[i]!)]
  let mant := makeIndexedWires "s3_mant" (P + 3)
  let mant_stk := Wire.mk "s3_mantstk"
  let shd6 := (List.range SHB).map fun i => if i < SLB then shd[i]! else zero
  let mant_gates := mkShiftRightSticky m_bits shd6 mant mant_stk zero "s3_bshm"
  let ml_amt := makeIndexedWires "s3_mla" SLB
  let const27_5 := constOf SIG_LSB SLB
  let (ml_amt_gates, _ml_borrow) := mkKoggeStoneSub const27_5 shd ml_amt "s3_mlas" one
  let ml := makeIndexedWires "s3_ml" (P + 3)
  let ml_amt6 := (List.range SHB).map fun i => if i < SLB then ml_amt[i]! else zero
  let ml_gates := mkBarrelShiftLeft m_bits ml_amt6 ml zero "s3_bslml"
  let (st2_raw, st2_raw_gates) := mkOrTree "s3_st2r" ((List.range (P + 2)).map fun i => ml[i]!)
  let any_unrounded := Wire.mk "s3_any_unrounded"
  let any_unrounded_gate := [Gate.mkOR win_any s2_stk any_unrounded]
  let (clamp_d_any, clamp_d_any_gates) := mkOrTree "s3_cldany" clamp_d
  let past_round := Wire.mk "s3_past_round"
  let past_round_gates := [
    Gate.mkAND clamp clamp_d_any past_round
  ]
  let rnd_bit := Wire.mk "s3_rndbit"
  let rnd_bit_gate := [
    Gate.mkMUX (ml[P + 2]!) zero past_round rnd_bit
  ]
  let st2 := Wire.mk "s3_st2"
  let st2_gate := [
    Gate.mkMUX st2_raw any_unrounded past_round st2
  ]
  let rem_any := Wire.mk "s3_remany"
  let rem_any_gate := [Gate.mkOR rnd_bit st2 rem_any]

  -- rounding modes: 000 RNE, 001 RTZ, 010 RDN, 011 RUP, 100 RMM
  let rne := Wire.mk "s3_rne"
  let rdn := Wire.mk "s3_rdn"
  let rup := Wire.mk "s3_rup"
  let rmm := Wire.mk "s2_rmm"
  let ovf_to_inf := Wire.mk "s3_ovfinf"
  let not_ovf_to_inf := Wire.mk "s3_novfinf"
  let rm_decode_gates := [
    Gate.mkNOT (s2_rm[0]!) (Wire.mk "s3_nr0"),
    Gate.mkNOT (s2_rm[1]!) (Wire.mk "s3_nr1"),
    Gate.mkNOT (s2_rm[2]!) (Wire.mk "s3_nr2"),
    Gate.mkAND (Wire.mk "s3_nr0") (Wire.mk "s3_nr1") (Wire.mk "s3_nr01"),
    Gate.mkAND (Wire.mk "s3_nr01") (Wire.mk "s3_nr2") rne,
    Gate.mkAND (Wire.mk "s3_nr0") (s2_rm[1]!) (Wire.mk "s3_r1"),
    Gate.mkAND (Wire.mk "s3_r1") (Wire.mk "s3_nr2") rdn,
    Gate.mkAND (s2_rm[0]!) (s2_rm[1]!) (Wire.mk "s3_r01"),
    Gate.mkAND (Wire.mk "s3_r01") (Wire.mk "s3_nr2") rup,
    Gate.mkAND (Wire.mk "s3_nr01") (s2_rm[2]!) rmm
  ]
  let not_sign := Wire.mk "s3_ns"
  let rne_up := Wire.mk "s3_rneup"
  let rdn_up := Wire.mk "s3_rdnup"
  let rup_up := Wire.mk "s3_rupup"
  let up := Wire.mk "s3_up"
  let up_gates := [
    Gate.mkNOT s2_sign not_sign,
    Gate.mkOR st2 (mant[0]!) (Wire.mk "s3_stlsb"),
    Gate.mkAND rnd_bit (Wire.mk "s3_stlsb") rne_up,
    Gate.mkAND rem_any s2_sign rdn_up,
    Gate.mkAND rem_any not_sign rup_up,
    Gate.mkAND rne rne_up (Wire.mk "s3_u0"),
    Gate.mkAND rdn rdn_up (Wire.mk "s3_u1"),
    Gate.mkAND rup rup_up (Wire.mk "s3_u2"),
    Gate.mkAND rmm rnd_bit (Wire.mk "s3_u3"),
    Gate.mkOR (Wire.mk "s3_u0") (Wire.mk "s3_u1") (Wire.mk "s3_u01"),
    Gate.mkOR (Wire.mk "s3_u01") (Wire.mk "s3_u2") (Wire.mk "s3_u012"),
    Gate.mkOR (Wire.mk "s3_u012") (Wire.mk "s3_u3") up,
    -- IEEE 754 section 7.4: overflow gives an infinity only when the rounding
    -- direction points away from zero for this sign.  Toward zero is rtz
    -- always, rdn for a positive sum and rup for a negative sum; round to
    -- nearest counts as away.  The other modes give the largest finite value.
    Gate.mkOR rne rdn (Wire.mk "s3_rm_ab"),
    Gate.mkOR (Wire.mk "s3_rm_ab") rup (Wire.mk "s3_rm_abc"),
    Gate.mkOR (Wire.mk "s3_rm_abc") rmm (Wire.mk "s3_rm_any"),
    Gate.mkNOT (Wire.mk "s3_rm_any") (Wire.mk "s3_tz_rtz"),
    Gate.mkAND rdn not_sign (Wire.mk "s3_tz_rdn"),
    Gate.mkAND rup s2_sign (Wire.mk "s3_tz_rup"),
    Gate.mkOR (Wire.mk "s3_tz_rtz") (Wire.mk "s3_tz_rdn") (Wire.mk "s3_tz_a"),
    Gate.mkOR (Wire.mk "s3_tz_a") (Wire.mk "s3_tz_rup") not_ovf_to_inf,
    Gate.mkNOT not_ovf_to_inf ovf_to_inf
  ]
  let mant_inc := makeIndexedWires "s3_mi" (P + 3)
  let up_ext := (List.range (P + 3)).map fun i => if i == 0 then up else zero
  let (mant_inc_gates, _mi_carry) := mkKoggeStoneAdd mant up_ext zero mant_inc "s3_mia"

  -- pack: normal when E >= 1, subnormal otherwise, both after the rounding carry
  let carry_out := mant_inc[P]!
  let e_inc := makeIndexedWires "s3_einc" EFFW
  let (e_inc_gates, _einc_carry) :=
    mkKoggeStoneAdd e_res one11 zero e_inc "s3_einca"
  let e_final := makeIndexedWires "s3_ef" EFFW
  let e_final_gates := (List.range EFFW).map fun i =>
    Gate.mkMUX (e_res[i]!) (e_inc[i]!) carry_out (e_final[i]!)
  let sig_final := makeIndexedWires "s3_sf" P
  let sig_final_gates := (List.range P).map fun i =>
    Gate.mkMUX (mant_inc[i]!) (mant_inc[i + 1]!) carry_out (sig_final[i]!)

  let e_ge1_f := Wire.mk "s3_ege1f"
  let e_ge1_f_gate := [Gate.mkNOT (e_final[EFFW - 1]!) e_ge1_f]
  let (e_final_any, e_final_any_gates) := mkOrTree "s3_efany" e_final
  let e_final_zero := Wire.mk "s3_efzero"
  let e_final_zero_gate := [Gate.mkNOT e_final_any e_final_zero]
  let sub_ok := Wire.mk "s3_subok"
  let sub_ok_gate := [Gate.mkOR (e_final[EFFW - 1]!) e_final_zero sub_ok]

  -- overflow: E >= 255, i.e. the field saturated or a higher bit set
  let (e_hi_any, e_hi_any_gates) := mkOrTree "s3_ehiany" ((List.range 3).map fun i => e_final[WEXP +
    i]!)
  let (e_field_all, e_field_all_gates) := mkAndTree "s3_efall" ((List.range WEXP).map fun i =>
    e_final[i]!)
  let of_cond := Wire.mk "s3_ofc"
  let of_cond_gate := [
    Gate.mkOR e_hi_any e_field_all (Wire.mk "s3_ofc1"),
    Gate.mkAND (Wire.mk "s3_ofc1") e_ge1_f of_cond
  ]

  -- body: the fused rounding result
  -- a saturated exponent is the canonical infinity: field all ones, fraction zero
  let body := makeIndexedWires "s3_body" (MSB + 1)
  let body_gates :=
    [Gate.mkBUF s2_sign (body[MSB]!)] ++
    -- an infinity has the exponent field all ones, the largest finite value has
    -- all ones minus one, so the two differ in bit 0 only
    [Gate.mkMUX (e_final[0]!) ovf_to_inf of_cond (body[FRAC]!)] ++
    (List.range (WEXP - 1)).map
      (fun i => Gate.mkMUX (e_final[i + 1]!) one of_cond (body[FRAC + 1 + i]!)) ++
    -- the fraction is zero for an infinity and all ones for the saturated value
    (List.range FRAC).map (fun i => Gate.mkMUX (sig_final[i]!) not_ovf_to_inf of_cond (body[i]!))
  -- subnormal result: field 0, or the smallest normal when the rounding carried
  let carried := mant_inc[FRAC]!
  let sub_body := makeIndexedWires "s3_sbody" (MSB + 1)
  let sub_body_gates :=
    [Gate.mkBUF s2_sign (sub_body[MSB]!)] ++
    (List.range WEXP).flatMap (fun i =>
      [Gate.mkBUF zero (sub_body[FRAC + i]!),
       Gate.mkBUF zero (Wire.mk s!"s3_sbh{i}")]) ++
    (List.range FRAC).map (fun i => Gate.mkBUF (mant_inc[i]!) (sub_body[i]!))
  let sub_carry := Wire.mk "s3_subcarry"
  let sub_carry_gate := [Gate.mkAND carried sub_ok sub_carry]
  let sub_fix := makeIndexedWires "s3_subfix" (MSB + 1)
  let sub_fix_gates := (List.range (MSB + 1)).map fun i =>
    if i == MSB then Gate.mkBUF (sub_body[i]!) (sub_fix[i]!)
    else if i == FRAC then Gate.mkMUX (sub_body[i]!) one sub_carry (sub_fix[i]!)
    else Gate.mkMUX (sub_body[i]!) zero sub_carry (sub_fix[i]!)
  let body_sel := makeIndexedWires "s3_bsel" (MSB + 1)
  let body_sel_gates := (List.range (MSB + 1)).map fun i =>
    Gate.mkMUX (body[i]!) (sub_fix[i]!) sub_ok (body_sel[i]!)

  -- exact zero: the window and the sticky are both clear
  let exact_zero := Wire.mk "s3_exz"
  let not_stk := Wire.mk "s3_nstk"
  let exact_zero_gate := [
    Gate.mkNOT s2_stk not_stk,
    Gate.mkNOT win_any (Wire.mk "s3_nwany"),
    Gate.mkAND (Wire.mk "s3_nwany") not_stk exact_zero
  ]
  let zero_sign := Wire.mk "s3_zsign"
  let zero_sign_gate := [
    Gate.mkAND s2_prod_sign s2_c_sign (Wire.mk "s3_zsame1"),
    -- The two operand signs compared here must be the registered ones.  This
    -- once compared s1_prod_sign with s1_c_sign, which at this stage belong to
    -- an operation two cycles older, so a pipelined stream rounded an exact
    -- zero by the previous operation's signs.
    -- s3_zdiff means "the two signs differ", so it is the xor itself: the
    -- stage-1 signal it replaced was "the signs agree", and negating the xor
    -- would compare them the other way round.
    Gate.mkXOR s2_prod_sign s2_c_sign (Wire.mk "s3_zdiff"),
    Gate.mkAND rdn (Wire.mk "s3_zdiff") (Wire.mk "s3_zd1"),
    Gate.mkOR (Wire.mk "s3_zsame1") (Wire.mk "s3_zd1") zero_sign
  ]
  let zero_bits := makeIndexedWires "s3_zb" (MSB + 1)
  let zero_bits_gates := (List.range (MSB + 1)).map fun i =>
    if i == MSB then Gate.mkBUF zero_sign (zero_bits[i]!)
    else Gate.mkBUF zero (zero_bits[i]!)
  let with_zero := makeIndexedWires "s3_wz" (MSB + 1)
  let with_zero_gates := (List.range (MSB + 1)).map fun i =>
    Gate.mkMUX (body_sel[i]!) (zero_bits[i]!) exact_zero (with_zero[i]!)

  -- special cases, highest precedence last
  let nan_bits := makeIndexedWires "s3_nan" (MSB + 1)
  let nan_gates := (List.range (MSB + 1)).map fun i =>
    if FRAC - 1 <= i && i <= MSB - 1 then Gate.mkBUF one (nan_bits[i]!)
    else Gate.mkBUF zero (nan_bits[i]!)
  let inf_sign := Wire.mk "s3_isign"
  let inf_bits := makeIndexedWires "s3_inf" (MSB + 1)
  let inf_gates :=
    [Gate.mkMUX s2_c_sign s2_prod_sign s2_prod_inf inf_sign] ++
    (List.range (MSB + 1)).map fun i =>
      if i == MSB then Gate.mkBUF inf_sign (inf_bits[i]!)
      else if FRAC <= i && i <= MSB - 1 then Gate.mkBUF one (inf_bits[i]!)
      else Gate.mkBUF zero (inf_bits[i]!)
  let any_inf := Wire.mk "s3_anyinf"
  let any_inf_gate := [Gate.mkOR s2_prod_inf s2_c_inf any_inf]
  let sel_nan := Wire.mk "s3_selnan"
  let inf_sub_inf := Wire.mk "s3_isubinf"
  let sel_nan_gate := [
    Gate.mkXOR inf_sign s2_c_sign (Wire.mk "s3_xss"),
    Gate.mkNOT (Wire.mk "s3_xss") (Wire.mk "s3_ssame"),
    Gate.mkNOT (Wire.mk "s3_ssame") (Wire.mk "s3_sdiff"),
    Gate.mkAND s2_prod_inf s2_c_inf (Wire.mk "s3_bothinf"),
    Gate.mkAND (Wire.mk "s3_bothinf") (Wire.mk "s3_sdiff") (Wire.mk "s3_isiraw"),
    Gate.mkNOT s2_any_nan (Wire.mk "s3_notnan"),
    Gate.mkAND (Wire.mk "s3_isiraw") (Wire.mk "s3_notnan") inf_sub_inf,
    Gate.mkOR s2_any_nan s2_inf_zero (Wire.mk "s3_sn1"),
    Gate.mkOR (Wire.mk "s3_sn1") inf_sub_inf sel_nan
  ]
  let with_inf := makeIndexedWires "s3_wi" (MSB + 1)
  let with_inf_gates := (List.range (MSB + 1)).map fun i =>
    Gate.mkMUX (with_zero[i]!) (inf_bits[i]!) any_inf (with_inf[i]!)
  let with_nan := makeIndexedWires "s3_wn" (MSB + 1)
  let with_nan_gates := (List.range (MSB + 1)).map fun i =>
    Gate.mkMUX (with_inf[i]!) (nan_bits[i]!) sel_nan (with_nan[i]!)
  -- product zero with a nonzero addend: the result is the addend itself.  A
  -- zero addend as well is an exact zero sum, and taking the addend for it
  -- returned +0 under round toward negative where section 6.3 requires -0: the
  -- exact-zero path below already applies that rule, so this must not pre-empt
  -- it.
  let use_pz := Wire.mk "s3_usepz"
  let not_sel_nan := Wire.mk "s3_nselnan"
  let not_any_inf := Wire.mk "s3_nanyinf"
  let not_c_zero := Wire.mk "s3_ncz"
  let use_pz_gate := [
    Gate.mkNOT sel_nan not_sel_nan,
    Gate.mkNOT any_inf not_any_inf,
    Gate.mkNOT s2_c_zero not_c_zero,
    Gate.mkAND not_sel_nan not_any_inf (Wire.mk "s3_upz1"),
    Gate.mkAND (Wire.mk "s3_upz1") not_c_zero (Wire.mk "s3_upz2"),
    Gate.mkAND (Wire.mk "s3_upz2") s2_prod_zero use_pz
  ]
  let res_final := makeIndexedWires "s3_rf" (MSB + 1)
  let res_final_gates := (List.range (MSB + 1)).map fun i =>
    Gate.mkMUX (with_nan[i]!) (s2_c_eff[i]!) use_pz (res_final[i]!)
  let result_gates := (List.range (MSB + 1)).map fun i => Gate.mkBUF (res_final[i]!) (result[i]!)

  -- flags
  let nv := Wire.mk "s3_nv"
  let nv_gate := [
    Gate.mkOR s2_any_snan s2_inf_zero (Wire.mk "s3_nv1"),
    Gate.mkOR (Wire.mk "s3_nv1") inf_sub_inf nv
  ]
  -- the fused rounding's NX/UF/OF belong to the rounded result: a special
  -- (NaN, infinity, or the addend of a zero product) replaces it entirely
  let round_active := Wire.mk "s3_rond"
  let round_active_gate := [
    Gate.mkNOT sel_nan (Wire.mk "s3_nsn"),
    Gate.mkNOT any_inf (Wire.mk "s3_naif"),
    Gate.mkNOT use_pz (Wire.mk "s3_nupz"),
    Gate.mkAND (Wire.mk "s3_nsn") (Wire.mk "s3_naif") (Wire.mk "s3_ra1"),
    Gate.mkAND (Wire.mk "s3_ra1") (Wire.mk "s3_nupz") round_active
  ]
  -- a saturated result is inexact by definition, so OF implies NX
  let nx_any := Wire.mk "s3_nxany"
  let nx := Wire.mk "s3_nx"
  let nx_gate := [Gate.mkOR rem_any of_cond nx_any,
                  Gate.mkAND nx_any round_active nx]
  -- Underflow needs a tiny and inexact result.  A subnormal carry reaches
  -- the smallest normal number, which is not tiny.
  let not_sub_carry := Wire.mk "s3_nsubcarry"
  let uf_cand := Wire.mk "s3_ufcand"
  let uf := Wire.mk "s3_uf"
  let uf_gate := [
    Gate.mkNOT sub_carry not_sub_carry,
    Gate.mkAND sub_ok not_sub_carry uf_cand,
    Gate.mkAND uf_cand nx uf
  ]
  let of_final := Wire.mk "s3_of"
  let of_final_gate := [Gate.mkAND of_cond round_active of_final]
  let exc_gates := [
    Gate.mkBUF nx (exc[0]!),
    Gate.mkBUF uf (exc[1]!),
    Gate.mkBUF of_final (exc[2]!),
    Gate.mkBUF zero (exc[3]!),
    Gate.mkBUF nv (exc[4]!)
  ]

  -- the rounding is combinational over the stage-2 banks, so the valid is two
  -- deep: unpack/CSA, then align; a third stage would present the next
  -- operation's data with this one's valid.
  let tag_gates := (List.range 6).map fun i => Gate.mkBUF (s2_tag[i]!) (tag_out[i]!)
  let valid_gate := [Gate.mkBUF s2_valid valid_out]

  { name := nm
    inputs := src1 ++ src2 ++ src3 ++ rm ++ dest_tag ++
              [negate_product, subtract_addend, valid_in, clock, reset, zero]
    outputs := result ++ tag_out ++ exc ++ [valid_out]
    gates :=
      [one_gate] ++ exp_a_any_gates ++ exp_b_any_gates ++ exp_c_any_gates ++
      exp_a_all_gates ++ exp_b_all_gates ++ exp_c_all_gates ++
      frac_a_any_gates ++ frac_b_any_gates ++ frac_c_any_gates ++
      zero_det_gates ++ class_gates ++ eff_gates ++
      pp_gates ++ csa_gates ++ lead_c_gates ++ pos_c_gates ++ sh_c_gates ++
      mant_c_norm_gates ++ mant_c_gates ++ eff_c_sub_gates ++ eff_c_gates ++
      c_eff_gates ++ sign_gates ++ s1_gates ++
      prod_add_gates ++ lead_p_gates ++ pos_p_gates ++ s_h_gates ++ prod_n_gates ++
      exp_sum_gates ++ exp_t1_gates ++ exp_p_gates ++ diff_gates ++ c_big_gate ++
      p_up_amt_gates ++ p_left_amt_gates ++ p_up_amt_e_gates ++ p_down_amt_gates ++ c_left_amt_gates
        ++
      c_up_amt_gates ++ c_down_amt_gates ++ c_down_any_gates ++ p_down_any_gates ++
      p_up_gates ++ p_left_gates ++ p_down_gates ++ p_dir_gate ++
      q_win_gates ++ q_win_gates' ++
      c_up_gates ++ c_left_gates ++ c_down_gates ++ c_dir_gate ++
      c_win_gates ++ c_win_gates' ++ stk_gates ++ same_gate ++
      sum_win_gates ++ diff_qc_gates ++ diff_cq_gates ++ mag_gates ++
      res_sign_gate ++ small_win_gates ++ ulp_borrow_gates ++ mag_c_gates ++
      mag_sel_gates ++ win_gates ++ e_hi_gates ++ s2_gates ++
      win_any_gates ++ lead_v_gates ++ pos_v_gates ++ sh_v_gates ++
      n_up_gates ++ n_dn_gates ++ n_gates ++ extra_gate ++ e_res_gates ++
      st_lo_gates ++ st_gates ++ m_gates ++ e_any_gates ++ e_ge1_gate ++
      four_minus_e_gates ++ clamp_d_gates ++ clamp_gate ++ shd_gates ++
      mant_gates ++ ml_amt_gates ++ ml_gates ++ st2_raw_gates ++ any_unrounded_gate ++
      clamp_d_any_gates ++ past_round_gates ++ rnd_bit_gate ++ st2_gate ++ rem_any_gate ++
      rm_decode_gates ++ up_gates ++ mant_inc_gates ++ e_inc_gates ++
      e_final_gates ++ sig_final_gates ++ e_ge1_f_gate ++ e_final_any_gates ++
      e_final_zero_gate ++ sub_ok_gate ++ e_hi_any_gates ++ e_field_all_gates ++
      of_cond_gate ++ body_gates ++ sub_body_gates ++ sub_carry_gate ++
      sub_fix_gates ++ body_sel_gates ++ exact_zero_gate ++ zero_sign_gate ++
      zero_bits_gates ++ with_zero_gates ++ nan_gates ++ inf_gates ++
      any_inf_gate ++ sel_nan_gate ++ with_inf_gates ++ with_nan_gates ++
      use_pz_gate ++ res_final_gates ++ result_gates ++ nv_gate ++ nx_gate ++
      round_active_gate ++ uf_gate ++ of_final_gate ++ exc_gates ++ tag_gates ++ valid_gate
    instances := csa_instances
    signalGroups := [
      { name := "src1", width := MSB + 1, wires := src1 },
      { name := "src2", width := MSB + 1, wires := src2 },
      { name := "src3", width := MSB + 1, wires := src3 },
      { name := "rm", width := 3, wires := rm },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := MSB + 1, wires := result },
      { name := "tag_out", width := 6, wires := tag_out },
      { name := "exc", width := 5, wires := exc }
    ] }

/-- The single-precision fused multiply-add. -/
def mkFPFMA : Circuit := mkFPFMAFusedP "FPFMA" 24 127 8

/-- Convenience definition for the fused FMA circuit. -/
def fpFMACircuit : Circuit := mkFPFMA

end Shoumei.Circuits.Sequential

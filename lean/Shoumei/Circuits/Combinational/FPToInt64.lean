/-
Circuits/Combinational/FPToInt64.lean - 64-Bit Float to Integer Conversion Submodule

Rebuilds FPToInt64 with the hierarchical HDL frontend.
The circuit decomposes into four verified submodules:
  1. FPUnpackDP: Float unpack, SP-to-DP expansion, and classification
  2. FPToIntAlign: Dynamic 128-bit right shift and sticky bit reduction
  3. FPToIntRoundNeg: Rounding mode evaluation and parallel negation
  4. FPToIntClamp: Overflow detection, saturation, and exception generation
Computes magnitude increment and negation in parallel to meet 1.0 GHz timing.
-/

import Shoumei.DSL
import Shoumei.HDL.Types
import Shoumei.HDL.Expr
import Shoumei.HDL.Module
import Shoumei.HDL.Lower

namespace Shoumei.Circuits.Combinational

open Shoumei
open Shoumei.HDL

/-- Submodule 1: Unpack and classify SP/DP floating-point inputs. -/
def mkFPUnpackDP : HDLModule :=
  let src1 : Signal 64 := .input "src1" 64
  let is_dp : Signal 1 := .input "is_dp" 1

  let sp_in_sign : Signal 1 := src1.bit 31
  let sp_in_exp : Signal 8 := src1.slice 30 23
  let sp_in_mant : Signal 23 := src1.slice 22 0

  let sp_in_exp_ones : Signal 1 := sp_in_exp.andReduce
  let sp_in_exp_zeros : Signal 1 := ~~~sp_in_exp.orReduce
  let sp_in_mant_any : Signal 1 := sp_in_mant.orReduce
  let sp_in_mant_zeros : Signal 1 := ~~~sp_in_mant_any

  let sp_in_is_nan : Signal 1 := sp_in_exp_ones &&& sp_in_mant_any
  let sp_in_is_inf : Signal 1 := sp_in_exp_ones &&& sp_in_mant_zeros
  let sp_in_is_zero : Signal 1 := sp_in_exp_zeros &&& sp_in_mant_zeros

  have h8_11 : 8 ≤ 11 := by omega
  let sp_exp_ext : Signal 11 := Signal.zeroExtend 11 h8_11 sp_in_exp
  let const896 : Signal 11 := .const (BitVec.ofNat 11 896)
  let norm_sp_dp_exp : Signal 11 := sp_exp_ext + const896

  have hnorm : 1 + (11 + (23 + 29)) = 64 := by omega
  let norm_as_dp : Signal 64 := hnorm ▸ .concat sp_in_sign
    (.concat norm_sp_dp_exp (.concat sp_in_mant (Signal.zero 29)))

  have hzero : 1 + 63 = 64 := by omega
  let zero_as_dp : Signal 64 := hzero ▸ .concat sp_in_sign (Signal.zero 63)

  have hinf : 1 + (11 + 52) = 64 := by omega
  let inf_as_dp : Signal 64 := hinf ▸ .concat sp_in_sign
    (.concat (.const (BitVec.ofNat 11 0x7FF)) (Signal.zero 52))

  let nan_as_dp : Signal 64 := .const (BitVec.ofNat 64 0x7FF8000000000000)

  let sp_m0 : Signal 64 := .mux sp_in_is_zero zero_as_dp norm_as_dp
  let sp_m1 : Signal 64 := .mux sp_in_is_inf inf_as_dp sp_m0
  let sp_as_dp : Signal 64 := .mux sp_in_is_nan nan_as_dp sp_m1

  let flt_in : Signal 64 := .mux is_dp src1 sp_as_dp

  let flt_exp : Signal 11 := flt_in.slice 62 52
  let flt_mant : Signal 52 := flt_in.slice 51 0

  let flt_exp_ones : Signal 1 := flt_exp.andReduce
  let flt_exp_zeros : Signal 1 := ~~~flt_exp.orReduce
  let flt_mant_any : Signal 1 := flt_mant.orReduce
  let flt_mant_zeros : Signal 1 := ~~~flt_mant_any

  let flt_is_nan : Signal 1 := flt_exp_ones &&& flt_mant_any
  let flt_is_inf : Signal 1 := flt_exp_ones &&& flt_mant_zeros
  let flt_is_zero : Signal 1 := flt_exp_zeros &&& flt_mant_zeros

  let m := HDLModule.empty "FPUnpackDP"
  let m := m.addInput "src1" 64
  let m := m.addInput "is_dp" 1
  let m := m.addOutput "flt_in" 64 flt_in
  let m := m.addOutput "flt_is_nan" 1 flt_is_nan
  let m := m.addOutput "flt_is_inf" 1 flt_is_inf
  let m := m.addOutput "flt_is_zero" 1 flt_is_zero
  let m := m.addOutput "flt_mant_any" 1 flt_mant_any
  m

/-- Submodule 2: Dynamic 128-bit alignment shift and sticky bit calculation. -/
def mkFPToIntAlign : HDLModule :=
  let flt_in : Signal 64 := .input "flt_in" 64
  let flt_is_zero : Signal 1 := .input "flt_is_zero" 1

  let flt_exp : Signal 11 := flt_in.slice 62 52
  let flt_mant : Signal 52 := flt_in.slice 51 0

  let const1138 : Signal 11 := .const (BitVec.ofNat 11 1138)
  let shamt_full : Signal 11 := const1138 - flt_exp
  let shamt_borrow : Signal 1 := .ult const1138 flt_exp
  let shamt7_raw : Signal 7 := shamt_full.slice 6 0
  let shamt7 : Signal 7 := .mux shamt_borrow (Signal.zero 7) shamt7_raw

  have hbus : 12 + (1 + (52 + 63)) = 128 := by omega
  let bus128_init : Signal 128 := hbus ▸ .concat (Signal.zero 12)
    (.concat Signal.true1 (.concat flt_mant (Signal.zero 63)))

  let bus128_out : Signal 128 := Signal.dshr bus128_init shamt7

  let const1023 : Signal 11 := .const (BitVec.ofNat 11 1023)
  let flt_exp_lt_1023 : Signal 1 := .ult flt_exp const1023

  let bus_mag : Signal 64 := bus128_out.slice 63 0
  let flt_int_mag : Signal 64 := .mux flt_exp_lt_1023 (Signal.zero 64) bus_mag

  have hmant53 : 1 + 52 = 53 := by omega
  let mant53 : Signal 53 := hmant53 ▸ .concat Signal.true1 flt_mant

  let const1022 : Signal 11 := .const (BitVec.ofNat 11 1022)
  let const1075 : Signal 11 := .const (BitVec.ofNat 11 1075)

  let guard_amt_sub : Signal 11 := flt_exp - const1022
  let guard_amt_borrow : Signal 1 := .ult flt_exp const1022
  let amt_hi_borrow : Signal 1 := .ult flt_exp const1075

  let guard_raw : Signal 7 := guard_amt_sub.slice 6 0
  let const63 : Signal 7 := .const (BitVec.ofNat 7 63)
  let guard_clamped : Signal 7 := .mux amt_hi_borrow guard_raw const63
  let guard_amt : Signal 7 := .mux guard_amt_borrow (Signal.zero 7) guard_clamped

  let guard_shift : Signal 53 := Signal.dshl mant53 guard_amt

  let guard_sticky_slice : Signal 52 := guard_shift.slice 51 0
  let guard_sticky : Signal 1 := guard_sticky_slice.orReduce

  let below_half_nonzero : Signal 1 := guard_amt_borrow &&& (~~~flt_is_zero)
  let sticky_any : Signal 1 := guard_sticky ||| below_half_nonzero

  let flt_round_bit : Signal 1 := (~~~guard_amt_borrow) &&& (guard_shift.bit 52)
  let flt_sticky_bit : Signal 1 := sticky_any
  let flt_inexact : Signal 1 := flt_round_bit ||| flt_sticky_bit

  let exp_hi4 : Signal 4 := flt_exp.slice 9 6
  let exp_hi4_any : Signal 1 := exp_hi4.orReduce
  let exp_gte_1088 : Signal 1 := (flt_exp.bit 10) &&& exp_hi4_any

  let exp_lo6 : Signal 6 := flt_exp.slice 5 0
  let exp_lo6_all : Signal 1 := exp_lo6.andReduce
  let exp_bits1_5 : Signal 5 := flt_exp.slice 5 1
  let exp_bits1_5_all : Signal 1 := exp_bits1_5.andReduce

  let exp_gte1087 : Signal 1 := exp_gte_1088 ||| ((flt_exp.bit 10) &&& exp_lo6_all)
  let exp_gte1086 : Signal 1 := exp_gte_1088 ||| ((flt_exp.bit 10) &&& exp_bits1_5_all)

  let m := HDLModule.empty "FPToIntAlign"
  let m := m.addInput "flt_in" 64
  let m := m.addInput "flt_is_zero" 1
  let m := m.addOutput "flt_int_mag" 64 flt_int_mag
  let m := m.addOutput "flt_round_bit" 1 flt_round_bit
  let m := m.addOutput "flt_sticky_bit" 1 flt_sticky_bit
  let m := m.addOutput "flt_inexact" 1 flt_inexact
  let m := m.addOutput "flt_exp_lt1023" 1 flt_exp_lt_1023
  let m := m.addOutput "exp_gte1086" 1 exp_gte1086
  let m := m.addOutput "exp_gte1087" 1 exp_gte1087
  m

/-- Submodule 3: Rounding mode evaluation, magnitude increment, and parallel negation. -/
def mkFPToIntRoundNeg : HDLModule :=
  let flt_int_mag : Signal 64 := .input "flt_int_mag" 64
  let flt_sign : Signal 1 := .input "flt_sign" 1
  let flt_round_bit : Signal 1 := .input "flt_round_bit" 1
  let flt_sticky_bit : Signal 1 := .input "flt_sticky_bit" 1
  let flt_inexact : Signal 1 := .input "flt_inexact" 1
  let rm : Signal 3 := .input "rm" 3

  let rm_is_rne : Signal 1 := .eq rm (.const (BitVec.ofNat 3 0))
  let rm_is_rtz : Signal 1 := .eq rm (.const (BitVec.ofNat 3 1))
  let rm_is_rdn : Signal 1 := .eq rm (.const (BitVec.ofNat 3 2))
  let rm_is_rup : Signal 1 := .eq rm (.const (BitVec.ofNat 3 3))
  let rm_is_rmm : Signal 1 := .eq rm (.const (BitVec.ofNat 3 4))

  let flt_lsb : Signal 1 := flt_int_mag.bit 0
  let flt_stk_or_lsb : Signal 1 := flt_sticky_bit ||| flt_lsb
  let flt_rne_up : Signal 1 := flt_round_bit &&& flt_stk_or_lsb
  let flt_rdn_up : Signal 1 := flt_sign &&& flt_inexact
  let flt_rup_up : Signal 1 := (~~~flt_sign) &&& flt_inexact

  let flt_round_up_raw : Signal 1 :=
    (rm_is_rne &&& flt_rne_up) |||
    (rm_is_rdn &&& flt_rdn_up) |||
    (rm_is_rup &&& flt_rup_up) |||
    (rm_is_rmm &&& flt_round_bit)

  let flt_round_up : Signal 1 := flt_round_up_raw &&& flt_inexact

  have h1_64 : 1 ≤ 64 := by omega
  let round_up_ext : Signal 64 := Signal.zeroExtend 64 h1_64 flt_round_up
  let flt_int_mag_inc : Signal 64 := flt_int_mag + round_up_ext
  let flt_mag_ovf : Signal 1 := flt_int_mag.andReduce &&& flt_round_up

  let not_mag : Signal 64 := ~~~flt_int_mag
  let neg_base : Signal 64 := not_mag + (.const (BitVec.ofNat 64 1))
  let flt_int_neg : Signal 64 := .mux flt_round_up not_mag neg_base

  let m := HDLModule.empty "FPToIntRoundNeg"
  let m := m.addInput "flt_int_mag" 64
  let m := m.addInput "flt_sign" 1
  let m := m.addInput "flt_round_bit" 1
  let m := m.addInput "flt_sticky_bit" 1
  let m := m.addInput "flt_inexact" 1
  let m := m.addInput "rm" 3
  let m := m.addOutput "flt_int_mag_inc" 64 flt_int_mag_inc
  let m := m.addOutput "flt_mag_ovf" 1 flt_mag_ovf
  let m := m.addOutput "flt_int_neg" 64 flt_int_neg
  let m := m.addOutput "flt_round_up" 1 flt_round_up
  m

/-- Submodule 4: Clamping, bounds saturation, and exception generation. -/
def mkFPToIntClamp : HDLModule :=
  let flt_int_mag_inc : Signal 64 := .input "flt_int_mag_inc" 64
  let flt_int_neg : Signal 64 := .input "flt_int_neg" 64
  let flt_mag_ovf : Signal 1 := .input "flt_mag_ovf" 1
  let flt_round_up : Signal 1 := .input "flt_round_up" 1
  let flt_sign : Signal 1 := .input "flt_sign" 1
  let is_unsigned : Signal 1 := .input "is_unsigned" 1
  let flt_is_nan : Signal 1 := .input "flt_is_nan" 1
  let flt_is_inf : Signal 1 := .input "flt_is_inf" 1
  let flt_is_zero : Signal 1 := .input "flt_is_zero" 1
  let flt_mant_any : Signal 1 := .input "flt_mant_any" 1
  let flt_exp_lt1023 : Signal 1 := .input "flt_exp_lt1023" 1
  let exp_gte1086 : Signal 1 := .input "exp_gte1086" 1
  let exp_gte1087 : Signal 1 := .input "exp_gte1087" 1
  let flt_inexact : Signal 1 := .input "flt_inexact" 1

  let signed_val : Signal 64 := .mux flt_sign flt_int_neg flt_int_mag_inc
  let flt_int_norm : Signal 64 := .mux is_unsigned flt_int_mag_inc signed_val

  let pos_signed_ovf : Signal 1 :=
    (~~~flt_sign) &&& (exp_gte1086 ||| flt_int_mag_inc.bit 63)
  let neg_signed_ovf : Signal 1 :=
    flt_sign &&& (exp_gte1087 ||| (exp_gte1086 &&& flt_mant_any))
  let signed_nv : Signal 1 := pos_signed_ovf ||| neg_signed_ovf

  let pos_unsigned_ovf : Signal 1 :=
    (~~~flt_sign) &&& (exp_gte1087 ||| flt_mag_ovf)
  let nuo_ge1 : Signal 1 := (~~~flt_exp_lt1023) &&& (~~~flt_is_zero)
  let nuo_rup : Signal 1 := flt_round_up &&& (~~~flt_is_zero)
  let neg_unsigned_ovf : Signal 1 := flt_sign &&& (nuo_ge1 ||| nuo_rup)
  let unsigned_nv : Signal 1 := pos_unsigned_ovf ||| neg_unsigned_ovf

  let flt_nv_raw : Signal 1 := .mux is_unsigned unsigned_nv signed_nv
  let nan_inf : Signal 1 := flt_is_nan ||| flt_is_inf
  let flt_nv : Signal 1 := flt_nv_raw ||| nan_inf
  let exc_nv : Signal 1 := flt_nv

  let clamp_u_val : Signal 1 := flt_is_nan ||| (~~~flt_sign)
  let clamp_unsigned : Signal 64 := Signal.replicate 64 clamp_u_val

  let clamp_is_neg : Signal 1 := flt_sign &&& (~~~flt_is_nan)
  let clamp_bit63 : Signal 1 := clamp_is_neg
  let clamp_bits62_0 : Signal 63 := Signal.replicate 63 (~~~clamp_is_neg)
  have hclamp : 1 + 63 = 64 := by omega
  let clamp_signed : Signal 64 := hclamp ▸ .concat clamp_bit63 clamp_bits62_0

  let clamp_val : Signal 64 := .mux is_unsigned clamp_unsigned clamp_signed
  let result : Signal 64 := .mux flt_nv clamp_val flt_int_norm

  let exc_nx : Signal 1 := flt_inexact &&& (~~~flt_nv)

  let m := HDLModule.empty "FPToIntClamp"
  let m := m.addInput "flt_int_mag_inc" 64
  let m := m.addInput "flt_int_neg" 64
  let m := m.addInput "flt_mag_ovf" 1
  let m := m.addInput "flt_round_up" 1
  let m := m.addInput "flt_sign" 1
  let m := m.addInput "is_unsigned" 1
  let m := m.addInput "flt_is_nan" 1
  let m := m.addInput "flt_is_inf" 1
  let m := m.addInput "flt_is_zero" 1
  let m := m.addInput "flt_mant_any" 1
  let m := m.addInput "flt_exp_lt1023" 1
  let m := m.addInput "exp_gte1086" 1
  let m := m.addInput "exp_gte1087" 1
  let m := m.addInput "flt_inexact" 1
  let m := m.addOutput "result" 64 result
  let m := m.addOutput "exc_nv" 1 exc_nv
  let m := m.addOutput "exc_nx" 1 exc_nx
  m

/-- Hierarchical FPToInt64 module composed of four submodules with 1-cycle pipeline. -/
def mkFPToInt64HDL : HDLModule :=
  let src1 : Signal 64 := .input "src1" 64
  let is_dp : Signal 1 := .input "is_dp" 1
  let is_unsigned : Signal 1 := .input "is_unsigned" 1
  let rm : Signal 3 := .input "rm" 3

  let clkW := Wire.mk "clock"
  let rstW := Wire.mk "reset"

  let instUnpack : InstanceBinding := {
    instName := "u_unpack"
    moduleName := "FPUnpackDP"
    inputs := [
      .mk "src1" 64 src1,
      .mk "is_dp" 1 is_dp
    ]
    outputs := [
      ("flt_in", 64),
      ("flt_is_nan", 1),
      ("flt_is_inf", 1),
      ("flt_is_zero", 1),
      ("flt_mant_any", 1)
    ]
  }

  let flt_in : Signal 64 := .instOut "u_unpack" "flt_in" 64
  let flt_is_nan : Signal 1 := .instOut "u_unpack" "flt_is_nan" 1
  let flt_is_inf : Signal 1 := .instOut "u_unpack" "flt_is_inf" 1
  let flt_is_zero : Signal 1 := .instOut "u_unpack" "flt_is_zero" 1
  let flt_mant_any : Signal 1 := .instOut "u_unpack" "flt_mant_any" 1

  let instAlign : InstanceBinding := {
    instName := "u_align"
    moduleName := "FPToIntAlign"
    inputs := [
      .mk "flt_in" 64 flt_in,
      .mk "flt_is_zero" 1 flt_is_zero
    ]
    outputs := [
      ("flt_int_mag", 64),
      ("flt_round_bit", 1),
      ("flt_sticky_bit", 1),
      ("flt_inexact", 1),
      ("flt_exp_lt1023", 1),
      ("exp_gte1086", 1),
      ("exp_gte1087", 1)
    ]
  }

  let flt_int_mag : Signal 64 := .instOut "u_align" "flt_int_mag" 64
  let flt_round_bit : Signal 1 := .instOut "u_align" "flt_round_bit" 1
  let flt_sticky_bit : Signal 1 := .instOut "u_align" "flt_sticky_bit" 1
  let flt_inexact : Signal 1 := .instOut "u_align" "flt_inexact" 1
  let flt_exp_lt1023 : Signal 1 := .instOut "u_align" "flt_exp_lt1023" 1
  let exp_gte1086 : Signal 1 := .instOut "u_align" "exp_gte1086" 1
  let exp_gte1087 : Signal 1 := .instOut "u_align" "exp_gte1087" 1

  let flt_sign : Signal 1 := flt_in.bit 63

  -- Registered Stage 1 signals as .wire inputs to Stage 2:
  let reg_flt_int_mag : Signal 64 := .wire "s1_fimag" 64
  let reg_flt_round_bit : Signal 1 := .wire "s1_fround" 1
  let reg_flt_sticky_bit : Signal 1 := .wire "s1_fsticky" 1
  let reg_flt_inexact : Signal 1 := .wire "s1_finexact" 1
  let reg_flt_sign : Signal 1 := .wire "s1_fsign" 1
  let reg_is_unsigned : Signal 1 := .wire "s1_is_uns" 1
  let reg_rm : Signal 3 := .wire "s1_rm" 3
  let reg_flt_is_nan : Signal 1 := .wire "s1_fnan" 1
  let reg_flt_is_inf : Signal 1 := .wire "s1_finf" 1
  let reg_flt_is_zero : Signal 1 := .wire "s1_fzero" 1
  let reg_flt_mant_any : Signal 1 := .wire "s1_mant_any" 1
  let reg_flt_exp_lt1023 : Signal 1 := .wire "s1_exp_lt1023" 1
  let reg_exp_gte1086 : Signal 1 := .wire "s1_exp_gte1086" 1
  let reg_exp_gte1087 : Signal 1 := .wire "s1_exp_gte1087" 1

  let instRoundNeg : InstanceBinding := {
    instName := "u_round_neg"
    moduleName := "FPToIntRoundNeg"
    inputs := [
      .mk "flt_int_mag" 64 reg_flt_int_mag,
      .mk "flt_sign" 1 reg_flt_sign,
      .mk "flt_round_bit" 1 reg_flt_round_bit,
      .mk "flt_sticky_bit" 1 reg_flt_sticky_bit,
      .mk "flt_inexact" 1 reg_flt_inexact,
      .mk "rm" 3 reg_rm
    ]
    outputs := [
      ("flt_int_mag_inc", 64),
      ("flt_mag_ovf", 1),
      ("flt_int_neg", 64),
      ("flt_round_up", 1)
    ]
  }

  let flt_int_mag_inc : Signal 64 := .instOut "u_round_neg" "flt_int_mag_inc" 64
  let flt_mag_ovf : Signal 1 := .instOut "u_round_neg" "flt_mag_ovf" 1
  let flt_int_neg : Signal 64 := .instOut "u_round_neg" "flt_int_neg" 64
  let flt_round_up : Signal 1 := .instOut "u_round_neg" "flt_round_up" 1

  let instClamp : InstanceBinding := {
    instName := "u_clamp"
    moduleName := "FPToIntClamp"
    inputs := [
      .mk "flt_int_mag_inc" 64 flt_int_mag_inc,
      .mk "flt_int_neg" 64 flt_int_neg,
      .mk "flt_mag_ovf" 1 flt_mag_ovf,
      .mk "flt_round_up" 1 flt_round_up,
      .mk "flt_sign" 1 reg_flt_sign,
      .mk "is_unsigned" 1 reg_is_unsigned,
      .mk "flt_is_nan" 1 reg_flt_is_nan,
      .mk "flt_is_inf" 1 reg_flt_is_inf,
      .mk "flt_is_zero" 1 reg_flt_is_zero,
      .mk "flt_mant_any" 1 reg_flt_mant_any,
      .mk "flt_exp_lt1023" 1 reg_flt_exp_lt1023,
      .mk "exp_gte1086" 1 reg_exp_gte1086,
      .mk "exp_gte1087" 1 reg_exp_gte1087,
      .mk "flt_inexact" 1 reg_flt_inexact
    ]
    outputs := [
      ("result", 64),
      ("exc_nv", 1),
      ("exc_nx", 1)
    ]
  }

  let result : Signal 64 := .instOut "u_clamp" "result" 64
  let exc_nv : Signal 1 := .instOut "u_clamp" "exc_nv" 1
  let exc_nx : Signal 1 := .instOut "u_clamp" "exc_nx" 1

  let m := HDLModule.empty "FPToInt64"
  let m := m.addInput "src1" 64
  let m := m.addInput "is_dp" 1
  let m := m.addInput "is_unsigned" 1
  let m := m.addInput "rm" 3
  let m := m.addInput "clock" 1
  let m := m.addInput "reset" 1
  let m := m.addInstance instUnpack
  let m := m.addInstance instAlign
  let m := m.addRegister "s1_fimag" 64 clkW rstW flt_int_mag
  let m := m.addRegister "s1_fround" 1 clkW rstW flt_round_bit
  let m := m.addRegister "s1_fsticky" 1 clkW rstW flt_sticky_bit
  let m := m.addRegister "s1_finexact" 1 clkW rstW flt_inexact
  let m := m.addRegister "s1_fsign" 1 clkW rstW flt_sign
  let m := m.addRegister "s1_is_uns" 1 clkW rstW is_unsigned
  let m := m.addRegister "s1_rm" 3 clkW rstW rm
  let m := m.addRegister "s1_fnan" 1 clkW rstW flt_is_nan
  let m := m.addRegister "s1_finf" 1 clkW rstW flt_is_inf
  let m := m.addRegister "s1_fzero" 1 clkW rstW flt_is_zero
  let m := m.addRegister "s1_mant_any" 1 clkW rstW flt_mant_any
  let m := m.addRegister "s1_exp_lt1023" 1 clkW rstW flt_exp_lt1023
  let m := m.addRegister "s1_exp_gte1086" 1 clkW rstW exp_gte1086
  let m := m.addRegister "s1_exp_gte1087" 1 clkW rstW exp_gte1087
  let m := m.addInstance instRoundNeg
  let m := m.addInstance instClamp
  let m := m.addOutput "result" 64 result
  let m := m.addOutput "exc_nv" 1 exc_nv
  let m := m.addOutput "exc_nx" 1 exc_nx
  m

/-- Lowered circuit definitions for each component. -/
def fpUnpackDPCircuit : Circuit :=
  let c := lowerModule mkFPUnpackDP
  { name := "FPUnpackDP",
    inputs := c.inputs,
    outputs := c.outputs,
    gates := c.gates,
    instances := c.instances,
    signalGroups := c.signalGroups,
    keepHierarchy := true }

def fpToIntAlignCircuit : Circuit :=
  let c := lowerModule mkFPToIntAlign
  { name := "FPToIntAlign",
    inputs := c.inputs,
    outputs := c.outputs,
    gates := c.gates,
    instances := c.instances,
    signalGroups := c.signalGroups,
    keepHierarchy := true }

def fpToIntRoundNegCircuit : Circuit :=
  let c := lowerModule mkFPToIntRoundNeg
  { name := "FPToIntRoundNeg",
    inputs := c.inputs,
    outputs := c.outputs,
    gates := c.gates,
    instances := c.instances,
    signalGroups := c.signalGroups,
    keepHierarchy := true }

def fpToIntClampCircuit : Circuit :=
  let c := lowerModule mkFPToIntClamp
  { name := "FPToIntClamp",
    inputs := c.inputs,
    outputs := c.outputs,
    gates := c.gates,
    instances := c.instances,
    signalGroups := c.signalGroups,
    keepHierarchy := true }

def fpToInt64Circuit : Circuit :=
  let c := lowerModule mkFPToInt64HDL
  { name := "FPToInt64",
    inputs := c.inputs,
    outputs := c.outputs,
    gates := c.gates,
    instances := c.instances,
    signalGroups := c.signalGroups,
    keepHierarchy := true }

end Shoumei.Circuits.Combinational

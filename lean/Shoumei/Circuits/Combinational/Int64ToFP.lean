/-
Circuits/Combinational/Int64ToFP.lean - 64-Bit Integer to Float Conversion Submodule

Rebuilds Int64ToFP with the hierarchical HDL frontend.
The circuit decomposes into three submodules:
  1. Int64Prep: Absolute value calculation, leading-zero detection, and base exponent generation
  2. Int64NormShift: Dynamic barrel left shift and sticky bit extraction
  3. Int64RoundPack: Fast mantissa increment, exponent selection, and SP/DP packaging
Meeting the 1.0 GHz ASAP7 timing constraint with 1-cycle pipeline latency.
-/

import Shoumei.DSL
import Shoumei.HDL.Types
import Shoumei.HDL.Expr
import Shoumei.HDL.Module
import Shoumei.HDL.Lower

namespace Shoumei.Circuits.Combinational

open Shoumei
open Shoumei.HDL

/-- 8-bit priority encoder: finds leading 1 (bit 7 down to bit 0). -/
def pe8 (b : Signal 8) : Signal 1 × Signal 3 :=
  let b7 := b.bit 7
  let b6 := b.bit 6
  let b5 := b.bit 5
  let b4 := b.bit 4
  let b3 := b.bit 3
  let b2 := b.bit 2
  let b1 := b.bit 1
  let b0 := b.bit 0
  let hi4 := b7 ||| b6 ||| b5 ||| b4
  let lo4 := b3 ||| b2 ||| b1 ||| b0
  let has1 := hi4 ||| lo4
  let hi_pair := b7 ||| b6
  let lo_pair := b3 ||| b2
  let pos2 := hi4
  let pos1 := .mux hi4 hi_pair lo_pair
  let hi_b0 := b7 ||| (~~~b6 &&& b5)
  let lo_b0 := b3 ||| (~~~b2 &&& b1)
  let pos0 := .mux hi4 hi_b0 lo_b0
  let pos : Signal 3 := Signal.concat (Signal.concat pos2 pos1) pos0
  (has1, pos)

/-- 8-to-1 multiplexer for 3-bit signals. -/
def mux8x3 (sel : Signal 3) (x0 x1 x2 x3 x4 x5 x6 x7 : Signal 3) : Signal 3 :=
  let m01 := .mux (sel.bit 0) x1 x0
  let m23 := .mux (sel.bit 0) x3 x2
  let m45 := .mux (sel.bit 0) x5 x4
  let m67 := .mux (sel.bit 0) x7 x6
  let m0123 := .mux (sel.bit 1) m23 m01
  let m4567 := .mux (sel.bit 1) m67 m45
  .mux (sel.bit 2) m4567 m0123

/-- Submodule 1: Integer absolute value, leading-zero detection, and base exponent generation. -/
def mkInt64Prep : HDLModule :=
  let src1 : Signal 64 := .input "src1" 64
  let is_unsigned : Signal 1 := .input "is_unsigned" 1

  let int_sign_expr : Signal 1 := src1.bit 63 &&& ~~~is_unsigned
  let int_neg_expr : Signal 64 := (.const (BitVec.ofNat 64 0)) - src1
  let int_abs_expr : Signal 64 := .mux (.wire "w_int_sign" 1) int_neg_expr src1

  let int_abs : Signal 64 := .wire "w_int_abs" 64
  let int_sign : Signal 1 := .wire "w_int_sign" 1

  let g0 := int_abs.slice 7 0
  let g1 := int_abs.slice 15 8
  let g2 := int_abs.slice 23 16
  let g3 := int_abs.slice 31 24
  let g4 := int_abs.slice 39 32
  let g5 := int_abs.slice 47 40
  let g6 := int_abs.slice 55 48
  let g7 := int_abs.slice 63 56

  let (has0, p0) := pe8 g0
  let (has1, p1) := pe8 g1
  let (has2, p2) := pe8 g2
  let (has3, p3) := pe8 g3
  let (has4, p4) := pe8 g4
  let (has5, p5) := pe8 g5
  let (has6, p6) := pe8 g6
  let (has7, p7) := pe8 g7

  let has76 := Signal.concat has7 has6
  let has54 := Signal.concat has5 has4
  let has32 := Signal.concat has3 has2
  let has10 := Signal.concat has1 has0
  let has_hi := Signal.concat has76 has54
  let has_lo := Signal.concat has32 has10
  let has_groups := Signal.concat has_hi has_lo

  let (has_any_expr, top_pos) := pe8 has_groups
  let bot_pos := mux8x3 top_pos p0 p1 p2 p3 p4 p5 p6 p7
  let lead_pos_expr : Signal 6 := Signal.concat top_pos bot_pos

  let lead_pos : Signal 6 := .wire "lead_pos" 6
  let has_any : Signal 1 := .wire "has_any" 1

  let int_is_zero : Signal 1 := ~~~has_any
  let norm_shamt : Signal 6 := ~~~lead_pos

  have h6_11 : 6 ≤ 11 := by omega
  let lead_pos_ext11 := Signal.zeroExtend 11 h6_11 lead_pos
  let dp_exp_base : Signal 11 := (.const (BitVec.ofNat 11 1023)) + lead_pos_ext11
  let dp_exp_inc : Signal 11 := (.const (BitVec.ofNat 11 1024)) + lead_pos_ext11

  have h6_8 : 6 ≤ 8 := by omega
  let lead_pos_ext8 := Signal.zeroExtend 8 h6_8 lead_pos
  let sp_exp_base : Signal 8 := (.const (BitVec.ofNat 8 127)) + lead_pos_ext8
  let sp_exp_inc : Signal 8 := (.const (BitVec.ofNat 8 128)) + lead_pos_ext8

  let m := HDLModule.empty "Int64Prep"
  let m := m.addInput "src1" 64
  let m := m.addInput "is_unsigned" 1
  let m := m.addWire "w_int_sign" 1 int_sign_expr
  let m := m.addWire "w_int_abs" 64 int_abs_expr
  let m := m.addWire "has_any" 1 has_any_expr
  let m := m.addWire "lead_pos" 6 lead_pos_expr
  let m := m.addOutput "int_abs" 64 int_abs
  let m := m.addOutput "norm_shamt" 6 norm_shamt
  let m := m.addOutput "int_sign" 1 int_sign
  let m := m.addOutput "int_is_zero" 1 int_is_zero
  let m := m.addOutput "dp_exp_base" 11 dp_exp_base
  let m := m.addOutput "dp_exp_inc" 11 dp_exp_inc
  let m := m.addOutput "sp_exp_base" 8 sp_exp_base
  let m := m.addOutput "sp_exp_inc" 8 sp_exp_inc
  m

/-- Submodule 2: Dynamic barrel left shift and sticky bit extraction. -/
def mkInt64NormShift : HDLModule :=
  let norm_in : Signal 64 := .input "norm_in" 64
  let norm_shamt : Signal 6 := .input "norm_shamt" 6

  let norm64_expr : Signal 64 := norm_in.dshl norm_shamt
  let norm64 : Signal 64 := .wire "norm64" 64

  let dp_raw_mant : Signal 52 := norm64.slice 62 11
  let dp_round_bit : Signal 1 := norm64.bit 10
  let dp_sticky_bit : Signal 1 := (norm64.slice 9 0).orReduce

  let sp_raw_mant : Signal 23 := norm64.slice 62 40
  let sp_round_bit : Signal 1 := norm64.bit 39
  let sp_sticky_bit : Signal 1 := (norm64.slice 38 0).orReduce

  let m := HDLModule.empty "Int64NormShift"
  let m := m.addInput "norm_in" 64
  let m := m.addInput "norm_shamt" 6
  let m := m.addWire "norm64" 64 norm64_expr
  let m := m.addOutput "dp_raw_mant" 52 dp_raw_mant
  let m := m.addOutput "dp_round_bit" 1 dp_round_bit
  let m := m.addOutput "dp_sticky_bit" 1 dp_sticky_bit
  let m := m.addOutput "sp_raw_mant" 23 sp_raw_mant
  let m := m.addOutput "sp_round_bit" 1 sp_round_bit
  let m := m.addOutput "sp_sticky_bit" 1 sp_sticky_bit
  m

/-- Submodule 3: Mantissa rounding, exponent increment, and SP/DP float packing. -/
def mkInt64RoundPack : HDLModule :=
  let dp_raw_mant : Signal 52 := .input "dp_raw_mant" 52
  let dp_round_bit : Signal 1 := .input "dp_round_bit" 1
  let dp_sticky_bit : Signal 1 := .input "dp_sticky_bit" 1
  let sp_raw_mant : Signal 23 := .input "sp_raw_mant" 23
  let sp_round_bit : Signal 1 := .input "sp_round_bit" 1
  let sp_sticky_bit : Signal 1 := .input "sp_sticky_bit" 1
  let int_sign : Signal 1 := .input "int_sign" 1
  let int_is_zero : Signal 1 := .input "int_is_zero" 1
  let is_dp : Signal 1 := .input "is_dp" 1
  let rm : Signal 3 := .input "rm" 3
  let dp_exp_base : Signal 11 := .input "dp_exp_base" 11
  let dp_exp_inc : Signal 11 := .input "dp_exp_inc" 11
  let sp_exp_base : Signal 8 := .input "sp_exp_base" 8
  let sp_exp_inc : Signal 8 := .input "sp_exp_inc" 8

  let not_rm0 := ~~~rm.bit 0
  let not_rm1 := ~~~rm.bit 1
  let not_rm2 := ~~~rm.bit 2
  let rm_is_rne := not_rm2 &&& not_rm1 &&& not_rm0
  let rm_is_rtz := not_rm2 &&& not_rm1 &&& rm.bit 0
  let rm_is_rdn := not_rm2 &&& rm.bit 1 &&& not_rm0
  let rm_is_rup := not_rm2 &&& rm.bit 1 &&& rm.bit 0
  let rm_is_rmm := rm.bit 2 &&& not_rm1 &&& not_rm0

  -- Double-precision rounding
  let dp_inexact := dp_round_bit ||| dp_sticky_bit
  let dp_lsb := dp_raw_mant.bit 0
  let dp_stk_or_lsb := dp_sticky_bit ||| dp_lsb
  let dp_rne_up := dp_round_bit &&& dp_stk_or_lsb
  let dp_rdn_up := int_sign &&& dp_inexact
  let dp_rup_up := (~~~int_sign) &&& dp_inexact
  let dp_round_up_raw :=
    (rm_is_rne &&& dp_rne_up) |||
    (rm_is_rdn &&& dp_rdn_up) |||
    (rm_is_rup &&& dp_rup_up) |||
    (rm_is_rmm &&& dp_round_bit)
  let dp_round_up := dp_round_up_raw &&& dp_inexact

  have h1_52 : 1 ≤ 52 := by omega
  let dp_round_up_ext : Signal 52 := Signal.zeroExtend 52 h1_52 dp_round_up
  let dp_mant_inc_expr : Signal 52 := dp_raw_mant + dp_round_up_ext
  let dp_mant_inc : Signal 52 := .wire "dp_mant_inc" 52
  let dp_mant_ovf : Signal 1 := dp_raw_mant.andReduce &&& dp_round_up
  let dp_mant_final : Signal 52 := .mux dp_mant_ovf (.const (BitVec.ofNat 52 0)) dp_mant_inc
  let dp_exp_final : Signal 11 := .mux dp_mant_ovf dp_exp_inc dp_exp_base

  let dp_hi12 : Signal 12 := Signal.concat int_sign dp_exp_final
  let dp_val : Signal 64 := Signal.concat dp_hi12 dp_mant_final
  let res_dp : Signal 64 := .mux int_is_zero (.const (BitVec.ofNat 64 0)) dp_val

  -- Single-precision rounding
  let sp_inexact := sp_round_bit ||| sp_sticky_bit
  let sp_lsb := sp_raw_mant.bit 0
  let sp_stk_or_lsb := sp_sticky_bit ||| sp_lsb
  let sp_rne_up := sp_round_bit &&& sp_stk_or_lsb
  let sp_rdn_up := int_sign &&& sp_inexact
  let sp_rup_up := (~~~int_sign) &&& sp_inexact
  let sp_round_up_raw :=
    (rm_is_rne &&& sp_rne_up) |||
    (rm_is_rdn &&& sp_rdn_up) |||
    (rm_is_rup &&& sp_rup_up) |||
    (rm_is_rmm &&& sp_round_bit)
  let sp_round_up := sp_round_up_raw &&& sp_inexact

  have h1_23 : 1 ≤ 23 := by omega
  let sp_round_up_ext : Signal 23 := Signal.zeroExtend 23 h1_23 sp_round_up
  let sp_mant_inc_expr : Signal 23 := sp_raw_mant + sp_round_up_ext
  let sp_mant_inc : Signal 23 := .wire "sp_mant_inc" 23
  let sp_mant_ovf : Signal 1 := sp_raw_mant.andReduce &&& sp_round_up
  let sp_mant_final : Signal 23 := .mux sp_mant_ovf (.const (BitVec.ofNat 23 0)) sp_mant_inc
  let sp_exp_final : Signal 8 := .mux sp_mant_ovf sp_exp_inc sp_exp_base

  let sp_hi9 : Signal 9 := Signal.concat int_sign sp_exp_final
  let sp_val : Signal 32 := Signal.concat sp_hi9 sp_mant_final
  let sp_masked : Signal 32 := .mux int_is_zero (.const (BitVec.ofNat 32 0)) sp_val
  let res_sp : Signal 64 := Signal.concat (.const (BitVec.ofNat 32 4294967295)) sp_masked

  let result : Signal 64 := .mux is_dp res_dp res_sp
  let exc_nx : Signal 1 := .mux is_dp dp_inexact sp_inexact

  let m := HDLModule.empty "Int64RoundPack"
  let m := m.addInput "dp_raw_mant" 52
  let m := m.addInput "dp_round_bit" 1
  let m := m.addInput "dp_sticky_bit" 1
  let m := m.addInput "sp_raw_mant" 23
  let m := m.addInput "sp_round_bit" 1
  let m := m.addInput "sp_sticky_bit" 1
  let m := m.addInput "int_sign" 1
  let m := m.addInput "int_is_zero" 1
  let m := m.addInput "is_dp" 1
  let m := m.addInput "rm" 3
  let m := m.addInput "dp_exp_base" 11
  let m := m.addInput "dp_exp_inc" 11
  let m := m.addInput "sp_exp_base" 8
  let m := m.addInput "sp_exp_inc" 8
  let m := m.addWire "dp_mant_inc" 52 dp_mant_inc_expr
  let m := m.addWire "sp_mant_inc" 23 sp_mant_inc_expr
  let m := m.addOutput "result" 64 result
  let m := m.addOutput "exc_nx" 1 exc_nx
  m

/-- Hierarchical Int64ToFP module with 1-cycle pipeline. -/
def mkInt64ToFPHDL : HDLModule :=
  let src1 : Signal 64 := .input "src1" 64
  let is_dp : Signal 1 := .input "is_dp" 1
  let is_unsigned : Signal 1 := .input "is_unsigned" 1
  let rm : Signal 3 := .input "rm" 3

  let instPrep : InstanceBinding := {
    instName := "u_prep"
    moduleName := "Int64Prep"
    inputs := [
      .mk "src1" 64 src1,
      .mk "is_unsigned" 1 is_unsigned
    ]
    outputs := [
      ("int_abs", 64),
      ("norm_shamt", 6),
      ("int_sign", 1),
      ("int_is_zero", 1),
      ("dp_exp_base", 11),
      ("dp_exp_inc", 11),
      ("sp_exp_base", 8),
      ("sp_exp_inc", 8)
    ]
  }

  let prep_int_abs : Signal 64 := .instOut "u_prep" "int_abs" 64
  let prep_norm_shamt : Signal 6 := .instOut "u_prep" "norm_shamt" 6
  let prep_int_sign : Signal 1 := .instOut "u_prep" "int_sign" 1
  let prep_int_is_zero : Signal 1 := .instOut "u_prep" "int_is_zero" 1
  let prep_dp_exp_base : Signal 11 := .instOut "u_prep" "dp_exp_base" 11
  let prep_dp_exp_inc : Signal 11 := .instOut "u_prep" "dp_exp_inc" 11
  let prep_sp_exp_base : Signal 8 := .instOut "u_prep" "sp_exp_base" 8
  let prep_sp_exp_inc : Signal 8 := .instOut "u_prep" "sp_exp_inc" 8

  let clkW : Wire := Wire.mk "clock"
  let rstW : Wire := Wire.mk "reset"

  let reg_int_abs : Signal 64 := .wire "s1_int_abs" 64
  let reg_norm_shamt : Signal 6 := .wire "s1_norm_shamt" 6
  let reg_int_sign : Signal 1 := .wire "s1_int_sign" 1
  let reg_int_is_zero : Signal 1 := .wire "s1_int_is_zero" 1
  let reg_is_dp : Signal 1 := .wire "s1_is_dp" 1
  let reg_rm : Signal 3 := .wire "s1_rm" 3
  let reg_dp_exp_base : Signal 11 := .wire "s1_dp_exp_base" 11
  let reg_dp_exp_inc : Signal 11 := .wire "s1_dp_exp_inc" 11
  let reg_sp_exp_base : Signal 8 := .wire "s1_sp_exp_base" 8
  let reg_sp_exp_inc : Signal 8 := .wire "s1_sp_exp_inc" 8

  let instNormShift : InstanceBinding := {
    instName := "u_norm_shift"
    moduleName := "Int64NormShift"
    inputs := [
      .mk "norm_in" 64 reg_int_abs,
      .mk "norm_shamt" 6 reg_norm_shamt
    ]
    outputs := [
      ("dp_raw_mant", 52),
      ("dp_round_bit", 1),
      ("dp_sticky_bit", 1),
      ("sp_raw_mant", 23),
      ("sp_round_bit", 1),
      ("sp_sticky_bit", 1)
    ]
  }

  let shift_dp_raw_mant : Signal 52 := .instOut "u_norm_shift" "dp_raw_mant" 52
  let shift_dp_round_bit : Signal 1 := .instOut "u_norm_shift" "dp_round_bit" 1
  let shift_dp_sticky_bit : Signal 1 := .instOut "u_norm_shift" "dp_sticky_bit" 1
  let shift_sp_raw_mant : Signal 23 := .instOut "u_norm_shift" "sp_raw_mant" 23
  let shift_sp_round_bit : Signal 1 := .instOut "u_norm_shift" "sp_round_bit" 1
  let shift_sp_sticky_bit : Signal 1 := .instOut "u_norm_shift" "sp_sticky_bit" 1

  let instRoundPack : InstanceBinding := {
    instName := "u_round_pack"
    moduleName := "Int64RoundPack"
    inputs := [
      .mk "dp_raw_mant" 52 shift_dp_raw_mant,
      .mk "dp_round_bit" 1 shift_dp_round_bit,
      .mk "dp_sticky_bit" 1 shift_dp_sticky_bit,
      .mk "sp_raw_mant" 23 shift_sp_raw_mant,
      .mk "sp_round_bit" 1 shift_sp_round_bit,
      .mk "sp_sticky_bit" 1 shift_sp_sticky_bit,
      .mk "int_sign" 1 reg_int_sign,
      .mk "int_is_zero" 1 reg_int_is_zero,
      .mk "is_dp" 1 reg_is_dp,
      .mk "rm" 3 reg_rm,
      .mk "dp_exp_base" 11 reg_dp_exp_base,
      .mk "dp_exp_inc" 11 reg_dp_exp_inc,
      .mk "sp_exp_base" 8 reg_sp_exp_base,
      .mk "sp_exp_inc" 8 reg_sp_exp_inc
    ]
    outputs := [
      ("result", 64),
      ("exc_nx", 1)
    ]
  }

  let result : Signal 64 := .instOut "u_round_pack" "result" 64
  let exc_nx : Signal 1 := .instOut "u_round_pack" "exc_nx" 1

  let m := HDLModule.empty "Int64ToFP"
  let m := m.addInput "src1" 64
  let m := m.addInput "is_dp" 1
  let m := m.addInput "is_unsigned" 1
  let m := m.addInput "rm" 3
  let m := m.addInput "clock" 1
  let m := m.addInput "reset" 1
  let m := m.addInstance instPrep
  let m := m.addRegister "s1_int_abs" 64 clkW rstW prep_int_abs
  let m := m.addRegister "s1_norm_shamt" 6 clkW rstW prep_norm_shamt
  let m := m.addRegister "s1_int_sign" 1 clkW rstW prep_int_sign
  let m := m.addRegister "s1_int_is_zero" 1 clkW rstW prep_int_is_zero
  let m := m.addRegister "s1_is_dp" 1 clkW rstW is_dp
  let m := m.addRegister "s1_rm" 3 clkW rstW rm
  let m := m.addRegister "s1_dp_exp_base" 11 clkW rstW prep_dp_exp_base
  let m := m.addRegister "s1_dp_exp_inc" 11 clkW rstW prep_dp_exp_inc
  let m := m.addRegister "s1_sp_exp_base" 8 clkW rstW prep_sp_exp_base
  let m := m.addRegister "s1_sp_exp_inc" 8 clkW rstW prep_sp_exp_inc
  let m := m.addInstance instNormShift
  let m := m.addInstance instRoundPack
  let m := m.addOutput "result" 64 result
  let m := m.addOutput "exc_nx" 1 exc_nx
  m

/-- Lowered circuit definitions for each component. -/
def int64PrepCircuit : Circuit :=
  let c := lowerModule mkInt64Prep
  { name := "Int64Prep",
    inputs := c.inputs,
    outputs := c.outputs,
    gates := c.gates,
    instances := c.instances,
    signalGroups := c.signalGroups,
    keepHierarchy := true }

def int64NormShiftCircuit : Circuit :=
  let c := lowerModule mkInt64NormShift
  { name := "Int64NormShift",
    inputs := c.inputs,
    outputs := c.outputs,
    gates := c.gates,
    instances := c.instances,
    signalGroups := c.signalGroups,
    keepHierarchy := true }

def int64RoundPackCircuit : Circuit :=
  let c := lowerModule mkInt64RoundPack
  { name := "Int64RoundPack",
    inputs := c.inputs,
    outputs := c.outputs,
    gates := c.gates,
    instances := c.instances,
    signalGroups := c.signalGroups,
    keepHierarchy := true }

def int64ToFPCircuit : Circuit :=
  let c := lowerModule mkInt64ToFPHDL
  { name := "Int64ToFP",
    inputs := c.inputs,
    outputs := c.outputs,
    gates := c.gates,
    instances := c.instances,
    signalGroups := c.signalGroups,
    keepHierarchy := true }

end Shoumei.Circuits.Combinational

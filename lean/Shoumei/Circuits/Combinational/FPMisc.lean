/-
Circuits/Combinational/FPMisc.lean - FP Miscellaneous Operations Circuit

Implements single-cycle FP bit-manipulation operations for RV32F:
  FSGNJ, FSGNJN, FSGNJX, FMV.X.W, FMV.W.X

Inputs:
  - src1[31:0], src2[31:0] - source operands
  - op[4:0] - operation select
  - zero, one - constant wires

Outputs:
  - result[31:0] - operation result
  - exc[4:0] - exception flags (always 0 for these ops)
-/

import Shoumei.DSL

namespace Shoumei.Circuits.Combinational

open Shoumei

private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

/-- FP miscellaneous operations: sign injection, FMV. -/
def fpMiscCircuit : Circuit :=
  let src1 := makeIndexedWires "src1" 32
  let src2 := makeIndexedWires "src2" 32
  let op := makeIndexedWires "op" 5
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"
  let result := makeIndexedWires "result" 32
  let exc := makeIndexedWires "exc" 5

  -- Sign bits for FSGNJ variants
  -- fsgnj_bit31 = src2[31]
  let fsgnj_bit31 := Wire.mk "fsgnj_bit31"
  let g_fsgnj := Gate.mkBUF (src2[31]!) fsgnj_bit31

  -- fsgnjn_bit31 = NOT src2[31]
  let fsgnjn_bit31 := Wire.mk "fsgnjn_bit31"
  let g_fsgnjn := Gate.mkNOT (src2[31]!) fsgnjn_bit31

  -- fsgnjx_bit31 = src1[31] XOR src2[31]
  let fsgnjx_bit31 := Wire.mk "fsgnjx_bit31"
  let g_fsgnjx := Gate.mkXOR (src1[31]!) (src2[31]!) fsgnjx_bit31

  -- Op decoding: match specific encodings
  -- FSGNJ  = 21 = 10101  → op4=1, op3=0, op2=1, op1=0, op0=1
  -- FSGNJN = 22 = 10110  → op4=1, op3=0, op2=1, op1=1, op0=0
  -- FSGNJX = 23 = 10111  → op4=1, op3=0, op2=1, op1=1, op0=1
  -- FMV_X_W= 16 = 10000  → op4=1, op3=0, op2=0, op1=0, op0=0
  -- FMV_W_X= 17 = 10001  → op4=1, op3=0, op2=0, op1=0, op0=1

  -- Inverted op bits for decoding
  let nop := makeIndexedWires "nop" 5
  let inv_gates := (List.range 5).map fun i =>
    Gate.mkNOT (op[i]!) (nop[i]!)

  -- is_fsgnj  = op4 & !op3 & op2 & !op1 & op0
  let fsgnj_t0 := Wire.mk "fsgnj_t0"
  let fsgnj_t1 := Wire.mk "fsgnj_t1"
  let fsgnj_t2 := Wire.mk "fsgnj_t2"
  let fsgnj_t3 := Wire.mk "fsgnj_t3"
  let is_fsgnj := Wire.mk "is_fsgnj"
  let dec_fsgnj := [
    Gate.mkAND (op[4]!) (nop[3]!) fsgnj_t0,
    Gate.mkAND (op[2]!) (nop[1]!) fsgnj_t1,
    Gate.mkAND fsgnj_t0 fsgnj_t1 fsgnj_t2,
    Gate.mkAND fsgnj_t2 (op[0]!) fsgnj_t3,
    Gate.mkBUF fsgnj_t3 is_fsgnj
  ]

  -- is_fsgnjn = op4 & !op3 & op2 & op1 & !op0
  let fsgnjn_t0 := Wire.mk "fsgnjn_t0"
  let fsgnjn_t1 := Wire.mk "fsgnjn_t1"
  let fsgnjn_t2 := Wire.mk "fsgnjn_t2"
  let is_fsgnjn := Wire.mk "is_fsgnjn"
  let dec_fsgnjn := [
    Gate.mkAND (op[4]!) (nop[3]!) fsgnjn_t0,
    Gate.mkAND (op[2]!) (op[1]!) fsgnjn_t1,
    Gate.mkAND fsgnjn_t0 fsgnjn_t1 fsgnjn_t2,
    Gate.mkAND fsgnjn_t2 (nop[0]!) is_fsgnjn
  ]

  -- is_fsgnjx = op4 & !op3 & op2 & op1 & op0
  let fsgnjx_t0 := Wire.mk "fsgnjx_t0"
  let fsgnjx_t1 := Wire.mk "fsgnjx_t1"
  let fsgnjx_t2 := Wire.mk "fsgnjx_t2"
  let is_fsgnjx := Wire.mk "is_fsgnjx"
  let dec_fsgnjx := [
    Gate.mkAND (op[4]!) (nop[3]!) fsgnjx_t0,
    Gate.mkAND (op[2]!) (op[1]!) fsgnjx_t1,
    Gate.mkAND fsgnjx_t0 fsgnjx_t1 fsgnjx_t2,
    Gate.mkAND fsgnjx_t2 (op[0]!) is_fsgnjx
  ]

  -- is_fmv = op4 & !op3 & !op2 & !op1  (covers both FMV_X_W and FMV_W_X)
  let fmv_t0 := Wire.mk "fmv_t0"
  let fmv_t1 := Wire.mk "fmv_t1"
  let is_fmv := Wire.mk "is_fmv"
  let dec_fmv := [
    Gate.mkAND (op[4]!) (nop[3]!) fmv_t0,
    Gate.mkAND (nop[2]!) (nop[1]!) fmv_t1,
    Gate.mkAND fmv_t0 fmv_t1 is_fmv
  ]

  -- is_sgnj_any = is_fsgnj | is_fsgnjn | is_fsgnjx
  let sgnj_or0 := Wire.mk "sgnj_or0"
  let is_sgnj_any := Wire.mk "is_sgnj_any"
  let dec_sgnj_any := [
    Gate.mkOR is_fsgnj is_fsgnjn sgnj_or0,
    Gate.mkOR sgnj_or0 is_fsgnjx is_sgnj_any
  ]

  -- Compute sign bit for sgnj group:
  -- sgnj_sign = MUX(is_fsgnjx, fsgnjx_bit31, MUX(is_fsgnjn, fsgnjn_bit31, fsgnj_bit31))
  let sgnj_sign_inner := Wire.mk "sgnj_sign_inner"
  let sgnj_sign := Wire.mk "sgnj_sign"
  let sgnj_sign_gates := [
    Gate.mkMUX fsgnj_bit31 fsgnjn_bit31 is_fsgnjn sgnj_sign_inner,
    Gate.mkMUX sgnj_sign_inner fsgnjx_bit31 is_fsgnjx sgnj_sign
  ]

  -- Build result bits [30:0]: for sgnj and fmv, these are src1[30:0]; default zero
  -- is_active = is_sgnj_any | is_fmv
  let is_active := Wire.mk "is_active"
  let g_active := Gate.mkOR is_sgnj_any is_fmv is_active

  let low_gates := (List.range 31).map fun i =>
    -- result[i] = is_active ? src1[i] : zero
    Gate.mkMUX zero (src1[i]!) is_active (result[i]!)

  -- result[31]:
  -- For sgnj ops: sgnj_sign
  -- For fmv: src1[31]
  -- Otherwise: zero
  -- result[31] = MUX(is_sgnj_any, sgnj_sign, MUX(is_fmv, src1[31], zero))
  let r31_fmv := Wire.mk "r31_fmv"
  let bit31_gates := [
    Gate.mkMUX zero (src1[31]!) is_fmv r31_fmv,
    Gate.mkMUX r31_fmv sgnj_sign is_sgnj_any (result[31]!)
  ]

  -- Exception flags: all zero for these operations
  let exc_gates := (List.range 5).map fun i =>
    Gate.mkBUF zero (exc[i]!)

  { name := "FPMisc"
    inputs := src1 ++ src2 ++ op ++ [zero, one]
    outputs := result ++ exc
    gates :=
      [g_fsgnj, g_fsgnjn, g_fsgnjx] ++
      inv_gates ++
      dec_fsgnj ++ dec_fsgnjn ++ dec_fsgnjx ++ dec_fmv ++
      dec_sgnj_any ++ sgnj_sign_gates ++
      [g_active] ++ low_gates ++ bit31_gates ++ exc_gates
    instances := []
    signalGroups := [
      { name := "src1",   width := 32, wires := src1 },
      { name := "src2",   width := 32, wires := src2 },
      { name := "op",     width := 5,  wires := op },
      { name := "result", width := 32, wires := result },
      { name := "exc",    width := 5,  wires := exc }
    ]
  }

end Shoumei.Circuits.Combinational

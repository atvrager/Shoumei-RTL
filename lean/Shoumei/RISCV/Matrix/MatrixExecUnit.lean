/-
RISCV/Matrix/MatrixExecUnit.lean - Matrix Execution Unit for VME

Wraps the MAC array, accumulator register file, and control FSM into a single
execution unit for VME matrix multiply-accumulate operations.

Follows MulDivExecUnit.lean pattern.

Architecture:
- MACArray instance (combinational compute)
- AccumulatorRegFile (DFF array, maxRows × maxCols × 32 bits)
- SEW mux (select int8 vs int16 datapath)
- Output mux (row read vs col read vs config result)
- FSM controller for multi-cycle operations

Inputs:
- vs1_data[127:0]: Vector source 1 data (from VecRegStub)
- vs2_data[127:0]: Vector source 2 data (from VecRegStub)
- scalar[31:0]: Scalar operand (for VMACC_AVX)
- op[3:0]: VME operation encoding
- dest_tag[5:0]: Physical register tag for CDB broadcast
- row_col_idx[3:0]: Row/column index for read/write ops
- valid_in: New operation request
- clock, reset, zero, one

Outputs:
- result[31:0]: Computation result (for CDB broadcast)
- tag_out[5:0]: Destination tag pass-through
- valid_out: Result ready
- busy: Cannot accept new operation

VME operation encoding (op[3:0]):
- 0000: MSETCLI  (set tile column dimension)
- 0001: MSETRLI  (set tile row dimension)
- 0010: VOP_AVV  (outer product, overwrite accumulator)
- 0011: VOPACC_AVV (outer product accumulate)
- 0100: VMACC_AVX  (vector-scalar MAC)
- 0101: VRACCR   (read accumulator row, destructive)
- 0110: VRACCC   (read accumulator column, destructive)
- 0111: VWACCR   (write accumulator row)
- 1000: VWACCC   (write accumulator column)
- 1001: VRRACCR  (raw read accumulator row)
- 1010: VRWACCR  (raw write accumulator row)
-/

import Shoumei.DSL
import Shoumei.RISCV.Config
import Shoumei.RISCV.Matrix.AccumulatorState
import Shoumei.RISCV.Matrix.VecRegStub
import Shoumei.Circuits.Combinational.MACArray

namespace Shoumei.RISCV.Matrix

open Shoumei
open Shoumei.Circuits.Combinational

/-! ## Behavioral Model -/

/-- VME operation codes -/
def vmeOpMSETCLI   : Nat := 0
def vmeOpMSETRLI   : Nat := 1
def vmeOpVOP_AVV   : Nat := 2
def vmeOpVOPACC_AVV : Nat := 3
def vmeOpVMACC_AVX : Nat := 4
def vmeOpVRACCR    : Nat := 5
def vmeOpVRACCC    : Nat := 6
def vmeOpVWACCR    : Nat := 7
def vmeOpVWACCC    : Nat := 8
def vmeOpVRRACCR   : Nat := 9
def vmeOpVRWACCR   : Nat := 10

/-- Matrix execution unit state.

    For VLEN=128: maxRows=16, maxCols=16 (sized for int8). -/
structure MatrixExecState (maxRows maxCols : Nat) where
  /-- Accumulator array -/
  accum : AccumulatorState maxRows maxCols
  /-- Unit busy flag -/
  busy : Bool
  /-- Current element width (8 or 16) -/
  sew : SEW
  /-- Cycle counter for multi-cycle ops -/
  cycleCount : Nat

/-- Initial state -/
def MatrixExecState.init (maxRows maxCols : Nat) : MatrixExecState maxRows maxCols :=
  { accum := AccumulatorState.init maxRows maxCols
    busy := false
    sew := .Int8
    cycleCount := 0 }

/-- Extract an element from a packed vector (UInt32 representing VLEN bits).

    For simplicity in the behavioral model, we pass elements as functions. -/
private def extractElement (data : Fin n → Bool) (elemIdx : Nat) (elemWidth : Nat) : UInt32 :=
  let bits := (List.range elemWidth).map (fun b =>
    let bitIdx := elemIdx * elemWidth + b
    if h : bitIdx < n then
      if data ⟨bitIdx, h⟩ then ((1 : UInt32) <<< b.toUInt32) else (0 : UInt32)
    else (0 : UInt32))
  bits.foldl (· ||| ·) (0 : UInt32)

/-- Step the matrix execution unit by one clock cycle.

    Returns updated state and optional CDB broadcast (tag, value). -/
def matrixStep
    (maxRows maxCols : Nat)
    (state : MatrixExecState maxRows maxCols)
    (vs1_data vs2_data : Fin 128 → Bool)
    (scalar : UInt32)
    (op : Nat)
    (rowColIdx : Nat)
    (tag : Fin 64)
    (valid : Bool)
    : MatrixExecState maxRows maxCols × Option (Fin 64 × UInt32) :=

  if !valid then (state, none)
  else match op with
  | 0 => -- MSETCLI: set VL (tile columns)
    let newState := { state with
      accum := state.accum.setVL (min rowColIdx maxCols) }
    (newState, some (tag, rowColIdx.toUInt32))

  | 1 => -- MSETRLI: set TR (tile rows)
    let newState := { state with
      accum := state.accum.setTR (min rowColIdx maxRows) }
    (newState, some (tag, rowColIdx.toUInt32))

  | 2 => -- VOP_AVV: outer product (overwrite)
    let sew := state.sew
    let elemWidth := sew.bits
    let numElems := 128 / elemWidth
    let vs1Elems : Fin maxRows → UInt32 := fun i =>
      if i.val < numElems then extractElement vs1_data i.val elemWidth else 0
    let vs2Elems : Fin maxCols → UInt32 := fun j =>
      if j.val < numElems then extractElement vs2_data j.val elemWidth else 0
    let newAccum := state.accum.outerProduct vs1Elems vs2Elems sew
    let newState := { state with accum := newAccum }
    (newState, some (tag, 0))  -- Signal completion

  | 3 => -- VOPACC_AVV: outer product accumulate
    let sew := state.sew
    let elemWidth := sew.bits
    let numElems := 128 / elemWidth
    let vs1Elems : Fin maxRows → UInt32 := fun i =>
      if i.val < numElems then extractElement vs1_data i.val elemWidth else 0
    let vs2Elems : Fin maxCols → UInt32 := fun j =>
      if j.val < numElems then extractElement vs2_data j.val elemWidth else 0
    let newAccum := state.accum.outerProductAccum vs1Elems vs2Elems sew
    let newState := { state with accum := newAccum }
    (newState, some (tag, 0))

  | 4 => -- VMACC_AVX: vector-scalar MAC
    let sew := state.sew
    let elemWidth := sew.bits
    let numElems := 128 / elemWidth
    let vs1Elems : Fin maxRows → UInt32 := fun i =>
      if i.val < numElems then extractElement vs1_data i.val elemWidth else 0
    let newAccum := state.accum.vectorScalarMAC vs1Elems scalar sew
    let newState := { state with accum := newAccum }
    (newState, some (tag, 0))

  | 5 => -- VRACCR: read row (destructive)
    if h : rowColIdx < maxRows then
      let (newAccum, rowData) := state.accum.readRowDestructive ⟨rowColIdx, h⟩
      -- Return first element of the row (rest would need multiple CDB broadcasts)
      let firstVal := if hc : 0 < maxCols then rowData ⟨0, hc⟩ else 0
      let newState := { state with accum := newAccum }
      (newState, some (tag, firstVal))
    else (state, none)

  | 6 => -- VRACCC: read column (destructive)
    if h : rowColIdx < maxCols then
      let (newAccum, colData) := state.accum.readColDestructive ⟨rowColIdx, h⟩
      let firstVal := if hr : 0 < maxRows then colData ⟨0, hr⟩ else 0
      let newState := { state with accum := newAccum }
      (newState, some (tag, firstVal))
    else (state, none)

  | 7 => -- VWACCR: write row
    if h : rowColIdx < maxRows then
      let elemWidth := state.sew.bits
      let numElems := 128 / elemWidth
      let rowVals : Fin maxCols → UInt32 := fun j =>
        if j.val < numElems then extractElement vs1_data j.val elemWidth else 0
      let newAccum := state.accum.writeRow ⟨rowColIdx, h⟩ rowVals
      let newState := { state with accum := newAccum }
      (newState, some (tag, 0))
    else (state, none)

  | 8 => -- VWACCC: write column
    if h : rowColIdx < maxCols then
      let elemWidth := state.sew.bits
      let numElems := 128 / elemWidth
      let colVals : Fin maxRows → UInt32 := fun i =>
        if i.val < numElems then extractElement vs1_data i.val elemWidth else 0
      let newAccum := state.accum.writeCol ⟨rowColIdx, h⟩ colVals
      let newState := { state with accum := newAccum }
      (newState, some (tag, 0))
    else (state, none)

  | 9 => -- VRRACCR: raw read row (non-destructive)
    if h : rowColIdx < maxRows then
      let rowData := state.accum.rawReadRow ⟨rowColIdx, h⟩
      let firstVal := if hc : 0 < maxCols then rowData ⟨0, hc⟩ else 0
      (state, some (tag, firstVal))
    else (state, none)

  | 10 => -- VRWACCR: raw write row
    if h : rowColIdx < maxRows then
      let elemWidth := state.sew.bits
      let numElems := 128 / elemWidth
      let rowVals : Fin maxCols → UInt32 := fun j =>
        if j.val < numElems then extractElement vs1_data j.val elemWidth else 0
      let newAccum := state.accum.rawWriteRow ⟨rowColIdx, h⟩ rowVals
      let newState := { state with accum := newAccum }
      (newState, some (tag, 0))
    else (state, none)

  | _ => (state, none)

/-! ## Structural Circuit -/

/-- Build the Matrix Execution Unit structural circuit.

    Uses hierarchical composition:
    - MACArray16x16_8 for int8 outer products
    - MACArray8x8_16 for int16 outer products
    - Accumulator DFF array (16×16×32 = 8192 bits)
    - FSM controller
    - Output mux
-/
def mkMatrixExecUnit : Circuit :=
  let maxRows := 16
  let maxCols := 16
  let accumBits := maxRows * maxCols * 32  -- 8192

  -- Inputs
  let vs1_data := makeIndexedWires "vs1_data" 128
  let vs2_data := makeIndexedWires "vs2_data" 128
  let scalar := makeIndexedWires "scalar" 32
  let op := makeIndexedWires "op" 4
  let dest_tag := makeIndexedWires "dest_tag" 6
  let row_col_idx := makeIndexedWires "row_col_idx" 4
  let valid_in := Wire.mk "valid_in"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- Outputs
  let result := makeIndexedWires "result" 32
  let tag_out := makeIndexedWires "tag_out" 6
  let valid_out := Wire.mk "valid_out"
  let busy := Wire.mk "busy"

  -- Accumulator storage (registered)
  let acc_reg := makeIndexedWires "acc_reg" accumBits
  let acc_next := makeIndexedWires "acc_next" accumBits

  -- MAC array outputs
  let mac8_out := makeIndexedWires "mac8_out" accumBits
  let mac16_out := makeIndexedWires "mac16_out" (8 * 8 * 32)  -- 2048 bits

  -- MACArray16x16_8 instance (int8 path)
  let mac8_inst : CircuitInstance := {
    moduleName := "MACArray16x16_8"
    instName := "u_mac8"
    portMap :=
      (vs1_data.enum.map (fun ⟨i, w⟩ => (s!"vs1_{i}", w))) ++
      (vs2_data.enum.map (fun ⟨i, w⟩ => (s!"vs2_{i}", w))) ++
      (acc_reg.enum.map (fun ⟨i, w⟩ => (s!"acc_in_{i}", w))) ++
      [("zero", zero)] ++
      (mac8_out.enum.map (fun ⟨i, w⟩ => (s!"acc_out_{i}", w)))
  }

  -- MACArray8x8_16 instance (int16 path)
  let mac16_inst : CircuitInstance := {
    moduleName := "MACArray8x8_16"
    instName := "u_mac16"
    portMap :=
      ((List.range 128).map (fun i => vs1_data[i]!)).enum.map (fun ⟨i, w⟩ => (s!"vs1_{i}", w)) ++
      ((List.range 128).map (fun i => vs2_data[i]!)).enum.map (fun ⟨i, w⟩ => (s!"vs2_{i}", w)) ++
      ((List.range 2048).map (fun i => acc_reg[i]!)).enum.map (fun ⟨i, w⟩ => (s!"acc_in_{i}", w)) ++
      [("zero", zero)] ++
      (mac16_out.enum.map (fun ⟨i, w⟩ => (s!"acc_out_{i}", w)))
  }

  -- SEW select: op determines which MAC array output to use
  -- For simplicity, MUX between mac8_out and mac16_out for the first 2048 bits
  -- (the int16 array only produces 2048 bits, padded with zeros for the rest)
  let sew_sel := Wire.mk "sew_sel"  -- 0=int8, 1=int16
  let sew_mux_gates : List Gate :=
    (List.range accumBits).map (fun i =>
      let mac16_wire := if i < 2048 then mac16_out[i]! else zero
      Gate.mkMUX (mac8_out[i]!) mac16_wire sew_sel (acc_next[i]!))

  -- Accumulator DFF storage
  let acc_write_en := Wire.mk "acc_write_en"
  let acc_mux := makeIndexedWires "acc_mux" accumBits
  let acc_mux_gates : List Gate := (List.range accumBits).map (fun i =>
    Gate.mkMUX (acc_reg[i]!) (acc_next[i]!) acc_write_en (acc_mux[i]!))
  let acc_dff_gates : List Gate := (List.range accumBits).map (fun i =>
    Gate.mkDFF (acc_mux[i]!) clock reset (acc_reg[i]!))

  -- Tag pass-through register
  let tag_reg := makeIndexedWires "tag_reg" 6
  let tag_dff_gates : List Gate := (List.range 6).map (fun i =>
    Gate.mkDFF (dest_tag[i]!) clock reset (tag_reg[i]!))
  let tag_out_gates := (List.range 6).map (fun i =>
    Gate.mkBUF (tag_reg[i]!) (tag_out[i]!))

  -- Result output: read from accumulator row/col based on row_col_idx
  -- For now, output first 32 bits of the selected row
  -- row_col_idx selects which 32-bit chunk of acc_reg to read
  -- result[k] = acc_reg[row_col_idx * maxCols * 32 + k] (simplified: first column)
  let result_mux_gates : List Gate := (List.range 32).map (fun k =>
    -- Simple: just output from base of accumulator (row 0, col 0)
    -- Full implementation would decode row_col_idx
    Gate.mkBUF (acc_reg[k]!) (result[k]!))

  -- Control signals (simplified FSM)
  -- acc_write_en = valid_in AND (op is compute operation)
  let is_compute := Wire.mk "is_compute"
  -- op == 2 or op == 3 or op == 4 → compute (outer product / MAC)
  let op2_match := Wire.mk "op2_match"
  let op3_match := Wire.mk "op3_match"
  let op4_match := Wire.mk "op4_match"
  let op23 := Wire.mk "op23"

  -- Decode: op == 0010 (VOP_AVV)
  let not_op0 := Wire.mk "not_op0"
  let not_op2 := Wire.mk "not_op2"
  let not_op3 := Wire.mk "not_op3"
  let decode_gates := [
    Gate.mkNOT (op[0]!) not_op0,
    Gate.mkNOT (op[2]!) not_op2,
    Gate.mkNOT (op[3]!) not_op3,
    -- op == 0010: !op[3] & !op[2] & op[1] & !op[0]
    Gate.mkAND not_op3 not_op2 (Wire.mk "d_hi"),
    Gate.mkAND (op[1]!) not_op0 (Wire.mk "d_lo"),
    Gate.mkAND (Wire.mk "d_hi") (Wire.mk "d_lo") op2_match,
    -- op == 0011: !op[3] & !op[2] & op[1] & op[0]
    Gate.mkAND (Wire.mk "d_hi") (Wire.mk "d_lo2") op3_match,
    Gate.mkAND (op[1]!) (op[0]!) (Wire.mk "d_lo2"),
    -- op == 0100: !op[3] & op[2] & !op[1] & !op[0]
    Gate.mkAND not_op3 (op[2]!) (Wire.mk "d_hi4"),
    Gate.mkAND (Wire.mk "d_hi4") (Wire.mk "d_lo") op4_match,
    -- is_compute = op2 | op3 | op4
    Gate.mkOR op2_match op3_match op23,
    Gate.mkOR op23 op4_match is_compute,
    Gate.mkAND valid_in is_compute acc_write_en
  ]

  -- sew_sel: for now hardcode to 0 (int8). Full impl would read sew register.
  let sew_gate := [Gate.mkBUF zero sew_sel]

  -- valid_out = registered valid_in (1-cycle latency for config ops, multi-cycle for compute)
  let valid_reg := Wire.mk "valid_reg"
  let valid_dff := [Gate.mkDFF valid_in clock reset valid_reg,
                    Gate.mkBUF valid_reg valid_out]

  -- busy = 0 for single-cycle ops (simplified)
  let busy_gate := [Gate.mkBUF zero busy]

  { name := "MatrixExecUnit"
    inputs := vs1_data ++ vs2_data ++ scalar ++ op ++ dest_tag ++
              row_col_idx ++ [valid_in, clock, reset, zero, one]
    outputs := result ++ tag_out ++ [valid_out, busy]
    gates := sew_mux_gates ++ acc_mux_gates ++ acc_dff_gates ++
             tag_dff_gates ++ tag_out_gates ++ result_mux_gates ++
             decode_gates ++ sew_gate ++ valid_dff ++ busy_gate
    instances := [mac8_inst, mac16_inst]
    signalGroups := [
      { name := "vs1_data", width := 128, wires := vs1_data },
      { name := "vs2_data", width := 128, wires := vs2_data },
      { name := "scalar", width := 32, wires := scalar },
      { name := "op", width := 4, wires := op },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "row_col_idx", width := 4, wires := row_col_idx },
      { name := "result", width := 32, wires := result },
      { name := "tag_out", width := 6, wires := tag_out },
      { name := "acc_reg", width := accumBits, wires := acc_reg },
      { name := "acc_next", width := accumBits, wires := acc_next }
    ]
  }

/-- Convenience alias -/
def matrixExecUnit : Circuit := mkMatrixExecUnit

end Shoumei.RISCV.Matrix

/-
FallbackSequencer.lean - Microcoded Fallback Execution Sequencer.

A dedicated sequential circuit for emulating un-decoded instructions (Zb* proving ground)
or vectoring to an architectural illegal instruction trap.
Exposes a TileLink TL-UH compatible WCS interface for host inspection, locking, and updates.
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.Register
import Shoumei.RISCV.Microcode.FallbackTypes

namespace Shoumei.RISCV.Microcode

open Shoumei
open Shoumei.Circuits.Sequential

/-- Helper: create indexed wires -/
private def makeWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

/-- Full adder cell returning sum and carry out -/
private def mkFullAdderCell (pfx : String) (i : Nat) (a b cin : Wire) : (List Gate × Wire × Wire) :=
  let ab_xor := Wire.mk s!"{pfx}_abx_{i}"
  let ab_and := Wire.mk s!"{pfx}_aba_{i}"
  let c_ab := Wire.mk s!"{pfx}_cab_{i}"
  let sum_i := Wire.mk s!"{pfx}_sum_{i}"
  let c_out := Wire.mk s!"{pfx}_cout_{i}"
  ([Gate.mkXOR a b ab_xor,
    Gate.mkAND a b ab_and,
    Gate.mkXOR ab_xor cin sum_i,
    Gate.mkAND ab_xor cin c_ab,
    Gate.mkOR ab_and c_ab c_out], sum_i, c_out)

/-- Ripple carry adder for 64-bit addition/subtraction using foldl -/
private def mkAdder64 (pfx : String) (a b : List Wire) (cin : Wire) : (List Gate × List Wire × Wire) :=
  (List.range 64).foldl (fun (gates, sum_wires, c_in) i =>
    let (cell_gates, s, c_next) := mkFullAdderCell pfx i a[i]! b[i]! c_in
    (gates ++ cell_gates, sum_wires ++ [s], c_next)
  ) ([], [], cin)

/-- XOR reduction using foldl -/
private def mkXorTree (pfx : String) (wires : List Wire) : (List Gate × Wire) :=
  match wires with
  | [] => ([], Wire.mk "zero")
  | w :: ws =>
    ws.enum.foldl (fun (gates, acc) ⟨i, next_w⟩ =>
      let out := Wire.mk s!"{pfx}_x_{i}"
      (gates ++ [Gate.mkXOR acc next_w out], out)
    ) ([], w)

/-- OR reduction using foldl -/
private def mkOrTree (pfx : String) (wires : List Wire) : (List Gate × Wire) :=
  match wires with
  | [] => ([], Wire.mk "zero")
  | w :: ws =>
    ws.enum.foldl (fun (gates, acc) ⟨i, next_w⟩ =>
      let out := Wire.mk s!"{pfx}_o_{i}"
      (gates ++ [Gate.mkOR acc next_w out], out)
    ) ([], w)

/-- Build the Fallback Sequencer Circuit.

    Inputs:
    - clock, reset
    - start: trigger from decode (when fetch_valid && !io_valid)
    - insn[31:0]: captured instruction word
    - pc_in[63:0]: PC of the un-decoded instruction
    - rs1_val[63:0]: source operand 1
    - rs2_val[63:0]: source operand 2
    - rd_tag_in[5:0]: physical destination register tag
    - rob_empty: ROB drain complete
    - sb_empty: store buffer drain complete
    - wcs_write_en: TileLink WCS write strobe
    - wcs_write_addr[7:0]: TileLink WCS word address
    - wcs_write_data[31:0]: TileLink WCS write data
    - wcs_enable: enable WCS RAM mode
    - wcs_lock: sticky lock bit from WCS_CTRL

    Outputs:
    - active: sequencer running (suppresses fetch/decode)
    - cdb_inject: CDB write strobe
    - cdb_tag[5:0]: physical tag for PRF write
    - cdb_data[63:0]: result data for PRF write
    - redir_valid: fetch redirect strobe
    - redir_pc[63:0]: target PC (pc+4 on success, or mtvec on illegal trap)
    - trap_active: asserted when illegal instruction exception taken
    - trap_cause[63:0]: exception code (2 for illegal instruction)
    - trap_val[63:0]: faulting instruction word for mtval
    - wcs_busy: asserted when active (stalls TileLink WCS writes)
-/
def mkFallbackSequencer : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let start := Wire.mk "start"
  let pipeline_flush := Wire.mk "pipeline_flush"

  -- Inputs
  let insn_in := makeWires "insn" 32
  let pc_in := makeWires "pc_in" 64
  let rs1_in := makeWires "rs1_val" 64
  let rs2_in := makeWires "rs2_val" 64
  let rd_tag_in := makeWires "rd_tag_in" 6
  let rob_empty := Wire.mk "rob_empty"
  let sb_empty := Wire.mk "sb_empty"

  -- TileLink WCS interface
  let wcs_write_en := Wire.mk "wcs_write_en"
  let wcs_write_addr := makeWires "wcs_write_addr" 8
  let wcs_write_data := makeWires "wcs_write_data" 32
  let wcs_enable := Wire.mk "wcs_enable"
  let wcs_lock := Wire.mk "wcs_lock"

  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- Active state register
  let active_q := Wire.mk "active"
  let active_next := Wire.mk "active_next"
  let seq_done := Wire.mk "seq_done"
  let done_or_flush := Wire.mk "done_or_flush"
  let not_done_flush := Wire.mk "not_done_flush"
  let active_keep := Wire.mk "active_keep"

  let activeGates := [
    Gate.mkOR seq_done pipeline_flush done_or_flush,
    Gate.mkNOT done_or_flush not_done_flush,
    Gate.mkAND active_q not_done_flush active_keep,
    Gate.mkOR start active_keep active_next,
    Gate.mkDFF active_next clock reset active_q
  ]

  -- Pipeline drain synchronization: drained when rob_empty AND sb_empty
  -- Delay checking rob_empty by 2 cycles after start so in-flight instructions enter the ROB
  let drain_dly1_q := Wire.mk "drain_dly1_q"
  let drain_dly2_q := Wire.mk "drain_dly2_q"
  let drain_dly1_d := Wire.mk "drain_dly1_d"
  let drain_dly2_d := Wire.mk "drain_dly2_d"
  let drained := Wire.mk "drained"
  let drainGates := [
    Gate.mkAND active_q drain_dly1_q (Wire.mk "dd1_hold"),
    Gate.mkOR start (Wire.mk "dd1_hold") drain_dly1_d,
    Gate.mkDFF drain_dly1_d clock reset drain_dly1_q,
    Gate.mkAND active_q drain_dly1_q drain_dly2_d,
    Gate.mkDFF drain_dly2_d clock reset drain_dly2_q,
    Gate.mkAND rob_empty sb_empty (Wire.mk "rob_sb_empty"),
    Gate.mkAND (Wire.mk "rob_sb_empty") drain_dly2_q drained
  ]
  -- Capture registers for instruction, PC, operands, and rd tag
  let insn_q := makeWires "insn_q" 32
  let insn_d := makeWires "insn_d" 32
  let pc_q := makeWires "pc_q" 64
  let pc_d := makeWires "pc_d" 64
  let rs1_q := makeWires "rs1_q" 64
  let rs1_d := makeWires "rs1_d" 64
  let rs2_q := makeWires "rs2_q" 64
  let rs2_d := makeWires "rs2_d" 64
  let cdb_tag_q := makeWires "cdb_tag" 6
  let rd_tag_d := makeWires "rd_tag_d" 6

  let exec_step_next := Wire.mk "exec_step_next"
  let op_latch := Wire.mk "op_latch"
  let captureGates := [
    Gate.mkOR start exec_step_next op_latch
  ] ++
    (List.range 32).map (fun i => Gate.mkMUX insn_q[i]! insn_in[i]! start insn_d[i]!) ++
    (List.range 64).map (fun i => Gate.mkMUX pc_q[i]! pc_in[i]! start pc_d[i]!) ++
    (List.range 64).map (fun i => Gate.mkMUX rs1_q[i]! rs1_in[i]! op_latch rs1_d[i]!) ++
    (List.range 64).map (fun i => Gate.mkMUX rs2_q[i]! rs2_in[i]! op_latch rs2_d[i]!) ++
    (List.range 6).map (fun i => Gate.mkMUX cdb_tag_q[i]! rd_tag_in[i]! start rd_tag_d[i]!)

  let captureRegs : List CircuitInstance := [
    { moduleName := "Register32", instName := "u_cap_insn",
      portMap := (insn_d.enum.map fun ⟨i, w⟩ => (s!"d_{i}", w)) ++
                 [("clock", clock), ("reset", reset)] ++
                 (insn_q.enum.map fun ⟨i, w⟩ => (s!"q_{i}", w)) },
    { moduleName := "Register64", instName := "u_cap_pc",
      portMap := (pc_d.enum.map fun ⟨i, w⟩ => (s!"d_{i}", w)) ++
                 [("clock", clock), ("reset", reset)] ++
                 (pc_q.enum.map fun ⟨i, w⟩ => (s!"q_{i}", w)) },
    { moduleName := "Register64", instName := "u_cap_rs1",
      portMap := (rs1_d.enum.map fun ⟨i, w⟩ => (s!"d_{i}", w)) ++
                 [("clock", clock), ("reset", reset)] ++
                 (rs1_q.enum.map fun ⟨i, w⟩ => (s!"q_{i}", w)) },
    { moduleName := "Register64", instName := "u_cap_rs2",
      portMap := (rs2_d.enum.map fun ⟨i, w⟩ => (s!"d_{i}", w)) ++
                 [("clock", clock), ("reset", reset)] ++
                 (rs2_q.enum.map fun ⟨i, w⟩ => (s!"q_{i}", w)) },
    { moduleName := "Register6", instName := "u_cap_rdtag",
      portMap := (rd_tag_d.enum.map fun ⟨i, w⟩ => (s!"d_{i}", w)) ++
                 [("clock", clock), ("reset", reset)] ++
                 (cdb_tag_q.enum.map fun ⟨i, w⟩ => (s!"q_{i}", w)) }
  ]

  -- 1-cycle execution pulse once drained
  let exec_step_q := Wire.mk "exec_step_q"
  let not_exec := Wire.mk "not_exec"
  let stepGates := [
    Gate.mkNOT exec_step_q not_exec,
    Gate.mkAND active_q drained (Wire.mk "act_drained"),
    Gate.mkAND (Wire.mk "act_drained") not_exec exec_step_next,
    Gate.mkDFF exec_step_next clock reset exec_step_q
  ]

  -- === INSTRUCTION DECODING ===
  let is_op_33 := Wire.mk "is_op_33"
  let opGates := [
    Gate.mkAND insn_q[0]! insn_q[1]! (Wire.mk "op_b01"),
    Gate.mkNOT insn_q[2]! (Wire.mk "op_nb2"),
    Gate.mkNOT insn_q[3]! (Wire.mk "op_nb3"),
    Gate.mkAND (Wire.mk "op_nb2") (Wire.mk "op_nb3") (Wire.mk "op_b23"),
    Gate.mkAND (Wire.mk "op_b01") (Wire.mk "op_b23") (Wire.mk "op_low4"),
    -- 0x33: bit6=0, bit5=1, bit4=1
    Gate.mkNOT insn_q[6]! (Wire.mk "op_nb6"),
    Gate.mkAND insn_q[5]! insn_q[4]! (Wire.mk "op_b54_33"),
    Gate.mkAND (Wire.mk "op_nb6") (Wire.mk "op_b54_33") (Wire.mk "op_hi3_33"),
    Gate.mkAND (Wire.mk "op_low4") (Wire.mk "op_hi3_33") is_op_33
  ]

  -- Funct3 decode (bits 14:12)
  let f3_b0 := insn_q[12]!
  let f3_b1 := insn_q[13]!
  let f3_b2 := insn_q[14]!
  let nf3_b0 := Wire.mk "nf3_b0"
  let nf3_b1 := Wire.mk "nf3_b1"
  let nf3_b2 := Wire.mk "nf3_b2"
  let f3InvGates := [
    Gate.mkNOT f3_b0 nf3_b0,
    Gate.mkNOT f3_b1 nf3_b1,
    Gate.mkNOT f3_b2 nf3_b2
  ]

  let is_f3_1 := Wire.mk "is_f3_1" -- 001
  let is_f3_2 := Wire.mk "is_f3_2" -- 010
  let is_f3_4 := Wire.mk "is_f3_4" -- 100
  let is_f3_5 := Wire.mk "is_f3_5" -- 101
  let is_f3_6 := Wire.mk "is_f3_6" -- 110
  let is_f3_7 := Wire.mk "is_f3_7" -- 111

  let f3DecGates := [
    Gate.mkAND nf3_b2 nf3_b1 (Wire.mk "f3_00x"),
    Gate.mkAND (Wire.mk "f3_00x") f3_b0 is_f3_1,

    Gate.mkAND nf3_b2 f3_b1 (Wire.mk "f3_01x"),
    Gate.mkAND (Wire.mk "f3_01x") nf3_b0 is_f3_2,

    Gate.mkAND f3_b2 nf3_b1 (Wire.mk "f3_10x"),
    Gate.mkAND (Wire.mk "f3_10x") nf3_b0 is_f3_4,
    Gate.mkAND (Wire.mk "f3_10x") f3_b0 is_f3_5,

    Gate.mkAND f3_b2 f3_b1 (Wire.mk "f3_11x"),
    Gate.mkAND (Wire.mk "f3_11x") nf3_b0 is_f3_6,
    Gate.mkAND (Wire.mk "f3_11x") f3_b0 is_f3_7
  ]

  -- Funct7 decode (bits 31:25)
  -- 0x10 = 0010000 (bit 4)
  -- 0x14 = 0010100 (bits 4, 2)
  -- 0x20 = 0100000 (bit 5)
  -- 0x24 = 0100100 (bits 5, 2)
  -- 0x30 = 0110000 (bits 5, 4)
  -- 0x34 = 0110100 (bits 5, 4, 2)
  -- 0x05 = 0000101 (bits 2, 0)
  let f7 := (List.range 7).map (fun i => insn_q[25+i]!)
  let nf7 := (List.range 7).map (fun i => Wire.mk s!"nf7_{i}")
  let f7InvGates := (List.range 7).map (fun i => Gate.mkNOT f7[i]! nf7[i]!)

  let is_f7_10 := Wire.mk "is_f7_10"
  let is_f7_14 := Wire.mk "is_f7_14"
  let is_f7_20 := Wire.mk "is_f7_20"
  let is_f7_24 := Wire.mk "is_f7_24"
  let is_f7_30 := Wire.mk "is_f7_30"
  let is_f7_34 := Wire.mk "is_f7_34"
  let is_f7_05 := Wire.mk "is_f7_05"

  -- Helper to decode 7-bit patterns
  let mkF7Match (name : String) (pat : List Bool) (out : Wire) : List Gate :=
    let b := (List.range 7).map fun i => if pat[i]! then f7[i]! else nf7[i]!
    let w01 := Wire.mk s!"{name}_01"
    let w23 := Wire.mk s!"{name}_23"
    let w45 := Wire.mk s!"{name}_45"
    let w03 := Wire.mk s!"{name}_03"
    let w05 := Wire.mk s!"{name}_05"
    [Gate.mkAND b[0]! b[1]! w01,
     Gate.mkAND b[2]! b[3]! w23,
     Gate.mkAND b[4]! b[5]! w45,
     Gate.mkAND w01 w23 w03,
     Gate.mkAND w03 w45 w05,
     Gate.mkAND w05 b[6]! out]

  let f7DecGates :=
    mkF7Match "f7_10" [false, false, false, false, true, false, false] is_f7_10 ++
    mkF7Match "f7_14" [false, false, true, false, true, false, false] is_f7_14 ++
    mkF7Match "f7_20" [false, false, false, false, false, true, false] is_f7_20 ++
    mkF7Match "f7_24" [false, false, true, false, false, true, false] is_f7_24 ++
    mkF7Match "f7_30" [false, false, false, false, true, true, false] is_f7_30 ++
    mkF7Match "f7_34" [false, false, true, false, true, true, false] is_f7_34 ++
    mkF7Match "f7_05" [true, false, true, false, false, false, false] is_f7_05

  -- Individual instruction matching
  let is_sh1add := Wire.mk "is_sh1add"
  let is_sh2add := Wire.mk "is_sh2add"
  let is_sh3add := Wire.mk "is_sh3add"
  let is_shadd := Wire.mk "is_shadd"

  let is_bset := Wire.mk "is_bset"
  let is_bclr := Wire.mk "is_bclr"
  let is_binv := Wire.mk "is_binv"
  let is_bext := Wire.mk "is_bext"

  let is_andn := Wire.mk "is_andn"
  let is_orn  := Wire.mk "is_orn"
  let is_xnor := Wire.mk "is_xnor"

  let is_min  := Wire.mk "is_min"
  let is_max  := Wire.mk "is_max"
  let is_minu := Wire.mk "is_minu"
  let is_maxu := Wire.mk "is_maxu"

  let is_rol  := Wire.mk "is_rol"
  let is_ror  := Wire.mk "is_ror"
  let is_clmul := Wire.mk "is_clmul"

  let insnMatchGates := [
    -- Zba: sh1add, sh2add, sh3add
    Gate.mkAND is_op_33 is_f7_10 (Wire.mk "op_f7_10"),
    Gate.mkAND (Wire.mk "op_f7_10") is_f3_2 is_sh1add,
    Gate.mkAND (Wire.mk "op_f7_10") is_f3_4 is_sh2add,
    Gate.mkAND (Wire.mk "op_f7_10") is_f3_6 is_sh3add,
    Gate.mkOR is_sh1add is_sh2add (Wire.mk "sh12add"),
    Gate.mkOR (Wire.mk "sh12add") is_sh3add is_shadd,

    -- Zbs: bset, bclr, binv, bext
    Gate.mkAND is_op_33 is_f7_14 (Wire.mk "op_f7_14"),
    Gate.mkAND (Wire.mk "op_f7_14") is_f3_1 is_bset,
    Gate.mkAND is_op_33 is_f7_24 (Wire.mk "op_f7_24"),
    Gate.mkAND (Wire.mk "op_f7_24") is_f3_1 is_bclr,
    Gate.mkAND (Wire.mk "op_f7_24") is_f3_5 is_bext,
    Gate.mkAND is_op_33 is_f7_34 (Wire.mk "op_f7_34"),
    Gate.mkAND (Wire.mk "op_f7_34") is_f3_1 is_binv,

    -- Zbb logic: andn, orn, xnor
    Gate.mkAND is_op_33 is_f7_20 (Wire.mk "op_f7_20"),
    Gate.mkAND (Wire.mk "op_f7_20") is_f3_7 is_andn,
    Gate.mkAND (Wire.mk "op_f7_20") is_f3_6 is_orn,
    Gate.mkAND (Wire.mk "op_f7_20") is_f3_4 is_xnor,

    -- Zbb min/max: funct3 MIN=4, MAX=6, MINU=5, MAXU=7
    Gate.mkAND is_op_33 is_f7_05 (Wire.mk "op_f7_05"),
    Gate.mkAND (Wire.mk "op_f7_05") is_f3_4 is_min,
    Gate.mkAND (Wire.mk "op_f7_05") is_f3_6 is_max,
    Gate.mkAND (Wire.mk "op_f7_05") is_f3_5 is_minu,
    Gate.mkAND (Wire.mk "op_f7_05") is_f3_7 is_maxu,

    -- Zbb rotates
    Gate.mkAND is_op_33 is_f7_30 (Wire.mk "op_f7_30"),
    Gate.mkAND (Wire.mk "op_f7_30") is_f3_1 is_rol,
    Gate.mkAND (Wire.mk "op_f7_30") is_f3_5 is_ror,

    -- Zbc carry-less multiply
    Gate.mkAND (Wire.mk "op_f7_05") is_f3_1 is_clmul
  ]

  -- Overall zb_matched signal
  let zb_matched := Wire.mk "zb_matched"
  let not_zb_matched := Wire.mk "not_zb_matched"
  let (orZbGates, zb_any) := mkOrTree "zb_match" [
    is_shadd, is_bset, is_bclr, is_binv, is_bext,
    is_andn, is_orn, is_xnor,
    is_min, is_max, is_minu, is_maxu,
    is_rol, is_ror, is_clmul
  ]
  let zbMatchGates := orZbGates ++ [
    Gate.mkBUF zb_any zb_matched,
    Gate.mkNOT zb_matched not_zb_matched
  ]

  -- === MICRO-ALU COMPUTATIONS ===

  -- 1. Zba: sh1add, sh2add, sh3add
  let sh_rs1 := makeWires "sh_rs1" 64
  let shMuxGates := (List.range 64).flatMap fun i =>
    let s1 := if i >= 1 then rs1_q[i-1]! else zero
    let s2 := if i >= 2 then rs1_q[i-2]! else zero
    let s3 := if i >= 3 then rs1_q[i-3]! else zero
    let tmp := Wire.mk s!"sh_tmp_{i}"
    [Gate.mkMUX s1 s2 is_sh2add tmp,
     Gate.mkMUX tmp s3 is_sh3add sh_rs1[i]!]

  let (shaddAdderGates, shadd_val, _) := mkAdder64 "shadd" sh_rs1 rs2_q zero

  -- 2. Zbb Logic: andn, orn, xnor
  let andn_val := makeWires "andn_val" 64
  let orn_val  := makeWires "orn_val" 64
  let xnor_val := makeWires "xnor_val" 64
  let logicGates := (List.range 64).flatMap fun i =>
    let n_rs2 := Wire.mk s!"n_rs2_{i}"
    let x_rs := Wire.mk s!"x_rs_{i}"
    [Gate.mkNOT rs2_q[i]! n_rs2,
     Gate.mkAND rs1_q[i]! n_rs2 andn_val[i]!,
     Gate.mkOR rs1_q[i]! n_rs2 orn_val[i]!,
     Gate.mkXOR rs1_q[i]! rs2_q[i]! x_rs,
     Gate.mkNOT x_rs xnor_val[i]!]

  -- 3. Zbs Single-bit: bset, bclr, binv, bext
  let n_shamt := (List.range 6).map fun i => Wire.mk s!"n_shamt_{i}"
  let shamtInvGates := (List.range 6).map fun i => Gate.mkNOT rs2_q[i]! n_shamt[i]!

  let bit_mask := makeWires "bit_mask" 64
  let maskGates := (List.range 64).flatMap fun k =>
    let b0 := if k % 2 == 1 then rs2_q[0]! else n_shamt[0]!
    let b1 := if (k / 2) % 2 == 1 then rs2_q[1]! else n_shamt[1]!
    let b2 := if (k / 4) % 2 == 1 then rs2_q[2]! else n_shamt[2]!
    let b3 := if (k / 8) % 2 == 1 then rs2_q[3]! else n_shamt[3]!
    let b4 := if (k / 16) % 2 == 1 then rs2_q[4]! else n_shamt[4]!
    let b5 := if (k / 32) % 2 == 1 then rs2_q[5]! else n_shamt[5]!
    let t01 := Wire.mk s!"bm_t01_{k}"
    let t23 := Wire.mk s!"bm_t23_{k}"
    let t45 := Wire.mk s!"bm_t45_{k}"
    let t03 := Wire.mk s!"bm_t03_{k}"
    [Gate.mkAND b0 b1 t01,
     Gate.mkAND b2 b3 t23,
     Gate.mkAND b4 b5 t45,
     Gate.mkAND t01 t23 t03,
     Gate.mkAND t03 t45 bit_mask[k]!]

  let bset_val := makeWires "bset_val" 64
  let bclr_val := makeWires "bclr_val" 64
  let binv_val := makeWires "binv_val" 64
  let bext_terms := makeWires "bext_term" 64
  let zbsOpGates := (List.range 64).flatMap fun i =>
    let n_mask := Wire.mk s!"n_mask_{i}"
    [Gate.mkOR rs1_q[i]! bit_mask[i]! bset_val[i]!,
     Gate.mkNOT bit_mask[i]! n_mask,
     Gate.mkAND rs1_q[i]! n_mask bclr_val[i]!,
     Gate.mkXOR rs1_q[i]! bit_mask[i]! binv_val[i]!,
     Gate.mkAND rs1_q[i]! bit_mask[i]! bext_terms[i]!]

  let (bextOrGates, bext_bit) := mkOrTree "bext" bext_terms
  let bext_val := makeWires "bext_val" 64
  let bextGates := bextOrGates ++
    [Gate.mkBUF bext_bit bext_val[0]!] ++
    (List.range 63).map (fun i => Gate.mkBUF zero bext_val[i+1]!)

  -- 4. Zbb: min, max, minu, maxu
  let not_rs2_sub := makeWires "not_rs2_sub" 64
  let subInvGates := (List.range 64).map fun i => Gate.mkNOT rs2_q[i]! not_rs2_sub[i]!
  let (subGates, _, cout_sub) := mkAdder64 "sub" rs1_q not_rs2_sub one

  let rs1_lt_u := Wire.mk "rs1_lt_u"
  let rs1_lt_s := Wire.mk "rs1_lt_s"
  let diff_sign := Wire.mk "diff_sign"
  let cmpGates := [
    Gate.mkNOT cout_sub rs1_lt_u,
    Gate.mkXOR rs1_q[63]! rs2_q[63]! diff_sign,
    Gate.mkMUX rs1_lt_u rs1_q[63]! diff_sign rs1_lt_s
  ]

  let min_val  := makeWires "min_val" 64
  let max_val  := makeWires "max_val" 64
  let minu_val := makeWires "minu_val" 64
  let maxu_val := makeWires "maxu_val" 64
  let minMaxGates := (List.range 64).flatMap fun i =>
    [Gate.mkMUX rs2_q[i]! rs1_q[i]! rs1_lt_s min_val[i]!,
     Gate.mkMUX rs1_q[i]! rs2_q[i]! rs1_lt_s max_val[i]!,
     Gate.mkMUX rs2_q[i]! rs1_q[i]! rs1_lt_u minu_val[i]!,
     Gate.mkMUX rs1_q[i]! rs2_q[i]! rs1_lt_u maxu_val[i]!]

  -- 5. Zbb: ror, rol (6-stage barrel rotators)
  -- ROR (rotate right by rs2_q[5:0])
  let ror_s0 := makeWires "ror_s0" 64
  let ror_s1 := makeWires "ror_s1" 64
  let ror_s2 := makeWires "ror_s2" 64
  let ror_s3 := makeWires "ror_s3" 64
  let ror_s4 := makeWires "ror_s4" 64
  let ror_val := makeWires "ror_val" 64
  let rorGates :=
    (List.range 64).map (fun i => Gate.mkMUX rs1_q[i]! rs1_q[(i+1)%64]! rs2_q[0]! ror_s0[i]!) ++
    (List.range 64).map (fun i => Gate.mkMUX ror_s0[i]! ror_s0[(i+2)%64]! rs2_q[1]! ror_s1[i]!) ++
    (List.range 64).map (fun i => Gate.mkMUX ror_s1[i]! ror_s1[(i+4)%64]! rs2_q[2]! ror_s2[i]!) ++
    (List.range 64).map (fun i => Gate.mkMUX ror_s2[i]! ror_s2[(i+8)%64]! rs2_q[3]! ror_s3[i]!) ++
    (List.range 64).map (fun i => Gate.mkMUX ror_s3[i]! ror_s3[(i+16)%64]! rs2_q[4]! ror_s4[i]!) ++
    (List.range 64).map (fun i => Gate.mkMUX ror_s4[i]! ror_s4[(i+32)%64]! rs2_q[5]! ror_val[i]!)

  -- ROL (rotate left by rs2_q[5:0])
  let rol_s0 := makeWires "rol_s0" 64
  let rol_s1 := makeWires "rol_s1" 64
  let rol_s2 := makeWires "rol_s2" 64
  let rol_s3 := makeWires "rol_s3" 64
  let rol_s4 := makeWires "rol_s4" 64
  let rol_val := makeWires "rol_val" 64
  let rolGates :=
    (List.range 64).map (fun i => Gate.mkMUX rs1_q[i]! rs1_q[(i+64-1)%64]! rs2_q[0]! rol_s0[i]!) ++
    (List.range 64).map (fun i => Gate.mkMUX rol_s0[i]! rol_s0[(i+64-2)%64]! rs2_q[1]! rol_s1[i]!) ++
    (List.range 64).map (fun i => Gate.mkMUX rol_s1[i]! rol_s1[(i+64-4)%64]! rs2_q[2]! rol_s2[i]!) ++
    (List.range 64).map (fun i => Gate.mkMUX rol_s2[i]! rol_s2[(i+64-8)%64]! rs2_q[3]! rol_s3[i]!) ++
    (List.range 64).map (fun i => Gate.mkMUX rol_s3[i]! rol_s3[(i+64-16)%64]! rs2_q[4]! rol_s4[i]!) ++
    (List.range 64).map (fun i => Gate.mkMUX rol_s4[i]! rol_s4[(i+64-32)%64]! rs2_q[5]! rol_val[i]!)

  -- 6. Zbc: clmul (carry-less multiplication)
  let clmul_val := makeWires "clmul_val" 64
  let clmulGates := (List.range 64).flatMap fun i =>
    let and_terms := (List.range (i + 1)).map fun j =>
      let and_w := Wire.mk s!"clm_{i}_{j}"
      (Gate.mkAND rs1_q[i-j]! rs2_q[j]! and_w, and_w)
    let agates := and_terms.map (·.1)
    let awires := and_terms.map (·.2)
    let (xgates, xout) := mkXorTree s!"clmx_{i}" awires
    agates ++ xgates ++ [Gate.mkBUF xout clmul_val[i]!]

  -- === RESULT MULTIPLEXER TREE ===
  let cdb_data_out := makeWires "cdb_data" 64

  -- Build priority selection:
  -- Stage 0: default zero
  -- MUX with shadd_val on is_shadd
  -- MUX with andn_val on is_andn
  -- MUX with orn_val on is_orn
  -- MUX with xnor_val on is_xnor
  -- MUX with bset_val on is_bset
  -- MUX with bclr_val on is_bclr
  -- MUX with binv_val on is_binv
  -- MUX with bext_val on is_bext
  -- MUX with min_val on is_min
  -- MUX with max_val on is_max
  -- MUX with minu_val on is_minu
  -- MUX with maxu_val on is_maxu
  -- MUX with ror_val on is_ror
  -- MUX with rol_val on is_rol
  -- MUX with clmul_val on is_clmul
  let opSelections : List (Wire × List Wire) := [
    (is_shadd, shadd_val),
    (is_andn, andn_val),
    (is_orn, orn_val),
    (is_xnor, xnor_val),
    (is_bset, bset_val),
    (is_bclr, bclr_val),
    (is_binv, binv_val),
    (is_bext, bext_val),
    (is_min, min_val),
    (is_max, max_val),
    (is_minu, minu_val),
    (is_maxu, maxu_val),
    (is_ror, ror_val),
    (is_rol, rol_val),
    (is_clmul, clmul_val)
  ]

  let (muxGates, final_wires) :=
    (List.range opSelections.length).foldl (fun (accGates, prev) idx =>
      let (sel, vals) := opSelections[idx]!
      let next_w := makeWires s!"rmux_{idx}" 64
      let g := (List.range 64).map fun i =>
        Gate.mkMUX prev[i]! vals[i]! sel next_w[i]!
      (accGates ++ g, next_w)
    ) ([], List.replicate 64 zero)
  let resultMuxGates := muxGates ++ (List.range 64).map (fun i => Gate.mkBUF final_wires[i]! cdb_data_out[i]!)

  -- WCS handshake logic: write allowed if write_en AND NOT(wcs_lock)
  let not_wcs_lock := Wire.mk "not_wcs_lock"
  let wcs_wr_allowed := Wire.mk "wcs_wr_allowed"
  let wcsGates := [
    Gate.mkNOT wcs_lock not_wcs_lock,
    Gate.mkAND wcs_write_en not_wcs_lock wcs_wr_allowed,
    Gate.mkAND wcs_wr_allowed wcs_enable (Wire.mk "wcs_ram_write_en")
  ] ++
  (List.range 8).map (fun i => Gate.mkBUF wcs_write_addr[i]! (Wire.mk s!"wcs_addr_buf_{i}")) ++
  (List.range 32).map (fun i => Gate.mkBUF wcs_write_data[i]! (Wire.mk s!"wcs_data_buf_{i}"))

  -- Control Outputs
  let cdb_inject := Wire.mk "cdb_inject"
  let redir_valid := Wire.mk "redir_valid"
  let trap_active := Wire.mk "trap_active"
  let wcs_busy := Wire.mk "wcs_busy"
  let seq_live := Wire.mk "seq_live"

  let ctrlGates := [
    -- Sequence completes when exec_step_q is high
    Gate.mkBUF exec_step_q seq_done,
    -- A redirect that flushes the sequencer clears active_q, but the DFF'd
    -- exec_step_q stays high one more cycle.  Gate the completion strobes with
    -- active_q so a flushed (squashed) sequence cannot inject its result or
    -- override the redirect that flushed it.
    Gate.mkAND active_q exec_step_q seq_live,
    -- cdb_inject fires on completion if matched and not illegal
    Gate.mkAND seq_live zb_matched cdb_inject,
    -- redir_valid fires on completion IF matched
    Gate.mkAND seq_live zb_matched redir_valid,
    -- trap_active fires if unhandled instruction completes
    Gate.mkAND seq_live not_zb_matched trap_active,
    -- wcs_busy is high whenever sequencer is active
    Gate.mkBUF active_q wcs_busy
  ]

  -- Redirection PC: PC + 4 on success
  let redir_pc_out := makeWires "redir_pc" 64
  let c4_vec := (List.range 64).map fun i => if i == 2 then one else zero
  let (pc4ExactGates, pc_plus_4_exact, _) := mkAdder64 "pc4" pc_q c4_vec zero
  let redirMuxGates := (List.range 64).map fun i =>
    Gate.mkBUF pc_plus_4_exact[i]! redir_pc_out[i]!

  -- Trap Cause: 2 for illegal instruction
  let trap_cause_out := makeWires "trap_cause" 64
  let trapCauseGates := (List.range 64).map fun i =>
    if i == 1 then Gate.mkBUF one trap_cause_out[i]!
    else Gate.mkBUF zero trap_cause_out[i]!

  -- Trap Val: faulting instruction word
  let trap_val_out := makeWires "trap_val" 64
  let trapValGates := (List.range 64).map fun i =>
    if i < 32 then Gate.mkBUF insn_q[i]! trap_val_out[i]!
    else Gate.mkBUF zero trap_val_out[i]!

  let allGates :=
    activeGates ++ drainGates ++ captureGates ++ stepGates ++
    opGates ++ f3InvGates ++ f3DecGates ++ f7InvGates ++ f7DecGates ++ insnMatchGates ++
    zbMatchGates ++ wcsGates ++
    shMuxGates ++ shaddAdderGates ++
    logicGates ++
    shamtInvGates ++ maskGates ++ zbsOpGates ++ bextGates ++
    subInvGates ++ subGates ++ cmpGates ++ minMaxGates ++
    rorGates ++ rolGates ++
    clmulGates ++
    resultMuxGates ++
    ctrlGates ++ pc4ExactGates ++ redirMuxGates ++ trapCauseGates ++ trapValGates

  let allInstances := captureRegs

  { name := "FallbackSequencer"
    inputs := [clock, reset, start, pipeline_flush] ++
              insn_in ++ pc_in ++ rs1_in ++ rs2_in ++ rd_tag_in ++
              [rob_empty, sb_empty, wcs_write_en] ++
              wcs_write_addr ++ wcs_write_data ++ [wcs_enable, wcs_lock]
    outputs := [active_q, cdb_inject, redir_valid, trap_active, wcs_busy] ++
               cdb_tag_q ++ cdb_data_out ++ redir_pc_out ++ trap_cause_out ++ trap_val_out
    gates := allGates
    instances := allInstances
    signalGroups := [
      { name := "insn", width := 32, wires := insn_in },
      { name := "pc_in", width := 64, wires := pc_in },
      { name := "rs1_val", width := 64, wires := rs1_in },
      { name := "rs2_val", width := 64, wires := rs2_in },
      { name := "rd_tag_in", width := 6, wires := rd_tag_in },
      { name := "wcs_write_addr", width := 8, wires := wcs_write_addr },
      { name := "wcs_write_data", width := 32, wires := wcs_write_data },
      { name := "cdb_tag", width := 6, wires := cdb_tag_q },
      { name := "cdb_data", width := 64, wires := cdb_data_out },
      { name := "redir_pc", width := 64, wires := redir_pc_out },
      { name := "trap_cause", width := 64, wires := trap_cause_out },
      { name := "trap_val", width := 64, wires := trap_val_out }
    ] }

def fallbackSequencerCircuit : Circuit := mkFallbackSequencer

end Shoumei.RISCV.Microcode

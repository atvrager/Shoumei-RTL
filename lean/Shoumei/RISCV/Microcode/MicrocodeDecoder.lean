/-
Microcode Decoder - Combinational circuit: 4-bit opcode → 11 one-hot control signals

Input: opcode[3:0] (from ROM entry)
Output: 11 one-hot signals, one per MicroOp
-/

import Shoumei.DSL
import Shoumei.RISCV.Microcode.MicrocodeTypes

namespace Shoumei.RISCV.Microcode

open Shoumei

/-- Build the microcode decoder circuit: 4-bit input → 11 one-hot outputs.
    Each output is high when the input matches that µop's encoding. -/
def mkMicrocodeDecoder : Circuit :=
  let opcode := (List.range 4).map (fun i => Wire.mk s!"opcode_{i}")
  let n_opcode := (List.range 4).map (fun i => Wire.mk s!"n_opcode_{i}")

  -- Invert each opcode bit
  let notGates := (List.range 4).map (fun i =>
    Gate.mkNOT opcode[i]! n_opcode[i]!)

  -- For each µop encoding, generate a 4-input AND (via 2-level tree)
  let mkMatch (enc : Nat) (name : String) : Wire × List Gate :=
    let outW := Wire.mk name
    let b := (List.range 4).map (fun i =>
      if Nat.testBit enc i then opcode[i]! else n_opcode[i]!)
    let t01 := Wire.mk s!"{name}_t01"
    let t23 := Wire.mk s!"{name}_t23"
    (outW, [Gate.mkAND b[0]! b[1]! t01,
            Gate.mkAND b[2]! b[3]! t23,
            Gate.mkAND t01 t23 outW])

  let ops := [
    (MicroOp.DRAIN.toNat, "is_drain"),
    (MicroOp.DRAIN_SB.toNat, "is_drain_sb"),
    (MicroOp.READ_CSR.toNat, "is_read_csr"),
    (MicroOp.WRITE_CSR.toNat, "is_write_csr"),
    (MicroOp.MOV_TO_RD.toNat, "is_mov_to_rd"),
    (MicroOp.ALU_MOV.toNat, "is_alu_mov"),
    (MicroOp.ALU_OR.toNat, "is_alu_or"),
    (MicroOp.ALU_ANDN.toNat, "is_alu_andn"),
    (MicroOp.FLUSH_FETCH.toNat, "is_flush_fetch"),
    (MicroOp.SET_PC.toNat, "is_set_pc"),
    (MicroOp.DONE.toNat, "is_done")
  ]

  let matchResults := ops.map (fun (enc, name) => mkMatch enc name)
  let outputWires := matchResults.map (·.1)
  let matchGates := matchResults.map (·.2) |>.flatten

  { name := "MicrocodeDecoder"
    inputs := opcode
    outputs := outputWires
    gates := notGates ++ matchGates
    instances := [] }

end Shoumei.RISCV.Microcode

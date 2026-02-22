/-
  CPUCircuitHelpers.lean — Extracted from CPU.lean

  Contains structural circuit helper functions used by mkCPU:
  mkOpTypeToALU4, aluMappingByName, mulDivMappingByName, mkOpTypeLUT,
  fpuMappingByName, mkMux64to1, mkBusyBitTable, mkOpcodeMatch6,
  mkBranchResolve, mkShadowRegisters, mkFPFlags, mkCommitControl,
  mkCDBForwardInt, mkCDBForwardFP, mkSidecarRegFile4x32.
-/
import Shoumei.DSL
import Shoumei.RISCV.Config
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Sequential.Register

namespace Shoumei.RISCV.CPU

open Shoumei
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential

/-- Helper: Create indexed wires -/
def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

/-- Helper: Create bundled I/O port map entries for modules with >200 ports -/
def bundledPorts (portName : String) (wires : List Wire) : List (String × Wire) :=
  wires.enum.map (fun ⟨i, w⟩ => (s!"{portName}_{i}", w))

/-! ## Width-generic helpers for W-wide superscalar pipelines -/

/-- Generate W copies of a wire bus: prefix_0[bits-1:0], prefix_1[bits-1:0], ... -/
def mkSlotBus (pfxName : String) (bits : Nat) (W : Nat) : List (List Wire) :=
  (List.range W).map (fun slot => makeIndexedWires s!"{pfxName}_{slot}" bits)

/-- Generate W single wires: name_0, name_1, ... -/
def mkSlotWires (name : String) (W : Nat) : List Wire :=
  (List.range W).map fun s => Wire.mk s!"{name}_{s}"

/-- Port mappings for slot s of a multi-slot bus -/
def slotBundledPorts (portPrefix : String) (s : Nat) (wires : List Wire) : List (String × Wire) :=
  bundledPorts s!"{portPrefix}_{s}" wires

/-- Build an OR-tree over a list of wires. Returns (gates, output_wire).
    Empty list → BUF zero to output. Single wire → BUF to output. -/
def mkOrTree (pfx : String) (wires : List Wire) (output : Wire) (zero : Wire := Wire.mk "zero") : List Gate :=
  match wires with
  | [] => [Gate.mkBUF zero output]
  | [w] => [Gate.mkBUF w output]
  | w0 :: w1 :: rest =>
    let first := Wire.mk s!"{pfx}_or0"
    let firstGate := Gate.mkOR w0 w1 first
    let (gates, _) := rest.enum.foldl (fun (acc, prev) ⟨idx, w⟩ =>
      let isLast := idx == rest.length - 1
      let next := if isLast then output else Wire.mk s!"{pfx}_or{idx+1}"
      (acc ++ [Gate.mkOR prev w next], next)
    ) ([firstGate], first)
    gates

/-- Build an AND-chain over a list of wires. Returns (gates, output_wire). -/
def mkAndChain (pfx : String) (wires : List Wire) (output : Wire) (one : Wire := Wire.mk "one") : List Gate :=
  match wires with
  | [] => [Gate.mkBUF one output]
  | [w] => [Gate.mkBUF w output]
  | w0 :: w1 :: rest =>
    let first := Wire.mk s!"{pfx}_and0"
    let firstGate := Gate.mkAND w0 w1 first
    let (gates, _) := rest.enum.foldl (fun (acc, prev) ⟨idx, w⟩ =>
      let isLast := idx == rest.length - 1
      let next := if isLast then output else Wire.mk s!"{pfx}_and{idx+1}"
      (acc ++ [Gate.mkAND prev w next], next)
    ) ([firstGate], first)
    gates

/-- For entry i with W alloc/commit decoders, generate OR of (enable_s AND decoder_s[i]).
    Returns (gates, output_wire) where output is true if any slot targets entry i. -/
def mkMultiSlotMatch (pfx : String) (W : Nat) (enables : List Wire)
    (decodedBits : List Wire) (output : Wire) (zero : Wire := Wire.mk "zero") : List Gate :=
  let terms := (List.range W).map fun s =>
    let t := Wire.mk s!"{pfx}_s{s}"
    (Gate.mkAND enables[s]! decodedBits[s]! t, t)
  let termGates := terms.map Prod.fst
  let termWires := terms.map Prod.snd
  termGates ++ mkOrTree s!"{pfx}" termWires output zero

/-- Priority MUX cascade: for W data sources with W enables, select highest-priority matching.
    Slot 0 has lowest priority, slot W-1 has highest (last writer wins).
    Returns (gates) that drive output wires. -/
def mkPriorityMuxCascade (pfx : String) (W : Nat) (enables : List Wire)
    (dataSources : List (List Wire)) (output : List Wire) : List Gate :=
  if W == 0 then []
  else if W == 1 then
    (List.range output.length).map fun b =>
      Gate.mkBUF dataSources[0]![b]! output[b]!
  else
    -- Start from slot 0 data, then MUX in each higher slot if its enable is set
    let width := output.length
    let initWires := dataSources[0]!
    let (allGates, _) := (List.range (W - 1)).foldl (fun (accGates, prevWires) idx =>
      let s := idx + 1
      let isLast := s == W - 1
      let nextWires := if isLast then output
                       else makeIndexedWires s!"{pfx}_pmux_s{s}" width
      let muxGates := (List.range width).map fun b =>
        Gate.mkMUX prevWires[b]! dataSources[s]![b]! enables[s]! nextWires[b]!
      (accGates ++ muxGates, nextWires)
    ) ([], initWires)
    allGates

/-- Generate gates for 6-bit OpType dispatch code → 4-bit ALU opcode translation.

    Takes the RS dispatch opcode (6-bit OpType encoding from decoder) and produces
    the 4-bit ALU opcode expected by IntegerExecUnit / ALU32.

    Implemented as AND-OR logic: for each output bit, OR together product terms
    matching the input encodings that should set that bit.

    Parameters:
    - prefix: Wire name prefix (for unique naming in multi-instance circuits)
    - optype: 6-bit OpType dispatch code from RS
    - aluOp: 4-bit ALU opcode output
    - mapping: List of (optype_encoding, alu_opcode) pairs

    ALU opcode encoding:
      0=ADD, 1=SUB, 2=SLT, 3=SLTU, 4=AND, 5=OR, 6=XOR, 8=SLL, 9=SRL, 11=SRA
-/
def mkOpTypeToALU4 (pfx : String) (optype : List Wire) (aluOp : List Wire)
    (mapping : List (Nat × Nat)) : List Gate :=
  -- For each ALU output bit, collect optype values that set it
  let testBit (n : Nat) (b : Nat) : Bool := (n / (2 ^ b)) % 2 != 0
  let bit0_terms := mapping.filter (fun (_, alu) => testBit alu 0) |>.map Prod.fst
  let bit1_terms := mapping.filter (fun (_, alu) => testBit alu 1) |>.map Prod.fst
  let bit2_terms := mapping.filter (fun (_, alu) => testBit alu 2) |>.map Prod.fst
  let bit3_terms := mapping.filter (fun (_, alu) => testBit alu 3) |>.map Prod.fst
  -- Helper: build a 6-bit equality match for one encoding value
  let mkMatch (enc : Nat) (tag : String) : (List Gate × Wire) :=
    let matchWire := Wire.mk s!"{pfx}_{tag}"
    -- Select true/inverted bit for each position
    let bitWires := (List.range 6).map fun b =>
      if testBit enc b then optype[b]! else Wire.mk s!"{pfx}_n{b}"
    -- Chain 6-input AND: a0 & a1 → t01, t01 & a2 → t012, etc.
    let t01 := Wire.mk s!"{pfx}_{tag}_t01"
    let t012 := Wire.mk s!"{pfx}_{tag}_t012"
    let t0123 := Wire.mk s!"{pfx}_{tag}_t0123"
    let t01234 := Wire.mk s!"{pfx}_{tag}_t01234"
    let andGates := [
      Gate.mkAND bitWires[0]! bitWires[1]! t01,
      Gate.mkAND t01 bitWires[2]! t012,
      Gate.mkAND t012 bitWires[3]! t0123,
      Gate.mkAND t0123 bitWires[4]! t01234,
      Gate.mkAND t01234 bitWires[5]! matchWire
    ]
    (andGates, matchWire)
  -- Helper: OR-chain to combine match wires into one output
  let mkOrChain (wires : List Wire) (outWire : Wire) : List Gate :=
    match wires with
    | [] => [Gate.mkBUF (Wire.mk s!"{pfx}_gnd") outWire]  -- no terms → 0
    | [w] => [Gate.mkBUF w outWire]
    | w0 :: w1 :: rest =>
      let first := Wire.mk s!"{pfx}_{outWire.name}_or0"
      let firstGate := Gate.mkOR w0 w1 first
      let (gates, _) := rest.enum.foldl (fun (acc, prev) ⟨idx, w⟩ =>
        let isLast := idx == rest.length - 1
        let next := if isLast then outWire else Wire.mk s!"{pfx}_{outWire.name}_or{idx+1}"
        (acc ++ [Gate.mkOR prev w next], next)
      ) ([firstGate], first)
      gates
  -- Generate shared NOT wires for all 6 optype bits
  let notGates := (List.range 6).map fun b =>
    Gate.mkNOT optype[b]! (Wire.mk s!"{pfx}_n{b}")
  -- Generate match + OR logic for each output bit
  let mkBitLogic (terms : List Nat) (bitIdx : Nat) : List Gate :=
    let matchResults := terms.enum.map fun ⟨idx, enc⟩ =>
      mkMatch enc s!"b{bitIdx}_e{idx}"
    let matchGates := (matchResults.map Prod.fst).flatten
    let matchWires := matchResults.map Prod.snd
    let orGates := mkOrChain matchWires aluOp[bitIdx]!
    matchGates ++ orGates
  notGates ++
    mkBitLogic bit0_terms 0 ++
    mkBitLogic bit1_terms 1 ++
    mkBitLogic bit2_terms 2 ++
    mkBitLogic bit3_terms 3

/-- Semantic ALU mapping: OpType → ALU4 opcode.
    Stable across decoder configurations — indices are resolved at build time.
    ALU: 0=ADD, 1=SUB, 2=SLT, 3=SLTU, 4=AND, 5=OR, 6=XOR, 8=SLL, 9=SRL, 11=SRA -/
def aluMappingByName : List (OpType × Nat) :=
  [ (.ADD, 0), (.ADDI, 0),
    (.SUB, 1),
    (.SLT, 2), (.SLTI, 2),
    (.SLTU, 3), (.SLTIU, 3),
    (.AND, 4), (.ANDI, 4),
    (.OR, 5), (.ORI, 5),
    (.XOR, 6), (.XORI, 6),
    (.SLL, 8), (.SLLI, 8),
    (.SRL, 9), (.SRLI, 9),
    (.SRA, 11), (.SRAI, 11) ]

/-- Semantic MulDiv mapping: OpType → 3-bit MulDiv opcode.
    MUL=0, MULH=1, MULHSU=2, MULHU=3, DIV=4, DIVU=5, REM=6, REMU=7 -/
def mulDivMappingByName : List (OpType × Nat) :=
  [ (.MUL, 0), (.MULH, 1), (.MULHSU, 2), (.MULHU, 3),
    (.DIV, 4), (.DIVU, 5), (.REM, 6), (.REMU, 7) ]

/-- Generic optype→opcode LUT for N-bit input → M-bit output.
    Same algorithm as mkOpTypeToALU4 but parameterized on widths. -/
def mkOpTypeLUT (pfx : String) (optype : List Wire) (outOp : List Wire)
    (mapping : List (Nat × Nat)) : List Gate :=
  let inWidth := optype.length
  let outWidth := outOp.length
  let testBit (n : Nat) (b : Nat) : Bool := (n / (2 ^ b)) % 2 != 0
  let bitTerms := (List.range outWidth).map fun b =>
    mapping.filter (fun (_, code) => testBit code b) |>.map Prod.fst
  let mkMatch (enc : Nat) (tag : String) : (List Gate × Wire) :=
    let matchWire := Wire.mk s!"{pfx}_{tag}"
    let bitWires := (List.range inWidth).map fun b =>
      if testBit enc b then optype[b]! else Wire.mk s!"{pfx}_n{b}"
    -- Chain AND gates
    let pairs := bitWires.enum.toArray
    if pairs.size <= 1 then
      ([Gate.mkBUF (bitWires.head!) matchWire], matchWire)
    else
      let first := Wire.mk s!"{pfx}_{tag}_t01"
      let firstGate := Gate.mkAND pairs[0]!.2 pairs[1]!.2 first
      let (gates, final) := (List.range (pairs.size - 2)).foldl (fun (acc, prev) idx =>
        let isLast := idx == pairs.size - 3
        let next := if isLast then matchWire else Wire.mk s!"{pfx}_{tag}_t{idx+2}"
        (acc ++ [Gate.mkAND prev pairs[idx + 2]!.2 next], next)
      ) ([firstGate], first)
      (gates, final)
  let mkOrChain (wires : List Wire) (outWire : Wire) : List Gate :=
    match wires with
    | [] => [Gate.mkBUF (Wire.mk s!"{pfx}_gnd") outWire]
    | [w] => [Gate.mkBUF w outWire]
    | w0 :: w1 :: rest =>
      let first := Wire.mk s!"{pfx}_{outWire.name}_or0"
      let firstGate := Gate.mkOR w0 w1 first
      let (gates, _) := rest.enum.foldl (fun (acc, prev) ⟨idx, w⟩ =>
        let isLast := idx == rest.length - 1
        let next := if isLast then outWire else Wire.mk s!"{pfx}_{outWire.name}_or{idx+1}"
        (acc ++ [Gate.mkOR prev w next], next)
      ) ([firstGate], first)
      gates
  let notGates := (List.range inWidth).map fun b =>
    Gate.mkNOT optype[b]! (Wire.mk s!"{pfx}_n{b}")
  let mkBitLogic (terms : List Nat) (bitIdx : Nat) : List Gate :=
    let matchResults := terms.enum.map fun ⟨idx, enc⟩ =>
      mkMatch enc s!"b{bitIdx}_e{idx}"
    let matchGates := (matchResults.map Prod.fst).flatten
    let matchWires := matchResults.map Prod.snd
    let orGates := mkOrChain matchWires outOp[bitIdx]!
    matchGates ++ orGates
  notGates ++ (bitTerms.enum.map fun ⟨i, terms⟩ => mkBitLogic terms i).flatten

/-- Semantic FPU mapping: OpType → 5-bit FPU opcode. -/
def fpuMappingByName : List (OpType × Nat) :=
  [ (.FADD_S, 0), (.FSUB_S, 1), (.FMUL_S, 2), (.FDIV_S, 3), (.FSQRT_S, 4),
    (.FMADD_S, 5), (.FMSUB_S, 6), (.FNMADD_S, 7), (.FNMSUB_S, 8),
    (.FEQ_S, 9), (.FLT_S, 10), (.FLE_S, 11),
    (.FCVT_W_S, 12), (.FCVT_WU_S, 13), (.FCVT_S_W, 14), (.FCVT_S_WU, 15),
    (.FMV_X_W, 16), (.FMV_W_X, 17), (.FCLASS_S, 18),
    (.FMIN_S, 19), (.FMAX_S, 20),
    (.FSGNJ_S, 21), (.FSGNJN_S, 22), (.FSGNJX_S, 23) ]

/-- Build a 64:1 mux tree from 64 single-bit inputs using 6 select bits. -/
def mkMux64to1 (inputs : List Wire) (sel : List Wire) (pfx : String) (output : Wire) : List Gate :=
  let l0 := (List.range 32).map fun i =>
    let o := Wire.mk s!"{pfx}_l0_{i}"
    (Gate.mkMUX inputs[2*i]! inputs[2*i+1]! sel[0]! o, o)
  let l0_outs := l0.map Prod.snd
  let l1 := (List.range 16).map fun i =>
    let o := Wire.mk s!"{pfx}_l1_{i}"
    (Gate.mkMUX l0_outs[2*i]! l0_outs[2*i+1]! sel[1]! o, o)
  let l1_outs := l1.map Prod.snd
  let l2 := (List.range 8).map fun i =>
    let o := Wire.mk s!"{pfx}_l2_{i}"
    (Gate.mkMUX l1_outs[2*i]! l1_outs[2*i+1]! sel[2]! o, o)
  let l2_outs := l2.map Prod.snd
  let l3 := (List.range 4).map fun i =>
    let o := Wire.mk s!"{pfx}_l3_{i}"
    (Gate.mkMUX l2_outs[2*i]! l2_outs[2*i+1]! sel[3]! o, o)
  let l3_outs := l3.map Prod.snd
  let l4 := (List.range 2).map fun i =>
    let o := Wire.mk s!"{pfx}_l4_{i}"
    (Gate.mkMUX l3_outs[2*i]! l3_outs[2*i+1]! sel[4]! o, o)
  let l4_outs := l4.map Prod.snd
  (l0.map Prod.fst) ++ (l1.map Prod.fst) ++ (l2.map Prod.fst) ++
    (l3.map Prod.fst) ++ (l4.map Prod.fst) ++
    [Gate.mkMUX l4_outs[0]! l4_outs[1]! sel[5]! output]

section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private def testBit (n : Nat) (b : Nat) : Bool := (n / (2 ^ b)) % 2 != 0

def mkOpcodeMatch6 (pfx : String) (enc : Nat) (opcode : List Wire) (result : Wire) : List Gate :=
  let bitWires := (List.range 6).map fun b =>
    if testBit enc b then opcode[b]! else Wire.mk s!"{pfx}_n{b}"
  let notGates := (List.range 6).filterMap fun b =>
    if !testBit enc b then some (Gate.mkNOT opcode[b]! (Wire.mk s!"{pfx}_n{b}")) else none
  let t01 := Wire.mk s!"{pfx}_t01"
  let t012 := Wire.mk s!"{pfx}_t012"
  let t0123 := Wire.mk s!"{pfx}_t0123"
  let t01234 := Wire.mk s!"{pfx}_t01234"
  notGates ++ [
    Gate.mkAND bitWires[0]! bitWires[1]! t01,
    Gate.mkAND t01 bitWires[2]! t012,
    Gate.mkAND t012 bitWires[3]! t0123,
    Gate.mkAND t0123 bitWires[4]! t01234,
    Gate.mkAND t01234 bitWires[5]! result
  ]

/-- Branch resolution logic: PC+4 link, target computation, condition evaluation,
    misprediction detection, ROB redirect, and redirect target muxes. -/
def mkBranchResolve
    (config : CPUConfig) (oi : OpType → Nat)
    (zero one : Wire)
    (br_captured_pc br_captured_imm : List Wire)
    (rs_branch_dispatch_src1 rs_branch_dispatch_src2 : List Wire)
    (rs_branch_dispatch_opcode : List Wire)
    (branch_result : List Wire)
    (branch_predicted_taken : Wire)
    (rob_commit_en rob_head_isBranch rob_head_mispredicted : Wire)
    (rob_head_redirect_target fence_i_redir_target : List Wire)
    (fence_i_drain_complete : Wire)
    (csr_flush_suppress not_csr_flush_suppress rename_flush_en redirect_valid_int : Wire)
    (rob_redirect_valid : Wire)
    (branch_redirect_target : List Wire)
    : List Gate × List CircuitInstance × Wire × Wire × List Wire × List Wire × List Wire × Wire × List Wire :=
  -- === JAL/JALR LINK REGISTER (PC+4) ===
  let br_pc_plus_4 := makeIndexedWires "br_pc_plus_4" 32
  let br_pc_plus_4_b := makeIndexedWires "br_pc_plus_4_b" 32
  let br_pc_plus_4_b_gates := (List.range 32).map (fun i =>
    if i == 2 then Gate.mkBUF one br_pc_plus_4_b[i]!
    else Gate.mkBUF zero br_pc_plus_4_b[i]!)

  let br_pc_plus_4_adder_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_br_pc_plus_4"
    portMap :=
      (br_captured_pc.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (br_pc_plus_4_b.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", zero)] ++
      (br_pc_plus_4.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w))) ++
      []
  }

  -- Opcode match: JAL/JALR from config
  let is_jal := Wire.mk "is_jal"
  let is_jalr := Wire.mk "is_jalr"
  let is_jal_or_jalr := Wire.mk "is_jal_or_jalr"
  let jal_match_gates := mkOpcodeMatch6 "jal_match" (oi .JAL) rs_branch_dispatch_opcode is_jal
  let jalr_match_gates := mkOpcodeMatch6 "jalr_match" (oi .JALR) rs_branch_dispatch_opcode is_jalr
  let jal_jalr_or_gate := [Gate.mkOR is_jal is_jalr is_jal_or_jalr]

  let branch_result_final := makeIndexedWires "branch_result_final" 32
  let branch_result_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX branch_result[i]! br_pc_plus_4[i]! is_jal_or_jalr branch_result_final[i]!)

  -- === BRANCH TARGET + PC REDIRECT ===
  let branch_target := makeIndexedWires "branch_target" 32
  let branch_target_adder_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_branch_target"
    portMap :=
      (br_captured_pc.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (br_captured_imm.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", zero)] ++
      (branch_target.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w))) ++
      []
  }

  -- JALR target = src1 + br_captured_imm, bit 0 cleared
  let jalr_target_raw := makeIndexedWires "jalr_target_raw" 32
  let jalr_target := makeIndexedWires "jalr_target" 32
  let jalr_target_adder_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_jalr_target"
    portMap :=
      (rs_branch_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (br_captured_imm.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", zero)] ++
      (jalr_target_raw.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w))) ++
      []
  }
  let jalr_target_gates := (List.range 32).map (fun i =>
    if i == 0 then Gate.mkBUF zero jalr_target[i]!
    else Gate.mkBUF jalr_target_raw[i]! jalr_target[i]!)

  let final_branch_target := makeIndexedWires "final_branch_target" 32
  let target_sel_gates := (List.range 32).map (fun i =>
    Gate.mkMUX branch_target[i]! jalr_target[i]! is_jalr final_branch_target[i]!)

  -- Branch condition evaluation
  let br_eq := Wire.mk "br_eq"
  let br_lt := Wire.mk "br_lt"
  let br_ltu := Wire.mk "br_ltu"

  let br_cmp_inst : CircuitInstance := {
    moduleName := "Comparator32"
    instName := "u_br_cmp"
    portMap :=
      (rs_branch_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (rs_branch_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("one", one), ("eq", br_eq), ("lt", br_lt), ("ltu", br_ltu),
       ("gt", Wire.mk "br_gt"), ("gtu", Wire.mk "br_gtu")]
  }

  -- Decode branch condition from opcode (encodings from config)
  let is_beq := Wire.mk "is_beq"
  let is_bne := Wire.mk "is_bne"
  let is_blt := Wire.mk "is_blt"
  let is_bge := Wire.mk "is_bge"
  let is_bltu := Wire.mk "is_bltu"
  let is_bgeu := Wire.mk "is_bgeu"

  let beq_match_gates := mkOpcodeMatch6 "beq_match" (oi .BEQ) rs_branch_dispatch_opcode is_beq
  let bne_match_gates := mkOpcodeMatch6 "bne_match" (oi .BNE) rs_branch_dispatch_opcode is_bne
  let blt_match_gates := mkOpcodeMatch6 "blt_match" (oi .BLT) rs_branch_dispatch_opcode is_blt
  let bge_match_gates := mkOpcodeMatch6 "bge_match" (oi .BGE) rs_branch_dispatch_opcode is_bge
  let bltu_match_gates := mkOpcodeMatch6 "bltu_match" (oi .BLTU) rs_branch_dispatch_opcode is_bltu
  let bgeu_match_gates := mkOpcodeMatch6 "bgeu_match" (oi .BGEU) rs_branch_dispatch_opcode is_bgeu

  -- Condition evaluation
  let not_eq := Wire.mk "br_not_eq"
  let not_lt := Wire.mk "not_lt"
  let not_ltu := Wire.mk "not_ltu"
  let beq_taken := Wire.mk "beq_taken"
  let bne_taken := Wire.mk "bne_taken"
  let blt_taken := Wire.mk "blt_taken"
  let bge_taken := Wire.mk "bge_taken"
  let bltu_taken := Wire.mk "bltu_taken"
  let bgeu_taken := Wire.mk "bgeu_taken"
  let cond_taken_tmp1 := Wire.mk "cond_taken_tmp1"
  let cond_taken_tmp2 := Wire.mk "cond_taken_tmp2"
  let cond_taken_tmp3 := Wire.mk "cond_taken_tmp3"
  let cond_taken_tmp4 := Wire.mk "cond_taken_tmp4"
  let cond_taken := Wire.mk "cond_taken"
  let branch_taken := Wire.mk "branch_taken"

  let branch_cond_gates := [
    Gate.mkNOT br_eq not_eq,
    Gate.mkNOT br_lt not_lt,
    Gate.mkNOT br_ltu not_ltu,
    Gate.mkAND is_beq br_eq beq_taken,
    Gate.mkAND is_bne not_eq bne_taken,
    Gate.mkAND is_blt br_lt blt_taken,
    Gate.mkAND is_bge not_lt bge_taken,
    Gate.mkAND is_bltu br_ltu bltu_taken,
    Gate.mkAND is_bgeu not_ltu bgeu_taken,
    Gate.mkOR beq_taken bne_taken cond_taken_tmp1,
    Gate.mkOR cond_taken_tmp1 blt_taken cond_taken_tmp2,
    Gate.mkOR cond_taken_tmp2 bge_taken cond_taken_tmp3,
    Gate.mkOR cond_taken_tmp3 bltu_taken cond_taken_tmp4,
    Gate.mkOR cond_taken_tmp4 bgeu_taken cond_taken,
    Gate.mkOR cond_taken is_jal_or_jalr branch_taken
  ]

  -- Misprediction detection
  let branch_mispredicted := Wire.mk "branch_mispredicted"
  let branch_cond_mispredicted := Wire.mk "branch_cond_mispredicted"
  let branch_mispredicted_gate :=
    [Gate.mkXOR branch_predicted_taken branch_taken branch_cond_mispredicted,
     Gate.mkOR branch_cond_mispredicted is_jalr branch_mispredicted]

  -- ROB redirect + CSR flush suppression
  let rob_redirect_tmp := Wire.mk "rob_redirect_tmp"
  let rob_redirect_branch := Wire.mk "rob_redirect_branch"
  let csr_flush_suppress_gates := if config.enableZicsr then [
    Gate.mkNOT csr_flush_suppress not_csr_flush_suppress,
    Gate.mkAND redirect_valid_int not_csr_flush_suppress rename_flush_en
  ] else [
    Gate.mkBUF redirect_valid_int rename_flush_en,
    Gate.mkBUF zero not_csr_flush_suppress
  ]
  let branch_redirect_gate := [
    Gate.mkAND rob_commit_en rob_head_isBranch rob_redirect_tmp,
    Gate.mkAND rob_redirect_tmp rob_head_mispredicted rob_redirect_branch,
    Gate.mkOR rob_redirect_branch fence_i_drain_complete rob_redirect_valid
  ]

  -- Redirect target: MUX between branch redirect target and FENCE.I PC+4
  let branch_target_wire_gates := (List.range 32).map (fun i =>
    Gate.mkMUX rob_head_redirect_target[i]! fence_i_redir_target[i]! fence_i_drain_complete branch_redirect_target[i]!)

  -- Misprediction redirect target mux
  let mispredict_redirect_target := makeIndexedWires "mispredict_redirect_target" 32
  let mispredict_sel := Wire.mk "mispredict_sel"
  let not_jal_or_jalr := Wire.mk "not_jal_or_jalr"
  let mispredict_redirect_gates :=
    [Gate.mkNOT is_jal_or_jalr not_jal_or_jalr,
     Gate.mkAND branch_predicted_taken not_jal_or_jalr mispredict_sel] ++
    (List.range 32).map (fun i =>
    Gate.mkMUX final_branch_target[i]! br_pc_plus_4[i]! mispredict_sel mispredict_redirect_target[i]!)

  let allGates :=
    br_pc_plus_4_b_gates ++ branch_result_mux_gates ++
    jal_match_gates ++ jalr_match_gates ++ jal_jalr_or_gate ++
    beq_match_gates ++ bne_match_gates ++ blt_match_gates ++
    bge_match_gates ++ bltu_match_gates ++ bgeu_match_gates ++
    branch_cond_gates ++ branch_mispredicted_gate ++ csr_flush_suppress_gates ++ branch_redirect_gate ++ mispredict_redirect_gates ++ branch_target_wire_gates ++
    jalr_target_gates ++ target_sel_gates

  let allInsts := [br_pc_plus_4_adder_inst, branch_target_adder_inst, jalr_target_adder_inst, br_cmp_inst]

  (allGates, allInsts, branch_taken, branch_mispredicted, final_branch_target,
   br_pc_plus_4, branch_result_final, is_jal_or_jalr, mispredict_redirect_target)

/-- Generate ROB shadow registers: is_fp (16×1), isStore (16×1), redirect target (16×6 tag + 16×32 target).
    Returns (gates, instances, rob_head_is_fp, not_rob_head_is_fp, rob_head_isStore, rob_head_redirect_target). -/
def mkShadowRegisters
    (enableF : Bool) (_zero _one clock reset : Wire)
    (rob_alloc_idx : List Wire) (rename_valid_gated : Wire)
    (decode_has_fp_rd dispatch_is_store : Wire)
    (alloc_physRd_for_shadow : List Wire)  -- 6-bit physRd tag written at allocation
    (cdb_tag_rob : List Wire) (cdb_valid cdb_mispredicted : Wire)
    (cdb_redirect_target : List Wire)  -- 32-bit
    (rob_head_idx : List Wire)  -- 4-bit
    : (List Gate × List CircuitInstance × Wire × Wire × Wire × List Wire) :=
  let rob_head_is_fp := Wire.mk "rob_head_is_fp"
  let not_rob_head_is_fp := Wire.mk "not_rob_head_is_fp"
  let rob_head_isStore := Wire.mk "rob_head_isStore"
  let rob_head_redirect_target := makeIndexedWires "rob_head_redirect_target" 32

  -- === is_fp shadow ===
  let rob_is_fp_shadow := (List.range 16).map (fun e => Wire.mk s!"rob_is_fp_e{e}")
  let rob_fp_shadow_write_gates :=
    if enableF then
      (List.range 16).map (fun e =>
        let match_bits := (List.range 4).map (fun b =>
          if (e / (2 ^ b)) % 2 != 0 then rob_alloc_idx[b]!
          else Wire.mk s!"rob_fp_sd_n{e}_{b}")
        let not_gates := (List.range 4).filterMap (fun b =>
          if (e / (2 ^ b)) % 2 == 0 then
            some (Gate.mkNOT rob_alloc_idx[b]! (Wire.mk s!"rob_fp_sd_n{e}_{b}"))
          else none)
        let t01 := Wire.mk s!"rob_fp_sd_t01_{e}"
        let t012 := Wire.mk s!"rob_fp_sd_t012_{e}"
        let next := Wire.mk s!"rob_fp_sdnx_e{e}"
        let rob_fp_shadow_decoded := Wire.mk s!"rob_fp_shadow_decoded_{e}"
        let rob_fp_shadow_we := Wire.mk s!"rob_fp_shadow_we_{e}"
        not_gates ++ [
          Gate.mkAND match_bits[0]! match_bits[1]! t01,
          Gate.mkAND t01 match_bits[2]! t012,
          Gate.mkAND t012 match_bits[3]! rob_fp_shadow_decoded,
          Gate.mkAND rob_fp_shadow_decoded rename_valid_gated rob_fp_shadow_we,
          Gate.mkMUX rob_is_fp_shadow[e]! decode_has_fp_rd rob_fp_shadow_we next,
          Gate.mkDFF next clock reset rob_is_fp_shadow[e]!
        ]) |>.flatten
    else []
  let rob_fp_shadow_read_gates :=
    if enableF then
      let mux_l0_w := (List.range 8).map (fun i => Wire.mk s!"rob_fp_rd_m0_{i}")
      let mux_l0_g := (List.range 8).map (fun i =>
        Gate.mkMUX rob_is_fp_shadow[2*i]! rob_is_fp_shadow[2*i+1]! rob_head_idx[0]! mux_l0_w[i]!)
      let mux_l1_w := (List.range 4).map (fun i => Wire.mk s!"rob_fp_rd_m1_{i}")
      let mux_l1_g := (List.range 4).map (fun i =>
        Gate.mkMUX mux_l0_w[2*i]! mux_l0_w[2*i+1]! rob_head_idx[1]! mux_l1_w[i]!)
      let mux_l2_w := (List.range 2).map (fun i => Wire.mk s!"rob_fp_rd_m2_{i}")
      let mux_l2_g := (List.range 2).map (fun i =>
        Gate.mkMUX mux_l1_w[2*i]! mux_l1_w[2*i+1]! rob_head_idx[2]! mux_l2_w[i]!)
      mux_l0_g ++ mux_l1_g ++ mux_l2_g ++
      [Gate.mkMUX mux_l2_w[0]! mux_l2_w[1]! rob_head_idx[3]! rob_head_is_fp,
       Gate.mkNOT rob_head_is_fp not_rob_head_is_fp]
    else []
  let rob_fp_shadow_gates := rob_fp_shadow_write_gates ++ rob_fp_shadow_read_gates

  -- === isStore shadow ===
  let rob_isStore_shadow := (List.range 16).map (fun e => Wire.mk s!"rob_isStore_e{e}")
  let rob_isStore_shadow_results := (List.range 16).map (fun e =>
      let match_bits := (List.range 4).map (fun b =>
        if (e / (2 ^ b)) % 2 != 0 then rob_alloc_idx[b]!
        else Wire.mk s!"rob_st_sd_n{e}_{b}")
      let not_gates := (List.range 4).filterMap (fun b =>
        if (e / (2 ^ b)) % 2 == 0 then
          some (Gate.mkNOT rob_alloc_idx[b]! (Wire.mk s!"rob_st_sd_n{e}_{b}"))
        else none)
      let t01 := Wire.mk s!"rob_st_sd_t01_{e}"
      let t012 := Wire.mk s!"rob_st_sd_t012_{e}"
      let decoded := Wire.mk s!"rob_st_sd_dec_{e}"
      let we := Wire.mk s!"rob_st_sd_we_{e}"
      let next := Wire.mk s!"rob_st_sdnx_e{e}"
      let gates := not_gates ++ [
        Gate.mkAND match_bits[0]! match_bits[1]! t01,
        Gate.mkAND t01 match_bits[2]! t012,
        Gate.mkAND t012 match_bits[3]! decoded,
        Gate.mkAND decoded rename_valid_gated we,
        Gate.mkMUX rob_isStore_shadow[e]! dispatch_is_store we next
      ]
      let inst : CircuitInstance := {
        moduleName := "DFlipFlop", instName := s!"u_rob_isStore_dff_{e}",
        portMap := [("d", next), ("q", rob_isStore_shadow[e]!),
                    ("clock", clock), ("reset", reset)]
      }
      (gates, inst))
  let rob_isStore_shadow_write_gates := (rob_isStore_shadow_results.map Prod.fst).flatten
  let rob_isStore_shadow_insts := rob_isStore_shadow_results.map Prod.snd
  let rob_isStore_shadow_read_gates :=
    let mux_l0_w := (List.range 8).map (fun i => Wire.mk s!"rob_st_rd_m0_{i}")
    let mux_l0_g := (List.range 8).map (fun i =>
      Gate.mkMUX rob_isStore_shadow[2*i]! rob_isStore_shadow[2*i+1]! rob_head_idx[0]! mux_l0_w[i]!)
    let mux_l1_w := (List.range 4).map (fun i => Wire.mk s!"rob_st_rd_m1_{i}")
    let mux_l1_g := (List.range 4).map (fun i =>
      Gate.mkMUX mux_l0_w[2*i]! mux_l0_w[2*i+1]! rob_head_idx[1]! mux_l1_w[i]!)
    let mux_l2_w := (List.range 2).map (fun i => Wire.mk s!"rob_st_rd_m2_{i}")
    let mux_l2_g := (List.range 2).map (fun i =>
      Gate.mkMUX mux_l1_w[2*i]! mux_l1_w[2*i+1]! rob_head_idx[2]! mux_l2_w[i]!)
    mux_l0_g ++ mux_l1_g ++ mux_l2_g ++
    [Gate.mkMUX mux_l2_w[0]! mux_l2_w[1]! rob_head_idx[3]! rob_head_isStore]
  let rob_isStore_shadow_gates := rob_isStore_shadow_write_gates ++ rob_isStore_shadow_read_gates

  -- === Redirect target shadow ===
  let redir_tag_shadow := (List.range 16).map (fun e => makeIndexedWires s!"redir_tag_e{e}" 6)
  let redir_tag_shadow_results := (List.range 16).map (fun e =>
    let match_bits := (List.range 4).map (fun b =>
      if (e / (2 ^ b)) % 2 != 0 then rob_alloc_idx[b]!
      else Wire.mk s!"redir_ts_n{e}_{b}")
    let not_gates := (List.range 4).filter (fun b => (e / (2 ^ b)) % 2 == 0) |>.map (fun b =>
      Gate.mkNOT rob_alloc_idx[b]! (Wire.mk s!"redir_ts_n{e}_{b}"))
    let decoded := Wire.mk s!"redir_ts_dec{e}"
    let we := Wire.mk s!"redir_ts_we{e}"
    let t01 := Wire.mk s!"redir_ts_t01_{e}"
    let t012 := Wire.mk s!"redir_ts_t012_{e}"
    let gates := not_gates ++ [
      Gate.mkAND match_bits[0]! match_bits[1]! t01,
      Gate.mkAND t01 match_bits[2]! t012,
      Gate.mkAND t012 match_bits[3]! decoded,
      Gate.mkAND decoded rename_valid_gated we
    ]
    let bit_gates := (List.range 6).map (fun b =>
      let next := Wire.mk s!"redir_ts_next{e}_{b}"
      [Gate.mkMUX redir_tag_shadow[e]![b]! alloc_physRd_for_shadow[b]! we next,
       Gate.mkDFF next clock reset redir_tag_shadow[e]![b]!]) |>.flatten
    (gates ++ bit_gates))
  let redir_tag_shadow_gates := redir_tag_shadow_results.flatten

  let redir_tag_match := (List.range 16).map (fun e => Wire.mk s!"redir_tm{e}")
  let redir_tag_cmp_insts : List CircuitInstance := (List.range 16).map (fun e => {
    moduleName := "EqualityComparator6"
    instName := s!"u_redir_tag_cmp_{e}"
    portMap := [("eq", redir_tag_match[e]!)] ++
               (cdb_tag_rob.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (redir_tag_shadow[e]!.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  })

  let redir_target_shadow := (List.range 16).map (fun e => makeIndexedWires s!"redir_tgt_e{e}" 32)
  let redir_target_shadow_results := (List.range 16).map (fun e =>
    let we := Wire.mk s!"redir_tgt_we{e}"
    let we_tmp := Wire.mk s!"redir_tgt_we_tmp{e}"
    let gates := [
      Gate.mkAND cdb_valid redir_tag_match[e]! we_tmp,
      Gate.mkAND we_tmp cdb_mispredicted we
    ]
    let insts : List (List Gate × CircuitInstance) := (List.range 32).map (fun b =>
      let next := Wire.mk s!"redir_tgt_next{e}_{b}"
      ([Gate.mkMUX redir_target_shadow[e]![b]! cdb_redirect_target[b]! we next],
       { moduleName := "DFlipFlop"
         instName := s!"u_redir_tgt_dff_{e}_{b}"
         portMap := [("d", next), ("q", redir_target_shadow[e]![b]!),
                     ("clock", clock), ("reset", reset)]
       }))
    (gates ++ (insts.map Prod.fst).flatten, insts.map Prod.snd))
  let redir_target_shadow_gates := (redir_target_shadow_results.map Prod.fst).flatten
  let redir_target_shadow_insts := (redir_target_shadow_results.map Prod.snd).flatten

  let redir_target_read_gates := (List.range 32).map (fun b =>
    let mux_l0 := (List.range 8).map (fun i => Wire.mk s!"redir_rd_m0_{b}_{i}")
    let mux_l0_g := (List.range 8).map (fun i =>
      Gate.mkMUX redir_target_shadow[2*i]![b]! redir_target_shadow[2*i+1]![b]! rob_head_idx[0]! mux_l0[i]!)
    let mux_l1 := (List.range 4).map (fun i => Wire.mk s!"redir_rd_m1_{b}_{i}")
    let mux_l1_g := (List.range 4).map (fun i =>
      Gate.mkMUX mux_l0[2*i]! mux_l0[2*i+1]! rob_head_idx[1]! mux_l1[i]!)
    let mux_l2 := (List.range 2).map (fun i => Wire.mk s!"redir_rd_m2_{b}_{i}")
    let mux_l2_g := (List.range 2).map (fun i =>
      Gate.mkMUX mux_l1[2*i]! mux_l1[2*i+1]! rob_head_idx[2]! mux_l2[i]!)
    mux_l0_g ++ mux_l1_g ++ mux_l2_g ++
    [Gate.mkMUX mux_l2[0]! mux_l2[1]! rob_head_idx[3]! rob_head_redirect_target[b]!]
  ) |>.flatten
  let redir_shadow_all_gates := redir_tag_shadow_gates ++ redir_target_shadow_gates ++ redir_target_read_gates

  let all_gates := rob_fp_shadow_gates ++ rob_isStore_shadow_gates ++ redir_shadow_all_gates
  let all_insts := rob_isStore_shadow_insts ++ redir_tag_cmp_insts ++ redir_target_shadow_insts
  (all_gates, all_insts, rob_head_is_fp, not_rob_head_is_fp, rob_head_isStore, rob_head_redirect_target)

/-- W=2 shadow registers: isStore + redirect target with dual alloc and dual CDB ports.
    Returns (gates, instances, rob_head_isStore, rob_head_redirect_target). -/
def mkShadowRegisters2
    (_zero _one clock reset : Wire)
    (rob_alloc_idx_0 rob_alloc_idx_1 : List Wire) -- 4-bit each
    (rename_valid_0 rename_valid_1 : Wire)
    (dispatch_is_store_0 dispatch_is_store_1 : Wire)
    (alloc_physRd_0 alloc_physRd_1 : List Wire) -- 6-bit each
    (cdb_tag_0 cdb_tag_1 : List Wire) -- 6-bit each
    (cdb_valid_0 cdb_valid_1 : Wire)
    (cdb_mispredicted_0 cdb_mispredicted_1 : Wire)
    (cdb_redirect_target_0 cdb_redirect_target_1 : List Wire) -- 32-bit each
    (rob_head_idx_0 rob_head_idx_1 : List Wire) -- 4-bit each
    : (List Gate × List CircuitInstance × Wire × Wire × List Wire × List Wire) :=
  let rob_head_isStore := Wire.mk "rob_head_isStore_0"
  let rob_head_isStore_1 := Wire.mk "rob_head_isStore_1"
  let rob_head_redirect_target_0 := makeIndexedWires "rob_head_redirect_target_0" 32
  let rob_head_redirect_target_1 := makeIndexedWires "rob_head_redirect_target_1" 32

  -- Helper: decode alloc_idx to per-entry write-enable for given slot
  let mkAllocDecode (pfx : String) (alloc_idx : List Wire) (rename_valid : Wire) (entries : Nat) :=
    (List.range entries).map (fun e =>
      let match_bits := (List.range 4).map (fun b =>
        if (e / (2 ^ b)) % 2 != 0 then alloc_idx[b]!
        else Wire.mk s!"{pfx}_n{e}_{b}")
      let not_gates := (List.range 4).filterMap (fun b =>
        if (e / (2 ^ b)) % 2 == 0 then
          some (Gate.mkNOT alloc_idx[b]! (Wire.mk s!"{pfx}_n{e}_{b}"))
        else none)
      let t01 := Wire.mk s!"{pfx}_t01_{e}"
      let t012 := Wire.mk s!"{pfx}_t012_{e}"
      let decoded := Wire.mk s!"{pfx}_dec_{e}"
      let we := Wire.mk s!"{pfx}_we_{e}"
      (not_gates ++ [
        Gate.mkAND match_bits[0]! match_bits[1]! t01,
        Gate.mkAND t01 match_bits[2]! t012,
        Gate.mkAND t012 match_bits[3]! decoded,
        Gate.mkAND decoded rename_valid we
      ], we))

  -- Helper: 16:1 mux tree reading shadow register by head index
  let mkMux16to1 (pfx : String) (values : List Wire) (sel : List Wire) (out : Wire) :=
    let mux_l0 := (List.range 8).map (fun i => Wire.mk s!"{pfx}_m0_{i}")
    let mux_l0_g := (List.range 8).map (fun i =>
      Gate.mkMUX values[2*i]! values[2*i+1]! sel[0]! mux_l0[i]!)
    let mux_l1 := (List.range 4).map (fun i => Wire.mk s!"{pfx}_m1_{i}")
    let mux_l1_g := (List.range 4).map (fun i =>
      Gate.mkMUX mux_l0[2*i]! mux_l0[2*i+1]! sel[1]! mux_l1[i]!)
    let mux_l2 := (List.range 2).map (fun i => Wire.mk s!"{pfx}_m2_{i}")
    let mux_l2_g := (List.range 2).map (fun i =>
      Gate.mkMUX mux_l1[2*i]! mux_l1[2*i+1]! sel[2]! mux_l2[i]!)
    mux_l0_g ++ mux_l1_g ++ mux_l2_g ++ [Gate.mkMUX mux_l2[0]! mux_l2[1]! sel[3]! out]

  -- === isStore shadow (16 entries, dual write) ===
  let rob_isStore_shadow := (List.range 16).map (fun e => Wire.mk s!"rob_isStore_e{e}")
  let s0_dec := mkAllocDecode "st_s0" rob_alloc_idx_0 rename_valid_0 16
  let s1_dec := mkAllocDecode "st_s1" rob_alloc_idx_1 rename_valid_1 16
  let isStore_results := (List.range 16).map (fun e =>
    let we0 := (s0_dec[e]!).2
    let we1 := (s1_dec[e]!).2
    -- Dual-write MUX: slot 1 wins if both (shouldn't happen with sequential alloc)
    let mid := Wire.mk s!"rob_st_mid_{e}"
    let next := Wire.mk s!"rob_st_next_{e}"
    let gates := [
      Gate.mkMUX rob_isStore_shadow[e]! dispatch_is_store_0 we0 mid,
      Gate.mkMUX mid dispatch_is_store_1 we1 next]
    let inst : CircuitInstance := {
      moduleName := "DFlipFlop", instName := s!"u_rob_isStore_dff_{e}",
      portMap := [("d", next), ("q", rob_isStore_shadow[e]!),
                  ("clock", clock), ("reset", reset)] }
    (gates, inst))
  let isStore_alloc_gates := (s0_dec.map Prod.fst).flatten ++ (s1_dec.map Prod.fst).flatten
  let isStore_write_gates := (isStore_results.map Prod.fst).flatten
  let isStore_insts := isStore_results.map Prod.snd
  let isStore_read_0 := mkMux16to1 "st_rd0" rob_isStore_shadow rob_head_idx_0 rob_head_isStore
  let isStore_read_1 := mkMux16to1 "st_rd1" rob_isStore_shadow rob_head_idx_1 rob_head_isStore_1
  let isStore_gates := isStore_alloc_gates ++ isStore_write_gates ++ isStore_read_0 ++ isStore_read_1

  -- === Redirect tag shadow (6-bit physRd per entry, dual write) ===
  let redir_tag_shadow := (List.range 16).map (fun e => makeIndexedWires s!"redir_tag_e{e}" 6)
  let rt0_dec := mkAllocDecode "rt_s0" rob_alloc_idx_0 rename_valid_0 16
  let rt1_dec := mkAllocDecode "rt_s1" rob_alloc_idx_1 rename_valid_1 16
  let redir_tag_results := (List.range 16).map (fun e =>
    let we0 := (rt0_dec[e]!).2
    let we1 := (rt1_dec[e]!).2
    let bit_gates := (List.range 6).map (fun b =>
      let mid := Wire.mk s!"redir_ts_mid{e}_{b}"
      let next := Wire.mk s!"redir_ts_next{e}_{b}"
      [Gate.mkMUX redir_tag_shadow[e]![b]! alloc_physRd_0[b]! we0 mid,
       Gate.mkMUX mid alloc_physRd_1[b]! we1 next,
       Gate.mkDFF next clock reset redir_tag_shadow[e]![b]!]) |>.flatten
    bit_gates)
  let redir_tag_alloc_gates := (rt0_dec.map Prod.fst).flatten ++ (rt1_dec.map Prod.fst).flatten
  let redir_tag_write_gates := redir_tag_results.flatten

  -- === Redirect tag comparison (dual CDB) ===
  -- For each entry, check both CDB tags for match
  let redir_tag_match_0 := (List.range 16).map (fun e => Wire.mk s!"redir_tm0_{e}")
  let redir_tag_match_1 := (List.range 16).map (fun e => Wire.mk s!"redir_tm1_{e}")
  let redir_tag_cmp_insts : List CircuitInstance :=
    (List.range 16).map (fun e => {
      moduleName := "EqualityComparator6"
      instName := s!"u_redir_tag_cmp0_{e}"
      portMap := [("eq", redir_tag_match_0[e]!)] ++
                 (cdb_tag_0.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
                 (redir_tag_shadow[e]!.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
    }) ++
    (List.range 16).map (fun e => {
      moduleName := "EqualityComparator6"
      instName := s!"u_redir_tag_cmp1_{e}"
      portMap := [("eq", redir_tag_match_1[e]!)] ++
                 (cdb_tag_1.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
                 (redir_tag_shadow[e]!.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
    })

  -- === Redirect target shadow (32-bit per entry, dual CDB write) ===
  let redir_target_shadow := (List.range 16).map (fun e => makeIndexedWires s!"redir_tgt_e{e}" 32)
  let redir_target_results := (List.range 16).map (fun e =>
    let we0_tmp := Wire.mk s!"redir_tgt_we0_tmp{e}"
    let we0 := Wire.mk s!"redir_tgt_we0_{e}"
    let we1_tmp := Wire.mk s!"redir_tgt_we1_tmp{e}"
    let we1 := Wire.mk s!"redir_tgt_we1_{e}"
    let we_gates := [
      Gate.mkAND cdb_valid_0 redir_tag_match_0[e]! we0_tmp,
      Gate.mkAND we0_tmp cdb_mispredicted_0 we0,
      Gate.mkAND cdb_valid_1 redir_tag_match_1[e]! we1_tmp,
      Gate.mkAND we1_tmp cdb_mispredicted_1 we1]
    let insts := (List.range 32).map (fun b =>
      let mid := Wire.mk s!"redir_tgt_mid{e}_{b}"
      let next := Wire.mk s!"redir_tgt_next{e}_{b}"
      ([Gate.mkMUX redir_target_shadow[e]![b]! cdb_redirect_target_0[b]! we0 mid,
        Gate.mkMUX mid cdb_redirect_target_1[b]! we1 next],
       { moduleName := "DFlipFlop"
         instName := s!"u_redir_tgt_dff_{e}_{b}"
         portMap := [("d", next), ("q", redir_target_shadow[e]![b]!),
                     ("clock", clock), ("reset", reset)] : CircuitInstance }))
    (we_gates ++ (insts.map Prod.fst).flatten, insts.map Prod.snd))
  let redir_target_gates := (redir_target_results.map Prod.fst).flatten
  let redir_target_insts := (redir_target_results.map Prod.snd).flatten

  -- Read redirect target at head (dual head)
  let redir_target_read_0 := (List.range 32).map (fun b =>
    mkMux16to1 s!"redir_rd0_{b}" ((List.range 16).map (fun e => redir_target_shadow[e]![b]!)) rob_head_idx_0 rob_head_redirect_target_0[b]!
  ) |>.flatten
  let redir_target_read_1 := (List.range 32).map (fun b =>
    mkMux16to1 s!"redir_rd1_{b}" ((List.range 16).map (fun e => redir_target_shadow[e]![b]!)) rob_head_idx_1 rob_head_redirect_target_1[b]!
  ) |>.flatten

  let all_gates := isStore_gates ++
    redir_tag_alloc_gates ++ redir_tag_write_gates ++
    redir_target_gates ++ redir_target_read_0 ++ redir_target_read_1
  let all_insts := isStore_insts ++ redir_tag_cmp_insts ++ redir_target_insts
  (all_gates, all_insts, rob_head_isStore, rob_head_isStore_1, rob_head_redirect_target_0, rob_head_redirect_target_1)

/-- Generate fflags accumulation and frm register update logic.
    Returns (gates, dff_instances). -/
def mkFPFlags
    (enableF : Bool) (zero _one clock reset : Wire)
    (fp_valid_out : Wire) (fp_exceptions : List Wire)
    (fflags_reg fflags_new fflags_acc fflags_masked fflags_acc_val : List Wire)
    (frm_reg frm_new : List Wire)
    : (List Gate × List CircuitInstance) :=
  let fflags_csr_we := Wire.mk "fflags_csr_we"
  let fflags_gates :=
    if enableF then
      (List.range 5).map (fun i =>
        Gate.mkAND fp_valid_out fp_exceptions[i]! fflags_masked[i]!) ++
      (List.range 5).map (fun i =>
        Gate.mkOR fflags_reg[i]! fflags_masked[i]! fflags_acc_val[i]!) ++
      [Gate.mkOR (Wire.mk "csr_we_fflags") (Wire.mk "csr_we_fcsr") fflags_csr_we] ++
      (List.range 5).map (fun i =>
        Gate.mkMUX fflags_acc_val[i]! (Wire.mk s!"csr_wv_e{i}") fflags_csr_we fflags_new[i]!) ++
      (List.range 5).map (fun i =>
        Gate.mkBUF fflags_reg[i]! fflags_acc[i]!)
    else
      (List.range 5).map (fun i => Gate.mkBUF zero fflags_acc[i]!)
  let fflags_dff_instances :=
    if enableF then
      (List.range 5).map (fun i =>
        { moduleName := "DFlipFlop"
          instName := s!"u_fflags_dff_{i}"
          portMap := [("d", fflags_new[i]!), ("q", fflags_reg[i]!),
                      ("clock", clock), ("reset", reset)] : CircuitInstance })
    else []
  let frm_dff_instances :=
    if enableF then
      (List.range 3).map (fun i =>
        { moduleName := "DFlipFlop"
          instName := s!"u_frm_dff_{i}"
          portMap := [("d", frm_new[i]!), ("q", frm_reg[i]!),
                      ("clock", clock), ("reset", reset)] : CircuitInstance })
    else []
  let frm_csr_we := Wire.mk "frm_csr_we"
  let frm_from_csr := makeIndexedWires "frm_from_csr" 3
  let frm_gates :=
    if enableF then
      [Gate.mkOR (Wire.mk "csr_we_frm") (Wire.mk "csr_we_fcsr") frm_csr_we] ++
      (List.range 3).map (fun i =>
        Gate.mkMUX (Wire.mk s!"csr_wv_e{i}") (Wire.mk s!"csr_wv_e{i + 5}") (Wire.mk "csr_we_fcsr") frm_from_csr[i]!) ++
      (List.range 3).map (fun i =>
        Gate.mkMUX frm_reg[i]! frm_from_csr[i]! frm_csr_we frm_new[i]!)
    else []
  (fflags_gates ++ frm_gates, fflags_dff_instances ++ frm_dff_instances)

/-- Generate commit control logic (branch tracking, retire routing, store commit).
    Returns gates list. -/
def mkCommitControl
    (enableF : Bool) (_zero : Wire)
    (branch_redirect_valid_reg rob_head_valid rob_head_complete : Wire)
    (rob_commit_en rob_head_isBranch rob_head_hasOldPhysRd : Wire)
    (rob_head_isStore : Wire)
    (rob_head_physRd rob_head_oldPhysRd : List Wire)
    (retire_tag_muxed : List Wire)
    (rob_head_is_fp not_rob_head_is_fp : Wire)
    (retire_recycle_valid_filtered int_retire_valid fp_retire_recycle_valid : Wire)
    : List Gate :=
  let not_flushing := Wire.mk "not_flushing"
  let rob_commit_en_pre := Wire.mk "rob_commit_en_pre"
  let not_hasOldPhysRd := Wire.mk "not_hasOldPhysRd"
  let branch_tracking_tmp := Wire.mk "branch_tracking_tmp"
  let branch_tracking := Wire.mk "branch_tracking"
  let retire_any_old := Wire.mk "retire_any_old"
  let retire_recycle_valid := Wire.mk "retire_recycle_valid"
  let commit_store_en := Wire.mk "commit_store_en"
  let commit_gates := [
    Gate.mkNOT branch_redirect_valid_reg not_flushing,
    Gate.mkAND rob_head_valid rob_head_complete rob_commit_en_pre,
    Gate.mkAND rob_commit_en_pre not_flushing rob_commit_en,
    Gate.mkNOT rob_head_hasOldPhysRd not_hasOldPhysRd,
    Gate.mkAND rob_head_isBranch not_hasOldPhysRd branch_tracking_tmp,
    Gate.mkAND branch_tracking_tmp (Wire.mk "rob_head_hasPhysRd") branch_tracking,
    Gate.mkOR rob_head_hasOldPhysRd branch_tracking retire_any_old,
    Gate.mkAND rob_commit_en retire_any_old retire_recycle_valid,
    Gate.mkAND rob_commit_en rob_head_isStore commit_store_en
  ] ++
  (List.range 6).map (fun i =>
    Gate.mkMUX rob_head_oldPhysRd[i]! rob_head_physRd[i]! branch_tracking retire_tag_muxed[i]!)
  let retire_tag_any := Wire.mk "retire_tag_any"
  let retire_tag_or := (List.range 5).map (fun i => Wire.mk s!"retire_tag_or_{i}")
  let retire_tag_filter_gates :=
    [Gate.mkOR retire_tag_muxed[0]! retire_tag_muxed[1]! retire_tag_or[0]!] ++
    (List.range 4).map (fun i =>
      Gate.mkOR retire_tag_or[i]! retire_tag_muxed[i + 2]!
        (if i < 3 then retire_tag_or[i + 1]! else retire_tag_any)) ++
    [Gate.mkAND retire_recycle_valid retire_tag_any retire_recycle_valid_filtered]
  let fp_retire_gates :=
    if enableF then [
      Gate.mkAND retire_recycle_valid_filtered not_rob_head_is_fp int_retire_valid,
      Gate.mkAND retire_recycle_valid_filtered rob_head_is_fp fp_retire_recycle_valid,
      Gate.mkAND rob_head_hasOldPhysRd not_rob_head_is_fp (Wire.mk "int_commit_hasPhysRd"),
      Gate.mkAND (Wire.mk "rob_head_hasPhysRd") not_rob_head_is_fp (Wire.mk "int_commit_hasAllocSlot")
    ] else []
  commit_gates ++ retire_tag_filter_gates ++ fp_retire_gates

/-- Generate INT CDB forwarding logic (registered + pre-register CDB bypass).
    Returns (gates, data_gates, instances). -/
def mkCDBForwardInt
    (enableF : Bool) (_zero : Wire)
    (cdb_valid_int_domain _cdb_pre_valid : Wire)
    (cdb_tag_int cdb_pre_tag : List Wire)
    (rs1_phys rs2_phys : List Wire)
    (cdb_data_int cdb_pre_data rs1_data rs2_data : List Wire)
    (busy_src1_ready busy_src2_ready busy_src2_ready_reg : Wire)
    (fwd_src1_data fwd_src2_data : List Wire)
    (issue_src1_ready issue_src2_ready issue_src2_ready_reg : Wire)
    : (List Gate × List Gate × List CircuitInstance) :=
  let cdb_match_src1 := Wire.mk "cdb_match_src1"
  let cdb_match_src2 := Wire.mk "cdb_match_src2"
  let cdb_fwd_src1 := Wire.mk "cdb_fwd_src1"
  let cdb_fwd_src2 := Wire.mk "cdb_fwd_src2"
  let cdb_pre_match_src1 := Wire.mk "cdb_pre_match_src1"
  let cdb_pre_match_src2 := Wire.mk "cdb_pre_match_src2"
  let cdb_pre_fwd_src1 := Wire.mk "cdb_pre_fwd_src1"
  let cdb_pre_fwd_src2 := Wire.mk "cdb_pre_fwd_src2"
  let any_fwd_src1 := Wire.mk "any_fwd_src1"
  let any_fwd_src2 := Wire.mk "any_fwd_src2"
  let cdb_fwd_cmp_src1_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_cdb_fwd_cmp_src1"
    portMap := [("eq", cdb_match_src1)] ++
               (cdb_tag_int.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let cdb_fwd_cmp_src2_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_cdb_fwd_cmp_src2"
    portMap := [("eq", cdb_match_src2)] ++
               (cdb_tag_int.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let cdb_pre_fwd_cmp_src1_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_cdb_pre_fwd_cmp_src1"
    portMap := [("eq", cdb_pre_match_src1)] ++
               (cdb_pre_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let cdb_pre_fwd_cmp_src2_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_cdb_pre_fwd_cmp_src2"
    portMap := [("eq", cdb_pre_match_src2)] ++
               (cdb_pre_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let cdb_pre_valid_int_dom := if enableF then Wire.mk "cdb_pre_valid_for_int" else Wire.mk "cdb_pre_valid_nz"
  let cdb_fwd_gates := [
    Gate.mkAND cdb_valid_int_domain cdb_match_src1 cdb_fwd_src1,
    Gate.mkAND cdb_valid_int_domain cdb_match_src2 cdb_fwd_src2,
    Gate.mkAND cdb_pre_valid_int_dom cdb_pre_match_src1 cdb_pre_fwd_src1,
    Gate.mkAND cdb_pre_valid_int_dom cdb_pre_match_src2 cdb_pre_fwd_src2,
    Gate.mkOR cdb_fwd_src1 cdb_pre_fwd_src1 any_fwd_src1,
    Gate.mkOR cdb_fwd_src2 cdb_pre_fwd_src2 any_fwd_src2,
    Gate.mkOR busy_src1_ready any_fwd_src1 issue_src1_ready,
    Gate.mkOR busy_src2_ready any_fwd_src2 issue_src2_ready,
    Gate.mkOR busy_src2_ready_reg any_fwd_src2 issue_src2_ready_reg
  ]
  let fwd_src1_data_tmp := makeIndexedWires "fwd_src1_data_tmp" 32
  let fwd_src2_data_tmp := makeIndexedWires "fwd_src2_data_tmp" 32
  let fwd_src1_data_gates := (List.range 32).map (fun i =>
    [Gate.mkMUX (rs1_data[i]!) (cdb_data_int[i]!) cdb_fwd_src1 (fwd_src1_data_tmp[i]!),
     Gate.mkMUX (fwd_src1_data_tmp[i]!) (cdb_pre_data[i]!) cdb_pre_fwd_src1 (fwd_src1_data[i]!)]) |>.flatten
  let fwd_src2_data_gates := (List.range 32).map (fun i =>
    [Gate.mkMUX (rs2_data[i]!) (cdb_data_int[i]!) cdb_fwd_src2 (fwd_src2_data_tmp[i]!),
     Gate.mkMUX (fwd_src2_data_tmp[i]!) (cdb_pre_data[i]!) cdb_pre_fwd_src2 (fwd_src2_data[i]!)]) |>.flatten
  let cdb_fwd_instances := [cdb_fwd_cmp_src1_inst, cdb_fwd_cmp_src2_inst,
                             cdb_pre_fwd_cmp_src1_inst, cdb_pre_fwd_cmp_src2_inst]
  (cdb_fwd_gates, fwd_src1_data_gates ++ fwd_src2_data_gates, cdb_fwd_instances)

/-- Generate FP CDB forwarding logic with domain-aware matching.
    Returns (gates, data_gates, instances). -/
def mkCDBForwardFP
    (enableF : Bool) (_zero : Wire)
    (cdb_valid cdb_pre_valid : Wire)
    (cdb_is_fp_rd : Wire)
    (cdb_tag_fp cdb_pre_tag : List Wire)
    (fp_issue_src1_tag fp_issue_src2_tag : List Wire)
    (cdb_data_fp cdb_pre_data fp_issue_src1_data fp_issue_src2_data : List Wire)
    (busy_src1_ready busy_src2_ready : Wire)
    (fp_busy_src1_ready_raw fp_busy_src2_ready_raw : Wire)
    (decode_fp_rs1_read decode_fp_rs2_read : Wire)
    (fp_fwd_src1_data fp_fwd_src2_data : List Wire)
    (fp_issue_src1_ready fp_issue_src2_ready : Wire)
    : (List Gate × List Gate × List CircuitInstance) :=
  let fp_cdb_match_src1 := Wire.mk "fp_cdb_match_src1"
  let fp_cdb_match_src2 := Wire.mk "fp_cdb_match_src2"
  let fp_cdb_fwd_src1 := Wire.mk "fp_cdb_fwd_src1"
  let fp_cdb_fwd_src2 := Wire.mk "fp_cdb_fwd_src2"
  let fp_cdb_pre_match_src1 := Wire.mk "fp_cdb_pre_match_src1"
  let fp_cdb_pre_match_src2 := Wire.mk "fp_cdb_pre_match_src2"
  let fp_cdb_pre_fwd_src1 := Wire.mk "fp_cdb_pre_fwd_src1"
  let fp_cdb_pre_fwd_src2 := Wire.mk "fp_cdb_pre_fwd_src2"
  let fp_any_fwd_src1 := Wire.mk "fp_any_fwd_src1"
  let fp_any_fwd_src2 := Wire.mk "fp_any_fwd_src2"
  let fp_busy_src1_ready := Wire.mk "fp_busy_src1_ready"
  let fp_busy_src2_ready := Wire.mk "fp_busy_src2_ready"
  let fp_cdb_fwd_cmp_src1_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_fp_cdb_fwd_cmp_src1"
    portMap := [("eq", fp_cdb_match_src1)] ++
               (cdb_tag_fp.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (fp_issue_src1_tag.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let fp_cdb_fwd_cmp_src2_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_fp_cdb_fwd_cmp_src2"
    portMap := [("eq", fp_cdb_match_src2)] ++
               (cdb_tag_fp.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (fp_issue_src2_tag.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let fp_cdb_pre_fwd_cmp_src1_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_fp_cdb_pre_fwd_cmp_src1"
    portMap := [("eq", fp_cdb_pre_match_src1)] ++
               (cdb_pre_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (fp_issue_src1_tag.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let fp_cdb_pre_fwd_cmp_src2_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_fp_cdb_pre_fwd_cmp_src2"
    portMap := [("eq", fp_cdb_pre_match_src2)] ++
               (cdb_pre_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (fp_issue_src2_tag.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let fp_domain_xor_src1 := Wire.mk "fp_domain_xor_src1"
  let fp_domain_match_src1 := Wire.mk "fp_domain_match_src1"
  let fp_domain_xor_src2 := Wire.mk "fp_domain_xor_src2"
  let fp_domain_match_src2 := Wire.mk "fp_domain_match_src2"
  let fp_cdb_fwd_src1_tmp := Wire.mk "fp_cdb_fwd_src1_tmp"
  let fp_cdb_fwd_src2_tmp := Wire.mk "fp_cdb_fwd_src2_tmp"
  let fp_pre_domain_xor_src1 := Wire.mk "fp_pre_domain_xor_src1"
  let fp_pre_domain_match_src1 := Wire.mk "fp_pre_domain_match_src1"
  let fp_pre_domain_xor_src2 := Wire.mk "fp_pre_domain_xor_src2"
  let fp_pre_domain_match_src2 := Wire.mk "fp_pre_domain_match_src2"
  let fp_cdb_pre_fwd_src1_tmp := Wire.mk "fp_cdb_pre_fwd_src1_tmp"
  let fp_cdb_pre_fwd_src2_tmp := Wire.mk "fp_cdb_pre_fwd_src2_tmp"
  let fp_cdb_fwd_gates :=
    if enableF then [
      Gate.mkXOR cdb_is_fp_rd decode_fp_rs1_read fp_domain_xor_src1,
      Gate.mkNOT fp_domain_xor_src1 fp_domain_match_src1,
      Gate.mkXOR cdb_is_fp_rd decode_fp_rs2_read fp_domain_xor_src2,
      Gate.mkNOT fp_domain_xor_src2 fp_domain_match_src2,
      Gate.mkAND cdb_valid fp_cdb_match_src1 fp_cdb_fwd_src1_tmp,
      Gate.mkAND fp_cdb_fwd_src1_tmp fp_domain_match_src1 fp_cdb_fwd_src1,
      Gate.mkAND cdb_valid fp_cdb_match_src2 fp_cdb_fwd_src2_tmp,
      Gate.mkAND fp_cdb_fwd_src2_tmp fp_domain_match_src2 fp_cdb_fwd_src2,
      Gate.mkXOR (Wire.mk "cdb_pre_is_fp") decode_fp_rs1_read fp_pre_domain_xor_src1,
      Gate.mkNOT fp_pre_domain_xor_src1 fp_pre_domain_match_src1,
      Gate.mkXOR (Wire.mk "cdb_pre_is_fp") decode_fp_rs2_read fp_pre_domain_xor_src2,
      Gate.mkNOT fp_pre_domain_xor_src2 fp_pre_domain_match_src2,
      Gate.mkAND cdb_pre_valid fp_cdb_pre_match_src1 fp_cdb_pre_fwd_src1_tmp,
      Gate.mkAND fp_cdb_pre_fwd_src1_tmp fp_pre_domain_match_src1 fp_cdb_pre_fwd_src1,
      Gate.mkAND cdb_pre_valid fp_cdb_pre_match_src2 fp_cdb_pre_fwd_src2_tmp,
      Gate.mkAND fp_cdb_pre_fwd_src2_tmp fp_pre_domain_match_src2 fp_cdb_pre_fwd_src2,
      Gate.mkOR fp_cdb_fwd_src1 fp_cdb_pre_fwd_src1 fp_any_fwd_src1,
      Gate.mkOR fp_cdb_fwd_src2 fp_cdb_pre_fwd_src2 fp_any_fwd_src2,
      Gate.mkMUX busy_src1_ready fp_busy_src1_ready_raw decode_fp_rs1_read fp_busy_src1_ready,
      Gate.mkMUX busy_src2_ready fp_busy_src2_ready_raw decode_fp_rs2_read fp_busy_src2_ready,
      Gate.mkOR fp_busy_src1_ready fp_any_fwd_src1 fp_issue_src1_ready,
      Gate.mkOR fp_busy_src2_ready fp_any_fwd_src2 fp_issue_src2_ready
    ] else []
  let fp_fwd_src1_tmp := makeIndexedWires "fp_fwd_src1_tmp" 32
  let fp_fwd_src2_tmp := makeIndexedWires "fp_fwd_src2_tmp" 32
  let fp_fwd_data_gates :=
    if enableF then
      ((List.range 32).map (fun i =>
        [Gate.mkMUX fp_issue_src1_data[i]! cdb_data_fp[i]! fp_cdb_fwd_src1 fp_fwd_src1_tmp[i]!,
         Gate.mkMUX fp_fwd_src1_tmp[i]! cdb_pre_data[i]! fp_cdb_pre_fwd_src1 fp_fwd_src1_data[i]!]) |>.flatten) ++
      ((List.range 32).map (fun i =>
        [Gate.mkMUX fp_issue_src2_data[i]! cdb_data_fp[i]! fp_cdb_fwd_src2 fp_fwd_src2_tmp[i]!,
         Gate.mkMUX fp_fwd_src2_tmp[i]! cdb_pre_data[i]! fp_cdb_pre_fwd_src2 fp_fwd_src2_data[i]!]) |>.flatten)
    else []
  let fp_cdb_fwd_instances :=
    if enableF then
      [fp_cdb_fwd_cmp_src1_inst, fp_cdb_fwd_cmp_src2_inst,
       fp_cdb_pre_fwd_cmp_src1_inst, fp_cdb_pre_fwd_cmp_src2_inst]
    else []
  (fp_cdb_fwd_gates, fp_fwd_data_gates, fp_cdb_fwd_instances)

/-- Generate a 4-entry × 32-bit sidecar register file.
    Used for immediate, PC, and other per-RS-entry storage.
    Returns (rf_gates, rf_entries, decoder_inst, mux_inst). -/
def mkSidecarRegFile4x32
    (pfx : String)
    (clock reset : Wire)
    (alloc_ptr : List Wire) (we_en : Wire)
    (write_data : List Wire) (grant : List Wire)
    (captured_out : List Wire)
    : (List Gate × List (List Wire) × CircuitInstance × CircuitInstance) :=
  let decoded := makeIndexedWires s!"{pfx}_decoded" 4
  let we := makeIndexedWires s!"{pfx}_we" 4
  let decoder_inst : CircuitInstance := {
    moduleName := "Decoder2"
    instName := s!"u_{pfx}_dec"
    portMap := [
      ("in_0", alloc_ptr[0]!), ("in_1", alloc_ptr[1]!),
      ("out_0", decoded[0]!), ("out_1", decoded[1]!),
      ("out_2", decoded[2]!), ("out_3", decoded[3]!)
    ]
  }
  let we_gates := (List.range 4).map (fun e =>
    Gate.mkAND decoded[e]! we_en we[e]!)
  let entries := (List.range 4).map (fun e =>
    makeIndexedWires s!"{pfx}_e{e}" 32)
  let rf_gates := (List.range 4).map (fun e =>
    let entry := entries[e]!
    (List.range 32).map (fun b =>
      let next := Wire.mk s!"{pfx}_next_e{e}_{b}"
      [ Gate.mkMUX entry[b]! write_data[b]! we[e]! next,
        Gate.mkDFF next clock reset entry[b]! ]
    ) |>.flatten
  ) |>.flatten
  let sel := makeIndexedWires s!"{pfx}_sel" 2
  let sel_gates := [
    Gate.mkOR grant[1]! grant[3]! sel[0]!,
    Gate.mkOR grant[2]! grant[3]! sel[1]!
  ]
  let mux_inst : CircuitInstance := {
    moduleName := "Mux4x32"
    instName := s!"u_{pfx}_mux"
    portMap :=
      (((List.range 4).map (fun e =>
          (List.range 32).map (fun b =>
            (s!"in{e}[{b}]", entries[e]![b]!)
          )
        )).flatten) ++
      (sel.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w))) ++
      (captured_out.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w)))
  }
  (we_gates ++ rf_gates ++ sel_gates, entries, decoder_inst, mux_inst)

end

end Shoumei.RISCV.CPU

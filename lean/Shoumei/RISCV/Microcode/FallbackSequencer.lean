/-
FallbackSequencer.lean - Microcoded fallback execution sequencer.

A dedicated sequential circuit that emulates the 43 undecoded Zb* bit
manipulation encodings, or vectors an unallocated encoding to an architectural
illegal instruction trap.  It is a control-store machine: a micro-PC selects a
32-bit micro-op from the control store (`ZbEmulationLibrary.zbRom`), the
micro-ALU in this file executes it against a four-entry scratchpad, and
`MOV_TO_RD` publishes the result on the CDB.

    start ─┐
           ▼
    ┌──────────────┐   base    ┌───────────┐
    │ 43 match     │──────────▶│  ridx_q   │ 6
    │ terms + prio │  matched  └─────┬─────┘
    └──────────────┘           step_q │ 3        ┌──────────┐
                                     └────────────┼─▶│  zbRom   │
                                                  │  └────┬─────┘
                                                  │       │ 32
                            temp0..3 ◀── temp file ◀── micro-ALU
                                                  │       │
                                                  ▼       ▼
                                                CDB inject / redirect / trap
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.Register
import Shoumei.RISCV.Microcode.ZbEmulationLibrary

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

/-- Ripple carry adder over `a.length` bits -/
private def mkAdderN (pfx : String) (a b : List Wire) (cin : Wire) : (List Gate × List Wire × Wire) :=
  (List.range a.length).foldl (fun (gates, sum_wires, c_in) i =>
    let cell := mkFullAdderCell pfx i a[i]! b[i]! c_in
    (gates ++ cell.1, sum_wires ++ [cell.2.1], cell.2.2)
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

/-- Binary mux tree: selects `inputs[i]`, `i` being the value on `sel` (LSB
    first).  `inputs.length` must be `2 ^ sel.length`. -/
private def mkMuxTree (pfx : String) (inputs : List Wire) (sel : List Wire) : List Gate × Wire :=
  let res : List Gate × List Wire := (List.range sel.length).foldl (fun (st : List Gate × List Wire) lvl =>
    if st.2.length ≤ 1 then st
    else
      let s := sel.getD lvl (Wire.mk "zero")
      let half := st.2.length / 2
      let next := makeWires s!"{pfx}_L{lvl}" half
      let g := (List.range half).map fun i =>
        Gate.mkMUX st.2[2 * i]! st.2[2 * i + 1]! s next[i]!
      (st.1 ++ g, next)) ([], inputs)
  (res.1, res.2.headD (Wire.mk "zero"))

/-- Binary mux tree over whole vectors: selects `inputs[i]` bit by bit. -/
private def mkMuxTreeVec (pfx : String) (inputs : List (List Wire))
    (sel : List Wire) : List Gate × List Wire :=
  let n := (inputs.headD []).length
  let res : List Gate × List Wire := (List.range n).foldl (fun (st : List Gate × List Wire) b =>
    let r := mkMuxTree s!"{pfx}_{b}" (inputs.map (fun v => v[b]!)) sel
    (st.1 ++ r.1, st.2 ++ [r.2])
  ) ([], [])
  (res.1, res.2)

/-- 6-bit compare of the micro-opcode field against `op` -/
private def mkOpMatch (pfx : String) (bits nbits : List Wire) (val : Nat) : List Gate × Wire :=
  let b := (List.range 6).map fun i => if val.testBit i then bits[i]! else nbits[i]!
  let t01 := Wire.mk s!"{pfx}_t01"
  let t23 := Wire.mk s!"{pfx}_t23"
  let t45 := Wire.mk s!"{pfx}_t45"
  let t0123 := Wire.mk s!"{pfx}_t0123"
  let out := Wire.mk pfx
  ([Gate.mkAND b[0]! b[1]! t01,
    Gate.mkAND b[2]! b[3]! t23,
    Gate.mkAND b[4]! b[5]! t45,
    Gate.mkAND t01 t23 t0123,
    Gate.mkAND t0123 t45 out], out)

/-- 6-stage barrel shifter, right shift, filling the vacated high bits with
    `fillBit`.  A stage performs nothing when its shift-amount bit is low, so a
    zero shift amount is the identity -/
private def mkBarrelRight (pfx : String) (x : List Wire) (sh : List Wire)
    (fillBit : Wire) : List Gate × List Wire :=
  let stage (k : Nat) (inp : List Wire) (gates : List Gate) : List Gate × List Wire :=
    let n := 2 ^ k
    let outs := makeWires s!"{pfx}_s{k}" 64
    let g := (List.range 64).map fun i =>
      if i + n < 64 then Gate.mkMUX inp[i]! inp[i + n]! sh[k]! outs[i]!
      else Gate.mkMUX inp[i]! fillBit sh[k]! outs[i]!
    (gates ++ g, outs)
  let stgg1 : List Gate × List Wire := stage 0 x []
  let g1 := stgg1.1
  let w1 := stgg1.2
  let stgg2 : List Gate × List Wire := stage 1 w1 g1
  let g2 := stgg2.1
  let w2 := stgg2.2
  let stgg3 : List Gate × List Wire := stage 2 w2 g2
  let g3 := stgg3.1
  let w3 := stgg3.2
  let stgg4 : List Gate × List Wire := stage 3 w3 g3
  let g4 := stgg4.1
  let w4 := stgg4.2
  let stgg5 : List Gate × List Wire := stage 4 w4 g4
  let g5 := stgg5.1
  let w5 := stgg5.2
  let stgg6 : List Gate × List Wire := stage 5 w5 g5
  let g6 := stgg6.1
  let w6 := stgg6.2
  (g6, w6)

/-- 6-stage barrel shifter, left shift, zero fill -/
private def mkBarrelLeft (pfx : String) (x : List Wire) (sh : List Wire) : List Gate × List Wire :=
  let stage (k : Nat) (inp : List Wire) (gates : List Gate) : List Gate × List Wire :=
    let n := 2 ^ k
    let outs := makeWires s!"{pfx}_s{k}" 64
    let g := (List.range 64).map fun i =>
      if n ≤ i then Gate.mkMUX inp[i]! inp[i - n]! sh[k]! outs[i]!
      else Gate.mkMUX inp[i]! (Wire.mk "zero") sh[k]! outs[i]!
    (gates ++ g, outs)
  let stgg1 : List Gate × List Wire := stage 0 x []
  let g1 := stgg1.1
  let w1 := stgg1.2
  let stgg2 : List Gate × List Wire := stage 1 w1 g1
  let g2 := stgg2.1
  let w2 := stgg2.2
  let stgg3 : List Gate × List Wire := stage 2 w2 g2
  let g3 := stgg3.1
  let w3 := stgg3.2
  let stgg4 : List Gate × List Wire := stage 3 w3 g3
  let g4 := stgg4.1
  let w4 := stgg4.2
  let stgg5 : List Gate × List Wire := stage 4 w4 g4
  let g5 := stgg5.1
  let w5 := stgg5.2
  let stgg6 : List Gate × List Wire := stage 5 w5 g5
  let g6 := stgg6.1
  let w6 := stgg6.2
  (g6, w6)

/-- 5-stage 32-bit rotator.  `dirLeft` picks the rotation direction -/
private def mkRotate32 (pfx : String) (x : List Wire) (sh : List Wire)
    (dirLeft : Bool) : List Gate × List Wire :=
  let stage (k : Nat) (inp : List Wire) (gates : List Gate) : List Gate × List Wire :=
    let n := 2 ^ k
    let outs := makeWires s!"{pfx}_s{k}" 32
    let g := (List.range 32).map fun i =>
      let j := if dirLeft then (i + 32 - n) % 32 else (i + n) % 32
      Gate.mkMUX inp[i]! inp[j]! sh[k]! outs[i]!
    (gates ++ g, outs)
  let stgg1 : List Gate × List Wire := stage 0 x []
  let g1 := stgg1.1
  let w1 := stgg1.2
  let stgg2 : List Gate × List Wire := stage 1 w1 g1
  let g2 := stgg2.1
  let w2 := stgg2.2
  let stgg3 : List Gate × List Wire := stage 2 w2 g2
  let g3 := stgg3.1
  let w3 := stgg3.2
  let stgg4 : List Gate × List Wire := stage 3 w3 g3
  let g4 := stgg4.1
  let w4 := stgg4.2
  let stgg5 : List Gate × List Wire := stage 4 w4 g4
  let g5 := stgg5.1
  let w5 := stgg5.2
  (g5, w5)

/-- Sign-extend a 32-bit vector to 64 bits -/
private def mkSext32 (pfx : String) (v : List Wire) : List Gate × List Wire :=
  let sign := Wire.mk s!"{pfx}_sign"
  let outs := makeWires pfx 64
  let g := [Gate.mkMUX (Wire.mk "zero") (Wire.mk "one") v[31]! sign] ++
    (List.range 32).map (fun i => Gate.mkBUF v[i]! outs[i]!) ++
    (List.range 32).map (fun i => Gate.mkBUF sign outs[32 + i]!)
  (g, outs)

/-- Zero-extend the low 32 bits of a 64-bit vector -/
private def mkZext32 (pfx : String) (v : List Wire) : List Gate × List Wire :=
  let outs := makeWires pfx 64
  let g := (List.range 32).map (fun i => Gate.mkBUF v[i]! outs[i]!) ++
    (List.range 32).map (fun i => Gate.mkBUF (Wire.mk "zero") outs[32 + i]!)
  (g, outs)

/-- One output bit of a carry-less multiply: XOR of `a[j] & b[k]` over every
    `j + k = i + offset` with `j, k < 64`.  `offset` 0 selects `clmul`, 64
    `clmulh` and 63 `clmulr` -/
private def mkClmulBit (pfx : String) (a b : List Wire) (i offset : Nat) : List Gate × Wire :=
  let lo := if 63 ≤ i + offset then i + offset - 63 else 0
  let hi := min 63 (i + offset)
  let terms := (List.range (hi + 1 - lo)).map fun d =>
    let j := lo + d
    let w := Wire.mk s!"{pfx}_a_{i}_{j}"
    (Gate.mkAND a[i + offset - j]! b[j]! w, w)
  let agates := terms.map (·.1)
  let xr := mkXorTree s!"{pfx}_x{i}" (terms.map (·.2))
  (agates ++ xr.1, xr.2)

/-- Full carry-less multiply datapath for one offset -/
private def mkClmul (pfx : String) (a b : List Wire) (offset : Nat) : List Gate × List Wire :=
  let outs := makeWires pfx 64
  let g := (List.range 64).flatMap fun i =>
    let r := mkClmulBit pfx a b i offset
    r.1 ++ [Gate.mkBUF r.2 outs[i]!]
  (g, outs)

/-- Population count of `bits`, zero-extended to 64 bits.  Balanced adder tree:
    the sums double in width once per level -/
private def mkPopCount (pfx : String) (bits : List Wire) : List Gate × List Wire :=
  let pad (n : Nat) (ws : List Wire) : List Wire :=
    ws ++ List.replicate (n - ws.length) (Wire.mk "zero")
  -- One round halves the number of partial sums, doubling each one's width.
  let oneRound (lvl : Nat) (ws : List (List Wire)) : List (List Wire) × List Gate :=
    let half := (ws.length + 1) / 2
    (List.range half).foldl (fun (acc : List (List Wire) × List Gate) i =>
      let x := ws.getD (2 * i) []
      let y := ws.getD (2 * i + 1) []
      if y.isEmpty then (acc.1 ++ [x], acc.2)
      else
        let w := max x.length y.length
        let r := mkAdderN s!"{pfx}_{lvl}_{i}" (pad w x) (pad w y) (Wire.mk "zero")
        (acc.1 ++ [r.2.1 ++ [r.2.2]], acc.2 ++ r.1)) ([], [])
  let res : List (List Wire) × List Gate := (List.range 7).foldl (fun (st : List (List Wire) × List Gate) lvl =>
      if st.1.length ≤ 1 then st
      else
        let r := oneRound lvl st.1
        (r.1, st.2 ++ r.2)) (bits.map (fun b => [b]), [])
  let out := res.1.headD []
  (res.2, out ++ List.replicate (64 - out.length) (Wire.mk "zero"))

/-- Build the Fallback Sequencer Circuit.

    Inputs:
    - clock, reset
    - start: trigger from decode (when the instruction is undecoded)
    - pipeline_flush: a redirect that squashes the sequence
    - insn[31:0]: captured instruction word
    - pc_in[63:0]: PC of the un-decoded instruction
    - rs1_val[63:0], rs2_val[63:0]: source operands, final once drained
    - rd_tag_in[5:0]: physical destination register tag
    - rob_empty, sb_empty: pipeline drain complete

    Outputs:
    - active: sequencer running (suppresses fetch/decode)
    - cdb_inject: CDB write strobe, exactly one pulse per emulated instruction
    - cdb_tag[5:0]: physical tag for PRF write
    - cdb_data[63:0]: result data for PRF write
    - redir_valid: fetch redirect strobe
    - redir_pc[63:0]: target PC (pc+4 on success)
    - trap_active: asserted when the illegal instruction exception is taken
    - trap_cause[63:0]: exception code (2 for illegal instruction)
    - trap_val[63:0]: faulting instruction word for mtval
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

  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- Active state register
  let active_q := Wire.mk "active"
  let active_next := Wire.mk "active_next"
  let done_or_flush := Wire.mk "done_or_flush"
  let not_done_flush := Wire.mk "not_done_flush"
  let active_keep := Wire.mk "active_keep"

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

  -- === ROUTINE SELECTION ===
  -- One AND-term per emulated encoding: every bit the entry's mask fixes must
  -- equal its sample.  A 43-to-6 priority encoder picks the first (lowest
  -- index) hit, matching `routineIndex`'s `find?`; no encoding is ambiguous,
  -- so priority never actually arbitrates.
  let insn_in_n := makeWires "n_insn_in" 32
  let insnInvGates := (List.range 32).map fun i => Gate.mkNOT insn_in[i]! insn_in_n[i]!
  let hitWires := (List.finRange routineCount).map fun r => Wire.mk s!"zb_hit_{r.val}"
  let hitGates := (List.finRange routineCount).flatMap fun r =>
    let e := zbEntry r
    let terms := (List.range 32).filterMap fun b =>
      if ((e.mask.toNat >>> b) % 2) == 1 then
        some (if ((e.sample.toNat >>> b) % 2) == 1 then insn_in[b]! else insn_in_n[b]!)
      else none
    let (w, g) := terms.enum.foldl (fun (st : Wire × List Gate) ⟨i, t⟩ =>
      let o := Wire.mk s!"zb_and_{r.val}_{i}"
      (o, st.2 ++ [Gate.mkAND st.1 t o])) (one, [])
    g ++ [Gate.mkBUF w hitWires[r.val]!]
  -- Priority mask: hit `r` wins only if no lower-indexed entry hit.
  let prioWires := (List.finRange routineCount).map fun r => Wire.mk s!"zb_prio_{r.val}"
  let prioGates := (List.finRange routineCount).flatMap fun r =>
    let prev := (List.finRange r.val).map fun k => hitWires.getD k.val zero
    let orr := mkOrTree s!"zb_prev_{r.val}" prev
    orr.1 ++ [Gate.mkNOT orr.2 (Wire.mk s!"zb_nprev_{r.val}"),
                Gate.mkAND hitWires[r.val]! (Wire.mk s!"zb_nprev_{r.val}") prioWires[r.val]!]
  let anyHitR : List Gate × Wire := mkOrTree "zb_any" hitWires
  let anyHitGates := anyHitR.1
  let anyHit := anyHitR.2
  let ridxEnc := (List.range 6).map fun j =>
    let bits := (List.finRange routineCount).filterMap fun r =>
      if (r.val >>> j) % 2 == 1 then some prioWires[r.val] else none
    let r := mkOrTree s!"zb_enc{j}" bits
    (r.1, r.2, j)
  let encGates : List Gate := ridxEnc.map (·.1) |>.flatten
  let matched_enc := anyHit
  let not_matched_enc := Wire.mk "n_matched_enc"
  let selGates := [
    Gate.mkNOT matched_enc not_matched_enc
  ] ++ ridxEnc.flatMap fun (_, o, j) =>
    -- unmatched selects routine slot `routineCount` (43 = 0b101011)
    if (routineCount >>> j) % 2 == 1 then
      [Gate.mkOR o not_matched_enc (Wire.mk s!"zb_ridx_{j}")]
    else
      [Gate.mkBUF o (Wire.mk s!"zb_ridx_{j}")]
  let ridx_in := (List.range 6).map fun j => Wire.mk s!"zb_ridx_{j}"
  let matched_d := Wire.mk "matched_d"
  let matchedGates := [
    Gate.mkMUX (Wire.mk "matched_q") matched_enc start matched_d,
    Gate.mkDFF matched_d clock reset (Wire.mk "matched_q")
  ]
  let matched := Wire.mk "matched_q"

  -- === MICRO-PC ===
  -- `ridx_q` selects the routine, `step_q` the micro-op inside it.
  let ridx_d := makeWires "ridx_d" 6
  let ridx_q := makeWires "ridx_q" 6
  let step_q := makeWires "step_q" 3
  let step_d := makeWires "step_d" 3
  let step_pre := makeWires "step_pre" 3
  let step_c0 := Wire.mk "step_c0"
  let step_c1 := Wire.mk "step_c1"
  let not_hold := Wire.mk "not_hold"
  let step_en := Wire.mk "step_en"
  let upcGates :=
    (List.range 6).map (fun i => Gate.mkMUX ridx_q[i]! ridx_in[i]! start ridx_d[i]!) ++
    (List.range 6).map (fun i => Gate.mkDFF ridx_d[i]! clock reset ridx_q[i]!) ++
    [Gate.mkNOT step_q[0]! step_c0,
     Gate.mkXOR step_q[1]! step_q[0]! step_c1,
     Gate.mkAND step_q[0]! step_q[1]! (Wire.mk "step_c2"),
     Gate.mkXOR step_q[2]! (Wire.mk "step_c2") (Wire.mk "step_c3")] ++
    [Gate.mkMUX step_q[0]! step_c0 step_en step_pre[0]!,
     Gate.mkMUX step_q[1]! step_c1 step_en step_pre[1]!,
     Gate.mkMUX step_q[2]! (Wire.mk "step_c3") step_en step_pre[2]!,
     Gate.mkMUX step_pre[0]! zero start step_d[0]!,
     Gate.mkMUX step_pre[1]! zero start step_d[1]!,
     Gate.mkMUX step_pre[2]! zero start step_d[2]!] ++
    (List.range 3).map (fun i => Gate.mkDFF step_d[i]! clock reset step_q[i]!)

  -- === CONTROL STORE ===
  -- 512 x 32-bit, addressed by `ridx_q & step_q`, realized as a mux tree on
  -- the 32 field bits.  Entries past a routine's last micro-op are `.DONE`.
  let romGates := (List.range 32).flatMap fun b =>
    let leaves := (List.range zbRomSize).map fun k =>
      if ((zbRom k).encode >>> b) % 2 == 1 then one else zero
    let r := mkMuxTree s!"rom_m{b}" leaves (step_q ++ ridx_q)
    r.1 ++ [Gate.mkBUF r.2 (Wire.mk s!"rom_b{b}")]
  let romData := (List.range 32).map fun b => Wire.mk s!"rom_b{b}"
  let romOp := (List.range 6).map fun i => romData[26 + i]!
  let romOpN := makeWires "n_rom_op" 6
  let romDst := (List.range 2).map fun i => romData[24 + i]!
  let romSrc1 := (List.range 2).map fun i => romData[22 + i]!
  let romSrc2 := (List.range 2).map fun i => romData[20 + i]!
  let romImm := (List.range 16).map fun i => romData[i]!
  let romInvGates := (List.range 6).map fun i => Gate.mkNOT romOp[i]! romOpN[i]!

  -- Micro-opcode decode: one match wire per micro-op the routines use.  Each
  -- `is_<n>` wire is defined exactly once, so every consumer shares it.
  let aluOpList : List FallbackOp :=
    [.ALU_ANDN, .ALU_ORN, .ALU_XNOR, .ALU_BSET, .ALU_BCLR, .ALU_BINV, .ALU_BEXT,
     .ALU_SH1ADD, .ALU_SH2ADD, .ALU_SH3ADD, .ALU_ADD, .ALU_SUB,
     .ALU_MIN, .ALU_MAX, .ALU_MINU, .ALU_MAXU, .ALU_ROL, .ALU_ROR,
     .ALU_ROLW, .ALU_RORW, .ALU_SLL, .ALU_SRL, .ALU_SRA,
     .ALU_CLMUL, .ALU_CLMULH, .ALU_CLMULR, .ALU_ZEXT_W, .ALU_SEXT_W,
     .ALU_CLZ, .ALU_CTZ, .ALU_CPOP, .ALU_CTZW, .ALU_ORCB, .ALU_REV8]
  let opMatchGates :=
    ([FallbackOp.DRAIN, .DONE, .MOV_TO_RD, .LOAD_RS1, .LOAD_RS2, .LOAD_SHAMT, .LOAD_IMM] ++
      aluOpList).flatMap
      fun op => (mkOpMatch s!"is_{op.toNat}" romOp romOpN op.toNat).1
  let isOp : FallbackOp → Wire := fun op => Wire.mk s!"is_{op.toNat}"
  let isDrain := isOp .DRAIN
  let isDone := isOp .DONE

  -- `hold` stalls the micro-PC while a DRAIN micro-op waits for the pipeline.
  let hold := Wire.mk "hold"
  let holdGates := [
    Gate.mkNOT drained (Wire.mk "n_drained"),
    Gate.mkAND isDrain (Wire.mk "n_drained") hold,
    Gate.mkNOT hold not_hold,
    Gate.mkAND active_q not_hold step_en
  ]

  -- Sequence completion
  let done := Wire.mk "done"
  let doneGates := [
    Gate.mkAND step_en isDone done,
    Gate.mkOR done pipeline_flush done_or_flush,
    Gate.mkNOT done_or_flush not_done_flush,
    Gate.mkAND active_q not_done_flush active_keep,
    Gate.mkOR start active_keep active_next,
    Gate.mkDFF active_next clock reset active_q
  ]

  -- Capture registers for instruction, PC, rd tag (at start) and the operands
  -- (once the pipeline has drained and the CDB snoop has filled them in).
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
  let op_latch := Wire.mk "op_latch"
  let captureGates := [
    Gate.mkAND step_en isDrain op_latch
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

  -- === SCRATCHPAD ===
  let tempsD := (List.range 4).map fun k => makeWires s!"temp{k}_d" 64
  let tempsQ := (List.range 4).map fun k => makeWires s!"temp{k}_q" 64

  -- === MICRO-ALU ===
  let src1Mux : List Gate × List Wire := mkMuxTreeVec "src1_val" tempsQ romSrc1
  let src1MuxGates := src1Mux.1
  let src1_val := src1Mux.2
  let src2Mux : List Gate × List Wire := mkMuxTreeVec "src2_val" tempsQ romSrc2
  let src2MuxGates := src2Mux.1
  let src2_val := src2Mux.2

  -- Logic with negate
  let andn_val := makeWires "andn_val" 64
  let orn_val := makeWires "orn_val" 64
  let xnor_val := makeWires "xnor_val" 64
  let logicGates := (List.range 64).flatMap fun i =>
    let n_rs2 := Wire.mk s!"n_rs2_{i}"
    let x_rs := Wire.mk s!"x_rs_{i}"
    [Gate.mkNOT src2_val[i]! n_rs2,
     Gate.mkAND src1_val[i]! n_rs2 andn_val[i]!,
     Gate.mkOR src1_val[i]! n_rs2 orn_val[i]!,
     Gate.mkXOR src1_val[i]! src2_val[i]! x_rs,
     Gate.mkNOT x_rs xnor_val[i]!]

  -- Single-bit ops: a 64-bit one-hot mask from the low 6 bits of src2
  let n_shamt := (List.range 6).map fun i => Wire.mk s!"n_shamt_{i}"
  let shamtInvGates := (List.range 6).map fun i => Gate.mkNOT src2_val[i]! n_shamt[i]!
  let bit_mask := makeWires "bit_mask" 64
  let maskGates := (List.range 64).flatMap fun k =>
    let b0 := if k % 2 == 1 then src2_val[0]! else n_shamt[0]!
    let b1 := if (k / 2) % 2 == 1 then src2_val[1]! else n_shamt[1]!
    let b2 := if (k / 4) % 2 == 1 then src2_val[2]! else n_shamt[2]!
    let b3 := if (k / 8) % 2 == 1 then src2_val[3]! else n_shamt[3]!
    let b4 := if (k / 16) % 2 == 1 then src2_val[4]! else n_shamt[4]!
    let b5 := if (k / 32) % 2 == 1 then src2_val[5]! else n_shamt[5]!
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
    [Gate.mkOR src1_val[i]! bit_mask[i]! bset_val[i]!,
     Gate.mkNOT bit_mask[i]! n_mask,
     Gate.mkAND src1_val[i]! n_mask bclr_val[i]!,
     Gate.mkXOR src1_val[i]! bit_mask[i]! binv_val[i]!,
     Gate.mkAND src1_val[i]! bit_mask[i]! bext_terms[i]!]
  let bextOr : List Gate × Wire := mkOrTree "bext" bext_terms
  let bextOrGates := bextOr.1
  let bext_bit := bextOr.2
  let bext_val := makeWires "bext_val" 64
  let bextGates := bextOrGates ++
    [Gate.mkBUF bext_bit bext_val[0]!] ++
    (List.range 63).map (fun i => Gate.mkBUF zero bext_val[i + 1]!)

  -- Shifted adds
  let sh_rs1 := makeWires "sh_rs1" 64
  let shMuxGates := (List.range 64).flatMap fun i =>
    let s1 := if i >= 1 then src1_val[i - 1]! else zero
    let s2 := if i >= 2 then src1_val[i - 2]! else zero
    let s3 := if i >= 3 then src1_val[i - 3]! else zero
    let tmp := Wire.mk s!"sh_tmp_{i}"
    [Gate.mkMUX s1 s2 (isOp .ALU_SH2ADD) tmp,
     Gate.mkMUX tmp s3 (isOp .ALU_SH3ADD) sh_rs1[i]!]
  let shaddAdd : List Gate × List Wire × Wire := mkAdderN "shadd" sh_rs1 src2_val zero
  let shaddAdderGates := shaddAdd.1
  let shadd_val := shaddAdd.2.1

  -- Add / subtract
  let addRes : List Gate × List Wire × Wire := mkAdderN "add" src1_val src2_val zero
  let addGates := addRes.1
  let add_val := addRes.2.1
  let n_rs2_sub := makeWires "n_rs2_sub" 64
  let subInvGates := (List.range 64).map fun i => Gate.mkNOT src2_val[i]! n_rs2_sub[i]!
  let subRes : List Gate × List Wire × Wire := mkAdderN "sub" src1_val n_rs2_sub one
  let subGates := subRes.1
  let sub_val := subRes.2.1
  let cout_sub := subRes.2.2

  -- Min / max
  let rs1_lt_u := Wire.mk "rs1_lt_u"
  let rs1_lt_s := Wire.mk "rs1_lt_s"
  let diff_sign := Wire.mk "diff_sign"
  let cmpGates := [
    Gate.mkNOT cout_sub rs1_lt_u,
    Gate.mkXOR src1_val[63]! src2_val[63]! diff_sign,
    Gate.mkMUX rs1_lt_u src1_val[63]! diff_sign rs1_lt_s
  ]
  let min_val := makeWires "min_val" 64
  let max_val := makeWires "max_val" 64
  let minu_val := makeWires "minu_val" 64
  let maxu_val := makeWires "maxu_val" 64
  let minMaxGates := (List.range 64).flatMap fun i =>
    [Gate.mkMUX src2_val[i]! src1_val[i]! rs1_lt_s min_val[i]!,
     Gate.mkMUX src1_val[i]! src2_val[i]! rs1_lt_s max_val[i]!,
     Gate.mkMUX src2_val[i]! src1_val[i]! rs1_lt_u minu_val[i]!,
     Gate.mkMUX src1_val[i]! src2_val[i]! rs1_lt_u maxu_val[i]!]

  -- 64-bit rotates
  let ror_val := makeWires "ror_val" 64
  let rol_val := makeWires "rol_val" 64
  let rorGates :=
    (List.range 64).map (fun i => Gate.mkMUX src1_val[i]! src1_val[(i + 1) % 64]! src2_val[0]! (Wire.mk s!"ror0_{i}")) ++
    (List.range 64).map (fun i => Gate.mkMUX (Wire.mk s!"ror0_{i}") (Wire.mk s!"ror0_{(i + 2) % 64}") src2_val[1]! (Wire.mk s!"ror1_{i}")) ++
    (List.range 64).map (fun i => Gate.mkMUX (Wire.mk s!"ror1_{i}") (Wire.mk s!"ror1_{(i + 4) % 64}") src2_val[2]! (Wire.mk s!"ror2_{i}")) ++
    (List.range 64).map (fun i => Gate.mkMUX (Wire.mk s!"ror2_{i}") (Wire.mk s!"ror2_{(i + 8) % 64}") src2_val[3]! (Wire.mk s!"ror3_{i}")) ++
    (List.range 64).map (fun i => Gate.mkMUX (Wire.mk s!"ror3_{i}") (Wire.mk s!"ror3_{(i + 16) % 64}") src2_val[4]! (Wire.mk s!"ror4_{i}")) ++
    (List.range 64).map (fun i => Gate.mkMUX (Wire.mk s!"ror4_{i}") (Wire.mk s!"ror4_{(i + 32) % 64}") src2_val[5]! ror_val[i]!) ++
    (List.range 64).map (fun i => Gate.mkMUX src1_val[i]! src1_val[(i + 64 - 1) % 64]! src2_val[0]! (Wire.mk s!"rol0_{i}")) ++
    (List.range 64).map (fun i => Gate.mkMUX (Wire.mk s!"rol0_{i}") (Wire.mk s!"rol0_{(i + 64 - 2) % 64}") src2_val[1]! (Wire.mk s!"rol1_{i}")) ++
    (List.range 64).map (fun i => Gate.mkMUX (Wire.mk s!"rol1_{i}") (Wire.mk s!"rol1_{(i + 64 - 4) % 64}") src2_val[2]! (Wire.mk s!"rol2_{i}")) ++
    (List.range 64).map (fun i => Gate.mkMUX (Wire.mk s!"rol2_{i}") (Wire.mk s!"rol2_{(i + 64 - 8) % 64}") src2_val[3]! (Wire.mk s!"rol3_{i}")) ++
    (List.range 64).map (fun i => Gate.mkMUX (Wire.mk s!"rol3_{i}") (Wire.mk s!"rol3_{(i + 64 - 16) % 64}") src2_val[4]! (Wire.mk s!"rol4_{i}")) ++
    (List.range 64).map (fun i => Gate.mkMUX (Wire.mk s!"rol4_{i}") (Wire.mk s!"rol4_{(i + 64 - 32) % 64}") src2_val[5]! rol_val[i]!)

  -- 32-bit rotates, sign-extended
  let rolw32 := (mkRotate32 "rolw32" (src1_val.take 32) (src2_val.take 5) true)
  let rorw32 := (mkRotate32 "rorw32" (src1_val.take 32) (src2_val.take 5) false)
  let rolwS : List Gate × List Wire := mkSext32 "rolw" rolw32.2
  let rolwSext := rolwS.1
  let rolw_val := rolwS.2
  let rorwS : List Gate × List Wire := mkSext32 "rorw" rorw32.2
  let rorwSext := rorwS.1
  let rorw_val := rorwS.2

  -- Barrel shifters
  let sllR : List Gate × List Wire := mkBarrelLeft "sll" src1_val (src2_val.take 6)
  let sllGates := sllR.1
  let sll_val := sllR.2
  let srlR : List Gate × List Wire := mkBarrelRight "srl" src1_val (src2_val.take 6) zero
  let srlGates := srlR.1
  let srl_val := srlR.2
  let sraR : List Gate × List Wire := mkBarrelRight "sra" src1_val (src2_val.take 6) src1_val[63]!
  let sraGates := sraR.1
  let sra_val := sraR.2

  -- Carry-less multiplies
  let clmulR : List Gate × List Wire := mkClmul "clmul" src1_val src2_val 0
  let clmulGates := clmulR.1
  let clmul_val := clmulR.2
  let clmulhR : List Gate × List Wire := mkClmul "clmulh" src1_val src2_val 64
  let clmulhGates := clmulhR.1
  let clmulh_val := clmulhR.2
  let clmulrR : List Gate × List Wire := mkClmul "clmulr" src1_val src2_val 63
  let clmulrGates := clmulrR.1
  let clmulr_val := clmulrR.2

  -- Extenders
  let zextwR : List Gate × List Wire := mkZext32 "zextw" src1_val
  let zextwGates := zextwR.1
  let zextw_val := zextwR.2
  let sextwR : List Gate × List Wire := mkSext32 "sextw" (src1_val.take 32)
  let sextwGates := sextwR.1
  let sextw_val := sextwR.2

  -- Byte wiring
  let orcb_val := makeWires "orcb_val" 64
  let orcbGates := (List.range 8).flatMap fun j =>
    let byteBits := (List.range 8).map fun k => src1_val[8 * j + k]!
    let r := mkOrTree s!"orcb_b{j}" byteBits
    r.1 ++ (List.range 8).map (fun k => Gate.mkBUF r.2 orcb_val[8 * j + k]!)
  let rev8_val := makeWires "rev8_val" 64
  let rev8Gates := (List.range 64).map fun i =>
    Gate.mkBUF src1_val[8 * (7 - i / 8) + i % 8]! rev8_val[i]!

  -- Count trees
  let clzBits := makeWires "clz_b" 64
  let ctzBits := makeWires "ctz_b" 64
  let clzGates := (List.range 64).flatMap fun i =>
    let acc := Wire.mk s!"clz_acc_{i}"
    let top := Wire.mk s!"clz_top_{i}"
    let prev := if i == 0 then zero else Wire.mk s!"clz_acc_{i - 1}"
    [Gate.mkOR prev src1_val[63 - i]! acc, Gate.mkNOT acc clzBits[i]!,
     Gate.mkOR (if i == 0 then zero else Wire.mk s!"ctz_acc_{i - 1}") src1_val[i]! (Wire.mk s!"ctz_acc_{i}"),
     Gate.mkNOT (Wire.mk s!"ctz_acc_{i}") ctzBits[i]!,
     Gate.mkBUF zero top]
  let clzCount : List Gate × List Wire := mkPopCount "clz" clzBits
  let clzCountGates := clzCount.1
  let clz_val := clzCount.2
  let ctzCount : List Gate × List Wire := mkPopCount "ctz" ctzBits
  let ctzCountGates := ctzCount.1
  let ctz_val := ctzCount.2
  let cpopCount : List Gate × List Wire := mkPopCount "cpop" src1_val
  let cpopCountGates := cpopCount.1
  let cpop_val := cpopCount.2
  let ctzwBits := makeWires "ctzw_b" 32
  let ctzwGates := (List.range 32).flatMap fun i =>
    let acc := Wire.mk s!"ctzw_acc_{i}"
    let prev := if i == 0 then zero else Wire.mk s!"ctzw_acc_{i - 1}"
    [Gate.mkOR prev src1_val[i]! acc, Gate.mkNOT acc ctzwBits[i]!]
  let ctzwCount : List Gate × List Wire := mkPopCount "ctzw" ctzwBits
  let ctzwCountGates := ctzwCount.1
  let ctzw_val := ctzwCount.2

  -- === MICRO-ALU RESULT MUX ===
  let aluOps : List (FallbackOp × List Wire) := [
    (.ALU_ANDN, andn_val), (.ALU_ORN, orn_val), (.ALU_XNOR, xnor_val),
    (.ALU_BSET, bset_val), (.ALU_BCLR, bclr_val), (.ALU_BINV, binv_val), (.ALU_BEXT, bext_val),
    (.ALU_SH1ADD, shadd_val), (.ALU_SH2ADD, shadd_val), (.ALU_SH3ADD, shadd_val),
    (.ALU_ADD, add_val), (.ALU_SUB, sub_val),
    (.ALU_MIN, min_val), (.ALU_MAX, max_val), (.ALU_MINU, minu_val), (.ALU_MAXU, maxu_val),
    (.ALU_ROL, rol_val), (.ALU_ROR, ror_val), (.ALU_ROLW, rolw_val), (.ALU_RORW, rorw_val),
    (.ALU_SLL, sll_val), (.ALU_SRL, srl_val), (.ALU_SRA, sra_val),
    (.ALU_CLMUL, clmul_val), (.ALU_CLMULH, clmulh_val), (.ALU_CLMULR, clmulr_val),
    (.ALU_ZEXT_W, zextw_val), (.ALU_SEXT_W, sextw_val),
    (.ALU_CLZ, clz_val), (.ALU_CTZ, ctz_val), (.ALU_CPOP, cpop_val), (.ALU_CTZW, ctzw_val),
    (.ALU_ORCB, orcb_val), (.ALU_REV8, rev8_val)
  ]
  let aluMux : List Gate × List Wire :=
    aluOps.foldl (fun (st : List Gate × List Wire) ⟨op, vals⟩ =>
      let next_w := makeWires s!"alu_mux_{st.1.length}" 64
      let g := (List.range 64).map fun i => Gate.mkMUX st.2[i]! vals[i]! (isOp op) next_w[i]!
      (st.1 ++ g, next_w)
    ) ([], List.replicate 64 zero)
  let aluMuxGates := aluMux.1
  let alu_val := aluMux.2

  -- === SCRATCHPAD WRITE PATH ===
  -- `LOAD_RS1/RS2/SHAMT/IMM` take their value from the capture registers or the
  -- instruction; every micro-ALU op takes the muxed result.
  let shamt64 := makeWires "shamt64" 64
  let imm64 := makeWires "imm64" 64
  let operandGates :=
    (List.range 64).map (fun i =>
      if i < 6 then Gate.mkBUF insn_q[20 + i]! shamt64[i]! else Gate.mkBUF zero shamt64[i]!) ++
    (List.range 64).map (fun i =>
      if i < 16 then Gate.mkBUF romImm[i]! imm64[i]! else Gate.mkBUF zero imm64[i]!)
  let write_val := makeWires "write_val" 64
  let writeMuxGates := (List.range 64).flatMap fun i =>
    let m1 := Wire.mk s!"wv1_{i}"
    let m2 := Wire.mk s!"wv2_{i}"
    let m3 := Wire.mk s!"wv3_{i}"
    [Gate.mkMUX alu_val[i]! rs1_q[i]! (isOp .LOAD_RS1) m1,
     Gate.mkMUX m1 rs2_q[i]! (isOp .LOAD_RS2) m2,
     Gate.mkMUX m2 shamt64[i]! (isOp .LOAD_SHAMT) m3,
     Gate.mkMUX m3 imm64[i]! (isOp .LOAD_IMM) write_val[i]!]
  let writeOps : List Wire :=
    ([FallbackOp.LOAD_RS1, .LOAD_RS2, .LOAD_SHAMT, .LOAD_IMM] ++ aluOpList).map isOp
  let writeOr : List Gate × Wire := mkOrTree "is_write" writeOps
  let writeOrGates := writeOr.1
  let isWrite := writeOr.2
  let dstEq := (List.range 4).map fun k => Wire.mk s!"dst_eq_{k}"
  let dstEqGates := (List.range 4).flatMap fun k =>
    let b0 := if k % 2 == 1 then romDst[0]! else Wire.mk s!"n_rom_dst0"
    let b1 := if k / 2 == 1 then romDst[1]! else Wire.mk s!"n_rom_dst1"
    [Gate.mkAND b0 b1 dstEq[k]!]
  let notDstGates := [Gate.mkNOT romDst[0]! (Wire.mk "n_rom_dst0"),
                      Gate.mkNOT romDst[1]! (Wire.mk "n_rom_dst1")]
  let tempGates := (List.range 4).flatMap fun k =>
    let wr := Wire.mk s!"temp_wr_{k}"
    let stepWr := Wire.mk s!"step_wr_{k}"
    [Gate.mkAND step_en isWrite stepWr,
     Gate.mkAND stepWr dstEq[k]! wr] ++
    (List.range 64).map (fun i => Gate.mkMUX tempsQ[k]![i]! write_val[i]! wr tempsD[k]![i]!) ++
    (List.range 64).map (fun i => Gate.mkDFF tempsD[k]![i]! clock reset tempsQ[k]![i]!)

  -- === OUTPUTS ===
  let cdb_inject := Wire.mk "cdb_inject"
  let redir_valid := Wire.mk "redir_valid"
  let trap_active := Wire.mk "trap_active"
  -- `MOV_TO_RD` names the temp to publish; the completion strobe fires one
  -- micro-op later at `.DONE`, whose operand fields mean nothing, so the
  -- payload is latched on the `MOV_TO_RD` step.
  let cdbData : List Gate × List Wire := mkMuxTreeVec "cdb_data_mux" tempsQ romSrc1
  let cdb_data_out := makeWires "cdb_data" 64
  let cdbDataGates := cdbData.1 ++
    [Gate.mkAND step_en (isOp .MOV_TO_RD) (Wire.mk "mov_to_rd_en")] ++
    (List.range 64).map (fun i =>
      Gate.mkMUX (Wire.mk s!"cdb_data_q_{i}") cdbData.2[i]! (Wire.mk "mov_to_rd_en") (Wire.mk s!"cdb_data_d_{i}")) ++
    (List.range 64).map (fun i =>
      Gate.mkDFF (Wire.mk s!"cdb_data_d_{i}") clock reset (Wire.mk s!"cdb_data_q_{i}")) ++
    (List.range 64).map (fun i => Gate.mkBUF (Wire.mk s!"cdb_data_q_{i}") cdb_data_out[i]!)
  let ctrlGates := [
    -- A completion strobe is qualified by the sequencer still being live.
    -- `done` is combinational from `active_q` and the control store, so a
    -- redirect that clears `active_q` cannot leave a stale strobe behind: the
    -- squashed sequence injects nothing and cannot override the redirect that
    -- flushed it.
    Gate.mkAND done matched cdb_inject,
    Gate.mkAND done matched redir_valid,
    Gate.mkNOT matched (Wire.mk "n_matched"),
    Gate.mkAND done (Wire.mk "n_matched") trap_active
  ]

  -- Redirection PC: PC + 4 on success
  let redir_pc_out := makeWires "redir_pc" 64
  let c4_vec := (List.range 64).map fun i => if i == 2 then one else zero
  let pc4 : List Gate × List Wire × Wire := mkAdderN "pc4" pc_q c4_vec zero
  let pc4ExactGates := pc4.1
  let pc_plus_4_exact := pc4.2.1
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

  let gA : List Gate :=
    insnInvGates ++ hitGates ++ prioGates ++ anyHitGates ++ encGates ++ selGates ++ matchedGates ++
    upcGates ++ romGates ++ romInvGates ++ opMatchGates
  let gB : List Gate :=
    holdGates ++ doneGates ++ drainGates ++ captureGates ++ src1MuxGates ++ src2MuxGates
  let gC : List Gate :=
    logicGates ++ shamtInvGates ++ maskGates ++ zbsOpGates ++ bextGates ++ shMuxGates ++ shaddAdderGates
  let gD : List Gate := addGates ++ subInvGates ++ subGates ++ cmpGates ++ minMaxGates
  let gE : List Gate := rorGates ++ rolw32.1 ++ rorw32.1 ++ rolwSext ++ rorwSext
  let gF : List Gate := sllGates ++ srlGates ++ sraGates
  let gG : List Gate := clmulGates ++ clmulhGates ++ clmulrGates
  let gH : List Gate := zextwGates ++ sextwGates ++ orcbGates ++ rev8Gates
  let gI : List Gate :=
    clzGates ++ clzCountGates ++ ctzCountGates ++ cpopCountGates ++ ctzwGates ++ ctzwCountGates
  let j1 : List Gate := aluMuxGates
  let j2 : List Gate := operandGates
  let j3 : List Gate := writeMuxGates
  let j4 : List Gate := writeOrGates
  let j5 : List Gate := notDstGates
  let j6 : List Gate := dstEqGates
  let j7 : List Gate := tempGates
  let gJ : List Gate := j1 ++ j2 ++ j3 ++ j4 ++ j5 ++ j6 ++ j7
  let gK : List Gate :=
    ctrlGates ++ cdbDataGates ++ pc4ExactGates ++ redirMuxGates ++ trapCauseGates ++ trapValGates
  let allGates := gA ++ gB ++ gC ++ gD ++ gE ++ gF ++ gG ++ gH ++ gI ++ gJ ++ gK

  { name := "FallbackSequencer"
    inputs := [clock, reset, start, pipeline_flush] ++
              insn_in ++ pc_in ++ rs1_in ++ rs2_in ++ rd_tag_in ++
              [rob_empty, sb_empty]
    outputs := [active_q, cdb_inject, redir_valid, trap_active] ++
               cdb_tag_q ++ cdb_data_out ++ redir_pc_out ++ trap_cause_out ++ trap_val_out
    gates := allGates
    instances := captureRegs
    signalGroups := [
      { name := "insn", width := 32, wires := insn_in },
      { name := "pc_in", width := 64, wires := pc_in },
      { name := "rs1_val", width := 64, wires := rs1_in },
      { name := "rs2_val", width := 64, wires := rs2_in },
      { name := "rd_tag_in", width := 6, wires := rd_tag_in },
      { name := "cdb_tag", width := 6, wires := cdb_tag_q },
      { name := "cdb_data", width := 64, wires := cdb_data_out },
      { name := "redir_pc", width := 64, wires := redir_pc_out },
      { name := "trap_cause", width := 64, wires := trap_cause_out },
      { name := "trap_val", width := 64, wires := trap_val_out }
    ] }

def fallbackSequencerCircuit : Circuit := mkFallbackSequencer

end Shoumei.RISCV.Microcode

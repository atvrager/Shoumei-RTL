/-
Circuits/Combinational/BranchTargetAdder.lean - 32-bit Branch Target Adder for RISC-V Fetch

Calculates branch/jump target (PC + immediate) for B-type and J-type (JAL) instructions.
Encapsulates immediate extraction, sign extension, and addition with cin=0 and imm[0]=0.
Eliminates LINT-32 (b[0]=0, cin=0) and LINT-33 (sign bit multi-pin) warnings by construction.
-/

import Shoumei.DSL

namespace Shoumei.Circuits.Combinational

open Shoumei

/-- Build a 32-bit Branch Target Adder.
    Inputs:
    - pc[31:0]: current PC (or PC+4)
    - instr[31:0]: instruction word
    - is_jal: 1 if JAL, 0 if B-type branch

    Outputs:
    - target[31:0]: computed target address (PC + offset)
-/
def mkBranchTargetAdder32 : Circuit :=
  let pc := (List.range 32).map fun i => Wire.mk s!"pc_{i}"
  let instr := (List.range 25).map fun i => Wire.mk s!"instr_{i}"
  let is_jal := Wire.mk "is_jal"
  let target := (List.range 32).map fun i => Wire.mk s!"target_{i}"

  -- Bit 0: pass through pc[0] via NOT-NOT buffer pair (imm[0] is always 0)
  let mid0 := Wire.mk "bta_mid_0"
  let bit0Gates := [
    Gate.mkNOT pc[0]! mid0,
    Gate.mkNOT mid0 target[0]!
  ]

  -- Extract B-type immediate bits [31:1]:
  -- Note: instr[24:0] corresponds to instruction bits [31:7].
  -- b_imm[4:1]   = instr_word[11:8]  = instr[4:1]
  -- b_imm[10:5]  = instr_word[30:25] = instr[23:18]
  -- b_imm[11]    = instr_word[7]     = instr[0]
  -- b_imm[31:12] = instr_word[31]    = instr[24]
  let b_imm := (List.range 32).map fun i => Wire.mk s!"b_imm_{i}"
  let b_ext_gates : List Gate :=
    ((List.range 4).map fun i => Gate.mkBUF instr[1 + i]! b_imm[1 + i]!) ++
    ((List.range 6).map fun i => Gate.mkBUF instr[18 + i]! b_imm[5 + i]!) ++
    [Gate.mkBUF instr[0]! b_imm[11]!] ++
    ((List.range 20).map fun i => Gate.mkBUF instr[24]! b_imm[12 + i]!)

  -- Extract J-type (JAL) immediate bits [31:1]:
  -- j_imm[10:1]  = instr_word[30:21] = instr[23:14]
  -- j_imm[11]    = instr_word[20]    = instr[13]
  -- j_imm[19:12] = instr_word[19:12] = instr[12:5]
  -- j_imm[31:20] = instr_word[31]    = instr[24]
  let j_imm := (List.range 32).map fun i => Wire.mk s!"j_imm_{i}"
  let j_ext_gates : List Gate :=
    ((List.range 10).map fun i => Gate.mkBUF instr[14 + i]! j_imm[1 + i]!) ++
    [Gate.mkBUF instr[13]! j_imm[11]!] ++
    ((List.range 8).map fun i => Gate.mkBUF instr[5 + i]! j_imm[12 + i]!) ++
    ((List.range 12).map fun i => Gate.mkBUF instr[24]! j_imm[20 + i]!)

  -- MUX immediate bits [31:1] based on is_jal
  let imm := (List.range 32).map fun i => Wire.mk s!"imm_{i}"
  let mux_imm_gates : List Gate :=
    (List.range 31).map fun i =>
      let idx := i + 1
      Gate.mkMUX b_imm[idx]! j_imm[idx]! is_jal imm[idx]!

  -- 31-bit Kogge-Stone Parallel Prefix Adder for bits [31:1]
  -- Level 0: generate g0 and propagate p0 for bits 1..31
  let g0 := (List.range 32).map fun i => Wire.mk s!"bta_g0_{i}"
  let p0 := (List.range 32).map fun i => Wire.mk s!"bta_p0_{i}"
  let init_gates : List Gate :=
    (List.range 31).flatMap fun i =>
      let idx := i + 1
      [ Gate.mkAND pc[idx]! imm[idx]! g0[idx]!,
        Gate.mkXOR pc[idx]! imm[idx]! p0[idx]! ]

  -- Prefix levels (strides 1, 2, 4, 8, 16) over 31 elements (1..31)
  let strides := [1, 2, 4, 8, 16]
  let (all_prefix_gates, final_g, _final_p) :=
    strides.foldl (fun (acc : List Gate × List Wire × List Wire) stride =>
      let (gates_acc, g_prev, p_prev) := acc
      let level_tag := s!"l{stride}"
      let g_new := (List.range 32).map fun i => Wire.mk s!"bta_g_{level_tag}_{i}"
      let p_new := (List.range 32).map fun i => Wire.mk s!"bta_p_{level_tag}_{i}"

      let level_gates : List Gate :=
        (List.range 31).flatMap fun i =>
          let idx := i + 1
          if idx <= stride then
            [ Gate.mkBUF g_prev[idx]! g_new[idx]!,
              Gate.mkBUF p_prev[idx]! p_new[idx]! ]
          else
            let pg := Wire.mk s!"bta_pg_{level_tag}_{idx}"
            [ Gate.mkAND p_prev[idx]! g_prev[idx - stride]! pg,
              Gate.mkOR g_prev[idx]! pg g_new[idx]!,
              Gate.mkAND p_prev[idx]! p_prev[idx - stride]! p_new[idx]! ]

      (gates_acc ++ level_gates, g_new, p_new)
    )
    ([], g0, p0)

  -- Final sum: target[1] = p0[1], target[i] = p0[i] XOR final_g[i-1] for i in 2..31
  let sum_gates : List Gate :=
    [ Gate.mkBUF p0[1]! target[1]! ] ++
    ((List.range 30).map fun i =>
      let idx := i + 2
      Gate.mkXOR p0[idx]! final_g[idx - 1]! target[idx]!)

  let allGates := bit0Gates ++ b_ext_gates ++ j_ext_gates ++ mux_imm_gates ++
                  init_gates ++ all_prefix_gates ++ sum_gates

  { name := "BranchTargetAdder32"
    inputs := pc ++ instr ++ [is_jal]
    outputs := target
    gates := allGates
    instances := []
    signalGroups := [
      { name := "pc", width := 32, wires := pc },
      { name := "instr", width := 25, wires := instr },
      { name := "target", width := 32, wires := target }
    ]
    keepHierarchy := true
  }

/-- BranchTargetAdder32 circuit export. -/
def branchTargetAdder32Circuit : Circuit := mkBranchTargetAdder32

end Shoumei.Circuits.Combinational

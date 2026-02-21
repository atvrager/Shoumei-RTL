import Shoumei.RISCV.Config
import Shoumei.DSL
import Shoumei.Circuits.Sequential.Register
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.RISCV

open Shoumei
open Shoumei.Circuits.Sequential
open Shoumei.Circuits.Combinational

/-- Helper: Create indexed wires -/
private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

-- Disable unused variables warning for work-in-progress circuit declaration
set_option linter.unusedVariables false

/--
Dual-Instruction Fetch Stage (N=2 Dual-Issue).

Given a 64-bit instruction chunk (two 32-bit instructions), this stage:
1. Manages PC increments by +8 normally.
2. Performs BTFN (Backward Taken, Forward Not-Taken) for slots 0 and 1 branches/JALs.
3. If slot 0 is taken, slot 1 is masked (valid=0) and next PC = target.
4. If slot 0 is not taken, slot 1 BTFN applies. If slot 1 is taken, next PC = target.

For simplicity at this stage, we assume 64-bit fetch and predict on both slots.

Inputs:
- clock, reset, stall
- branch_valid_0, branch_valid_1: backend redirects
- branch_target_0[31:0], branch_target_1[31:0]
- instr_0[31:0], instr_1[31:0] (from I-cache)

Outputs:
- pc_0[31:0], pc_1[31:0]
- valid_0, valid_1 
- predicted_taken_0, predicted_taken_1
-/
def mkFetchStage_W2 : Circuit :=
  -- Input wires
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let stall := Wire.mk "stall"
  
  -- branch_op represents any redirect.
  -- Wait actually the interface should be unified: branch_valid (from backend flush)
  let branch_valid := Wire.mk "branch_valid"
  let branch_target := makeIndexedWires "branch_target" 32
  
  let instr_0 := makeIndexedWires "instr_0" 32
  let instr_1 := makeIndexedWires "instr_1" 32
  let const_0 := Wire.mk "const_0"
  let const_1 := Wire.mk "const_1"

  -- Internal wires: PC register
  let pc_reg := makeIndexedWires "pc_reg" 32
  let next_pc := makeIndexedWires "next_pc" 32

  -- Internal wires: Constant 8 generation (+8 for sequential N=2 fetch)
  let const_8 := makeIndexedWires "const_8" 32
  let const_8_gates := (List.range 32).map (fun i =>
    if i == 3 then
      Gate.mkBUF const_1 (const_8[i]!)
    else
      Gate.mkBUF const_0 (const_8[i]!)
  )

  -- Internal wires: Constant 4 generation (+4 for slot 1 PC and predicting slot 0 forward-fetch)
  let const_4 := makeIndexedWires "const_4" 32
  let const_4_gates := (List.range 32).map (fun i =>
    if i == 2 then
      Gate.mkBUF const_1 (const_4[i]!)
    else
      Gate.mkBUF const_0 (const_4[i]!)
  )

  -- PC + 8
  let pc_plus_8 := makeIndexedWires "pc_plus_8" 32
  
  -- PC + 4
  let pc_plus_4 := makeIndexedWires "pc_plus_4" 32

  -- Helper to build BTFN prediction for a slot
  let buildPredictor (slot : String) (instr : List Wire) (pc : List Wire) : 
      List Gate × Wire × List Wire :=
    -- is_branch, is_jal, b_imm, j_imm are the same as in `mkFetchStage`
    let is_branch := Wire.mk s!"is_branch_{slot}"
    let is_jal    := Wire.mk s!"is_jal_fetch_{slot}"
    
    let not_bit2 := Wire.mk s!"not_bit2_{slot}"
    let not_bit3 := Wire.mk s!"not_bit3_{slot}"
    let not_bit4 := Wire.mk s!"not_bit4_{slot}"
    let btype_tmp1 := Wire.mk s!"btype_tmp1_{slot}"
    let btype_tmp2 := Wire.mk s!"btype_tmp2_{slot}"
    let btype_tmp3 := Wire.mk s!"btype_tmp3_{slot}"
    let btype_tmp4 := Wire.mk s!"btype_tmp4_{slot}"
    let btype_tmp5 := Wire.mk s!"btype_tmp5_{slot}"

    let btype_gates := [
      Gate.mkNOT instr[2]! not_bit2,
      Gate.mkNOT instr[3]! not_bit3,
      Gate.mkNOT instr[4]! not_bit4,
      Gate.mkAND instr[0]! instr[1]! btype_tmp1,
      Gate.mkAND not_bit2 not_bit3 btype_tmp2,
      Gate.mkAND not_bit4 instr[5]! btype_tmp3,
      Gate.mkAND btype_tmp1 btype_tmp2 btype_tmp4,
      Gate.mkAND btype_tmp3 instr[6]! btype_tmp5,
      Gate.mkAND btype_tmp4 btype_tmp5 is_branch
    ]

    let jal_tmp1 := Wire.mk s!"jal_tmp1_{slot}"
    let jal_tmp2 := Wire.mk s!"jal_tmp2_{slot}"
    let jal_tmp3 := Wire.mk s!"jal_tmp3_{slot}"
    let jal_tmp4 := Wire.mk s!"jal_tmp4_{slot}"
    let jal_tmp5 := Wire.mk s!"jal_tmp5_{slot}"

    let jal_gates := [
      Gate.mkAND instr[0]! instr[1]! jal_tmp1,
      Gate.mkAND instr[2]! instr[3]! jal_tmp2,
      Gate.mkAND not_bit4 instr[5]! jal_tmp3,
      Gate.mkAND jal_tmp1 jal_tmp2 jal_tmp4,
      Gate.mkAND jal_tmp3 instr[6]! jal_tmp5,
      Gate.mkAND jal_tmp4 jal_tmp5 is_jal
    ]

    let b_imm := makeIndexedWires s!"b_imm_{slot}" 32
    let b_imm_gates :=
      [Gate.mkBUF const_0 b_imm[0]!] ++
      (List.range 4).map (fun i => Gate.mkBUF instr[8+i]! b_imm[1+i]!) ++
      (List.range 6).map (fun i => Gate.mkBUF instr[25+i]! b_imm[5+i]!) ++
      [Gate.mkBUF instr[7]! b_imm[11]!, Gate.mkBUF instr[31]! b_imm[12]!] ++
      (List.range 19).map (fun i => Gate.mkBUF instr[31]! b_imm[13+i]!)

    let j_imm := makeIndexedWires s!"j_imm_{slot}" 32
    let j_imm_gates :=
      [Gate.mkBUF const_0 j_imm[0]!] ++
      (List.range 10).map (fun i => Gate.mkBUF instr[21+i]! j_imm[1+i]!) ++
      [Gate.mkBUF instr[20]! j_imm[11]!] ++
      (List.range 8).map (fun i => Gate.mkBUF instr[12+i]! j_imm[12+i]!) ++
      [Gate.mkBUF instr[31]! j_imm[20]!] ++
      (List.range 11).map (fun i => Gate.mkBUF instr[31]! j_imm[21+i]!)
      
    let predict_imm := makeIndexedWires s!"predict_imm_{slot}" 32
    let predict_imm_gates := (List.range 32).map (fun i =>
      Gate.mkMUX b_imm[i]! j_imm[i]! is_jal predict_imm[i]!)
      
    let branch_backward := Wire.mk s!"branch_backward_{slot}"
    let predicted_taken := Wire.mk s!"predicted_taken_{slot}"
    let btfn_gates := [
      Gate.mkAND is_branch instr[31]! branch_backward,
      Gate.mkOR branch_backward is_jal predicted_taken
    ]
    
    let gates := btype_gates ++ jal_gates ++ b_imm_gates ++ j_imm_gates ++ predict_imm_gates ++ btfn_gates
    (gates, predicted_taken, predict_imm)

  let (pred_gates_0, pt_0, pimm_0) := buildPredictor "0" instr_0 pc_reg
  let (pred_gates_1, pt_1, pimm_1) := buildPredictor "1" instr_1 pc_plus_4
  
  -- Target adders
  let predict_target_0 := makeIndexedWires "predict_target_0" 32
  let predict_target_0_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_predict_adder_0"
    portMap :=
      (pc_reg.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (pimm_0.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", const_0)] ++
      (predict_target_0.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }
  
  let predict_target_1 := makeIndexedWires "predict_target_1" 32
  let predict_target_1_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_predict_adder_1"
    portMap :=
      (pc_plus_4.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (pimm_1.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", const_0)] ++
      (predict_target_1.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }

  -- Next PC logic
  -- Priority:
  -- 1. branch_valid (backend redirect override) -> branch_target
  -- 2. stall -> pc_reg
  -- 3. pt_0 (slot 0 taken) -> predict_target_0
  -- 4. pt_1 (slot 1 taken) -> predict_target_1
  -- 5. default -> pc_plus_8
  
  let p1_mux_out := makeIndexedWires "p1_mux_out" 32
  let p1_gates := (List.range 32).map fun i => Gate.mkMUX pc_plus_8[i]! predict_target_1[i]! pt_1 p1_mux_out[i]!
  
  let p0_mux_out := makeIndexedWires "p0_mux_out" 32
  let p0_gates := (List.range 32).map fun i => Gate.mkMUX p1_mux_out[i]! predict_target_0[i]! pt_0 p0_mux_out[i]!
  
  let stall_mux_out := makeIndexedWires "stall_mux_out" 32
  let stall_gates := (List.range 32).map fun i => Gate.mkMUX p0_mux_out[i]! pc_reg[i]! stall stall_mux_out[i]!
  
  let final_mux_gates := (List.range 32).map fun i => Gate.mkMUX stall_mux_out[i]! branch_target[i]! branch_valid next_pc[i]!
  
  let combined_mux_gates := p1_gates ++ p0_gates ++ stall_gates ++ final_mux_gates
  
  -- Outputs
  let valid_0 := Wire.mk "valid_0"
  let valid_0_gate := Gate.mkBUF const_1 valid_0
  
  let not_pt_0 := Wire.mk "not_pt_0"
  let valid_1 := Wire.mk "valid_1"
  let valid_1_gates := [Gate.mkNOT pt_0 not_pt_0, Gate.mkBUF not_pt_0 valid_1]

  let pc_0_out := makeIndexedWires "pc_0" 32
  let pc_1_out := makeIndexedWires "pc_1" 32
  let pc_out_gates := (List.range 32).map fun i => Gate.mkBUF pc_reg[i]! pc_0_out[i]!
  let pc_1_out_gates := (List.range 32).map fun i => Gate.mkBUF pc_plus_4[i]! pc_1_out[i]!

  let pc_reg_inst : CircuitInstance := {
    moduleName := "Register32"
    instName := "u_pc_reg"
    portMap :=
      (next_pc.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
      [("clock", clock), ("reset", reset)] ++
      (pc_reg.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
  }

  let pc_adder_4_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_pc_adder_4"
    portMap :=
      (pc_reg.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (const_4.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", const_0)] ++
      (pc_plus_4.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }
  
  let pc_adder_8_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_pc_adder_8"
    portMap :=
      (pc_reg.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (const_8.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", const_0)] ++
      (pc_plus_8.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }

  -- Stalled status control output
  let stalled_reg := Wire.mk "stalled_reg"
  let stalled_cleared := Wire.mk "stalled_cleared"
  let stall_and_not_branch := Wire.mk "stall_and_not_branch"

  let stalled_cntrl_gates := [
    Gate.mkNOT branch_valid stalled_cleared,
    Gate.mkAND stall stalled_cleared stall_and_not_branch,
    Gate.mkDFF stall_and_not_branch clock reset stalled_reg
  ]

  { name := "FetchStage_W2"
    inputs := [clock, reset, stall, branch_valid, const_0, const_1] ++ 
              branch_target ++ instr_0 ++ instr_1
    outputs := pc_0_out ++ pc_1_out ++ [valid_0, valid_1, pt_0, pt_1, stalled_reg]
    gates := const_8_gates ++ const_4_gates ++ 
             pred_gates_0 ++ pred_gates_1 ++ combined_mux_gates ++
             [valid_0_gate] ++ valid_1_gates ++ pc_out_gates ++ pc_1_out_gates ++
             stalled_cntrl_gates
    instances := [pc_reg_inst, pc_adder_4_inst, pc_adder_8_inst, predict_target_0_inst, predict_target_1_inst] }

end Shoumei.RISCV

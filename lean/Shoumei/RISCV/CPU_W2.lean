import Shoumei.RISCV.Config
import Shoumei.RISCV.CPUBehavioral
import Shoumei.RISCV.CPUCircuitHelpers
import Shoumei.RISCV.CPUHelpers
import Shoumei.DSL
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Sequential.Register

import Shoumei.RISCV.Fetch_W2
import Shoumei.RISCV.Renaming.RenameStage_W2
import Shoumei.RISCV.CDBMux_W2
import Shoumei.RISCV.Execution.ReservationStation_W2
import Shoumei.RISCV.Execution.IntegerExecUnit_W2
import Shoumei.RISCV.Retirement.ROB_W2
import Shoumei.RISCV.CPU.BusyBitTable_W2

namespace Shoumei.RISCV.CPU_W2

open Shoumei.RISCV
open Shoumei
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential
open Shoumei.RISCV.CPU

/--
Dual-Issue Top-Level CPU Integration (W=2).
Extends mkCPU to 2 instructions per cycle throughout the pipeline.
-/
def mkCPU_W2 (config : CPUConfig) : Circuit :=
  let enableM := config.enableM
  let enableF := config.enableF
  let _oi := config.opcodeIndex
  let opcodeWidth := if enableF then 7 else 6
  
  -- Global signals
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- === EXTERNAL INTERFACES ===
  let imem_resp_data_0 := CPU.makeIndexedWires "imem_resp_data_0" 32
  let imem_resp_data_1 := CPU.makeIndexedWires "imem_resp_data_1" 32
  let dmem_resp_data := CPU.makeIndexedWires "dmem_resp_data" 32

  -- === FETCH STAGE (W2) ===
  let fetch_stall := Wire.mk "fetch_stall"
  let branch_redirect_valid := Wire.mk "branch_redirect_valid"
  let branch_redirect_target := CPU.makeIndexedWires "branch_redirect_target" 32
  
  let fetch_inst : CircuitInstance := {
    moduleName := "FetchStage_W2"
    instName := "u_fetch"
    portMap := [("clock", clock), ("reset", reset), ("stall", fetch_stall),
                ("branch_valid", branch_redirect_valid), ("const_0", zero), ("const_1", one)] ++
               bundledPorts "branch_target" branch_redirect_target ++
               bundledPorts "instr_0" imem_resp_data_0 ++
               bundledPorts "instr_1" imem_resp_data_1 ++
               bundledPorts "pc_0" (CPU.makeIndexedWires "fetch_pc_0" 32) ++
               bundledPorts "pc_1" (CPU.makeIndexedWires "fetch_pc_1" 32) ++
               [("valid_0", Wire.mk "fetch_valid_0"), ("valid_1", Wire.mk "fetch_valid_1"),
                ("pt_0", Wire.mk "fetch_pt_0"), ("pt_1", Wire.mk "fetch_pt_1"),
                ("stalled_reg", Wire.mk "fetch_stalled")]
  }

  -- === DECODE STAGE (W2) ===
  let decoderModuleName :=
    if enableF && enableM then "RV32IMFDecoder"
    else if enableF then "RV32IFDecoder"
    else if enableM then "RV32IMDecoder"
    else "RV32IDecoder"

  let mkDecoder (idx : Nat) (instr : List Wire) :=
    let pfx := s!"dec{idx}"
    let optype := CPU.makeIndexedWires s!"{pfx}_optype" opcodeWidth
    let rd := CPU.makeIndexedWires s!"{pfx}_rd" 5
    let rs1 := CPU.makeIndexedWires s!"{pfx}_rs1" 5
    let rs2 := CPU.makeIndexedWires s!"{pfx}_rs2" 5
    let imm := CPU.makeIndexedWires s!"{pfx}_imm" 32
    let valid := Wire.mk s!"{pfx}_valid"
    let inst : CircuitInstance := {
      moduleName := decoderModuleName, instName := s!"u_decoder_{idx}",
      portMap := bundledPorts "io_instr" instr ++ bundledPorts "io_optype" optype ++
                 bundledPorts "io_rd" rd ++ bundledPorts "io_rs1" rs1 ++ bundledPorts "io_rs2" rs2 ++ bundledPorts "io_imm" imm ++
                 [("io_valid", valid), ("io_has_rd", Wire.mk s!"{pfx}_has_rd"),
                  ("io_is_integer", Wire.mk s!"{pfx}_is_int"), ("io_is_memory", Wire.mk s!"{pfx}_is_mem"),
                  ("io_is_branch", Wire.mk s!"{pfx}_is_br"), ("io_is_store", Wire.mk s!"{pfx}_is_st"),
                  ("io_use_imm", Wire.mk s!"{pfx}_use_imm")]
    }
    (inst, optype, rd, rs1, rs2, imm, valid, Wire.mk s!"{pfx}_has_rd", Wire.mk s!"{pfx}_is_int", Wire.mk s!"{pfx}_is_br", Wire.mk s!"{pfx}_use_imm")

  let (dec0_inst, d0_op, d0_rd, d0_rs1, d0_rs2, _d0_imm, d0_valid, d0_has_rd, _d0_is_int, d0_is_br, d0_use_imm) := mkDecoder 0 imem_resp_data_0
  let (dec1_inst, d1_op, d1_rd, d1_rs1, d1_rs2, _d1_imm, d1_valid, d1_has_rd, _d1_is_int, d1_is_br, d1_use_imm) := mkDecoder 1 imem_resp_data_1

  -- === PIPELINE CONTROL ===
  -- (Simple for now: no redirection/flushes fully implemented here yet)
  let pipeline_flush := zero
  let commit_archRd_0 := CPU.makeIndexedWires "head_archRd_0" 5
  let commit_physRd_0 := CPU.makeIndexedWires "head_physRd_0" 6
  let commit_archRd_1 := CPU.makeIndexedWires "head_archRd_1" 5
  let commit_physRd_1 := CPU.makeIndexedWires "head_physRd_1" 6
  let retire_valid_0 := Wire.mk "commit_en_0"
  let retire_valid_1 := Wire.mk "commit_en_1"

  -- === RENAME STAGE (W2) ===
  let rs1_phys_0 := CPU.makeIndexedWires "rs1_phys_0" 6
  let rs2_phys_0 := CPU.makeIndexedWires "rs2_phys_0" 6
  let rd_phys_0  := CPU.makeIndexedWires "rd_phys_0" 6
  let rs1_data_0 := CPU.makeIndexedWires "rs1_data_0" 32
  let rs2_data_0 := CPU.makeIndexedWires "rs2_data_0" 32
  let old_physRd_0 := CPU.makeIndexedWires "old_physRd_0" 6
  
  let rs1_phys_1 := CPU.makeIndexedWires "rs1_phys_1" 6
  let rs2_phys_1 := CPU.makeIndexedWires "rs2_phys_1" 6
  let rd_phys_1  := CPU.makeIndexedWires "rd_phys_1" 6
  let rs1_data_1 := CPU.makeIndexedWires "rs1_data_1" 32
  let rs2_data_1 := CPU.makeIndexedWires "rs2_data_1" 32
  let old_physRd_1 := CPU.makeIndexedWires "old_physRd_1" 6

  let cdb_valid_0 := Wire.mk "cdb_valid_0"; let cdb_tag_0 := CPU.makeIndexedWires "cdb_tag_0" 6; let cdb_data_0 := CPU.makeIndexedWires "cdb_data_0" 32
  let cdb_valid_1 := Wire.mk "cdb_valid_1"; let cdb_tag_1 := CPU.makeIndexedWires "cdb_tag_1" 6; let cdb_data_1 := CPU.makeIndexedWires "cdb_data_1" 32

  let rename_inst : CircuitInstance := {
    moduleName := "RenameStage_W2"
    instName := "u_rename"
    portMap := [("clock", clock), ("reset", reset), ("zero", zero), ("one", one),
                ("instr_valid", d0_valid), ("has_rd", d0_has_rd), ("force_alloc", d0_is_br),
                ("instr_valid_1", d1_valid), ("has_rd_1", d1_has_rd), ("force_alloc_1", d1_is_br),
                ("flush_en", pipeline_flush), ("retire_valid", retire_valid_0), ("retire_valid_1", retire_valid_1)] ++
               bundledPorts "rs1_addr" d0_rs1 ++ bundledPorts "rs2_addr" d0_rs2 ++ bundledPorts "rd_addr" d0_rd ++
               bundledPorts "rs1_addr_1" d1_rs1 ++ bundledPorts "rs2_addr_1" d1_rs2 ++ bundledPorts "rd_addr_1" d1_rd ++
               bundledPorts "commit_archRd" commit_archRd_0 ++ bundledPorts "commit_physRd" commit_physRd_0 ++
               bundledPorts "commit_archRd_1" commit_archRd_1 ++ bundledPorts "commit_physRd_1" commit_physRd_1 ++
               [("cdb_valid_0", cdb_valid_0), ("cdb_valid_1", cdb_valid_1)] ++
               bundledPorts "cdb_tag_0" cdb_tag_0 ++ bundledPorts "cdb_data_0" cdb_data_0 ++
               bundledPorts "cdb_tag_1" cdb_tag_1 ++ bundledPorts "cdb_data_1" cdb_data_1 ++
               [("rename_valid", Wire.mk "rename_valid_0"), ("stall", Wire.mk "rename_stall_0"), 
                ("rename_valid_1", Wire.mk "rename_valid_1"), ("stall_1", Wire.mk "rename_stall_1")] ++
               bundledPorts "rs1_phys_out" rs1_phys_0 ++ bundledPorts "rs2_phys_out" rs2_phys_0 ++ bundledPorts "rd_phys_out" rd_phys_0 ++
               bundledPorts "old_rd_phys_out" old_physRd_0 ++
               bundledPorts "rs1_data" rs1_data_0 ++ bundledPorts "rs2_data" rs2_data_0 ++
               bundledPorts "rs1_phys_out_1" rs1_phys_1 ++ bundledPorts "rs2_phys_out_1" rs2_phys_1 ++ bundledPorts "rd_phys_out" rd_phys_1 ++
               bundledPorts "old_rd_phys_out_1" old_physRd_1 ++
               bundledPorts "rs1_data_1" rs1_data_1 ++ bundledPorts "rs2_data_1" rs2_data_1
  }

  -- === BUSY TABLE (W2) ===
  let src1_ready_0 := Wire.mk "src1_ready_0"; let src2_ready_0 := Wire.mk "src2_ready_0"
  let src1_ready_1 := Wire.mk "src1_ready_1"; let src2_ready_1 := Wire.mk "src2_ready_1"
  let (busy_gates, busy_insts) := mkBusyBitTable_W2 clock reset [] zero one
    rd_phys_0 rd_phys_1 (Wire.mk "rename_valid_0") (Wire.mk "rename_valid_1")
    cdb_tag_0 cdb_tag_1 cdb_valid_0 cdb_valid_1
    rs1_phys_0 rs2_phys_0 rs1_phys_1 rs2_phys_1
    d0_use_imm d1_use_imm
    src1_ready_0 src2_ready_0 (Wire.mk "src2_ready0_reg")
    src1_ready_1 src2_ready_1 (Wire.mk "src2_ready1_reg")

  -- === REORDER BUFFER (W2) ===
  let rob_inst : CircuitInstance := {
    moduleName := "ROB16_W2"
    instName := "u_rob"
    portMap := [("clock", clock), ("reset", reset), ("zero", zero), ("one", one),
                ("alloc_en_0", Wire.mk "rename_valid_0"), ("alloc_en_1", Wire.mk "rename_valid_1"),
                ("alloc_hasPhysRd_0", d0_has_rd), ("alloc_hasPhysRd_1", d1_has_rd),
                ("alloc_isBranch_0", d0_is_br), ("alloc_isBranch_1", d1_is_br),
                ("cdb_valid", cdb_valid_0), ("cdb_valid_1", cdb_valid_1),
                ("flush_en", pipeline_flush), ("commit_en_0", retire_valid_0), ("commit_en_1", retire_valid_1)] ++
               bundledPorts "alloc_physRd_0" rd_phys_0 ++ bundledPorts "alloc_oldPhysRd_0" old_physRd_0 ++ bundledPorts "alloc_archRd_0" d0_rd ++
               bundledPorts "alloc_physRd_1" rd_phys_1 ++ bundledPorts "alloc_oldPhysRd_1" old_physRd_1 ++ bundledPorts "alloc_archRd_1" d1_rd ++
               bundledPorts "cdb_tag" cdb_tag_0 ++ bundledPorts "cdb_tag_1" cdb_tag_1 ++
               bundledPorts "head_archRd_0" commit_archRd_0 ++ bundledPorts "head_physRd_0" commit_physRd_0 ++
               bundledPorts "head_archRd_1" commit_archRd_1 ++ bundledPorts "head_physRd_1" commit_physRd_1
  }

  -- === RESERVATION STATION (Integer, W2) ===
  let issue0_valid := Wire.mk "issue0_valid"; let issue1_valid := Wire.mk "issue1_valid"
  let dispatch_opcode_0 := CPU.makeIndexedWires "dispatch_opcode_0" 6
  let dispatch_src1_data_0 := CPU.makeIndexedWires "dispatch_src1_0" 32; let dispatch_src2_data_0 := CPU.makeIndexedWires "dispatch_src2_0" 32
  let dispatch_dest_tag_0 := CPU.makeIndexedWires "dispatch_dest_0" 6
  let dispatch_opcode_1 := CPU.makeIndexedWires "dispatch_opcode_1" 6
  let dispatch_src1_data_1 := CPU.makeIndexedWires "dispatch_src1_1" 32; let dispatch_src2_data_1 := CPU.makeIndexedWires "dispatch_src2_1" 32
  let dispatch_dest_tag_1 := CPU.makeIndexedWires "dispatch_dest_1" 6

  let rs_int_inst : CircuitInstance := {
    moduleName := "ReservationStation4_W2"
    instName := "u_rs_int"
    portMap := [("clock", clock), ("reset", reset), ("zero", zero), ("one", one), ("flush_en", pipeline_flush),
                ("issue_en_0", Wire.mk "rename_valid_0"), ("issue_en_1", Wire.mk "rename_valid_1"),
                ("issue_src1_ready_0", src1_ready_0), ("issue_src2_ready_0", src2_ready_0),
                ("issue_src1_ready_1", src1_ready_1), ("issue_src2_ready_1", src2_ready_1)] ++
               bundledPorts "issue_opcode_0" d0_op ++ bundledPorts "issue_dest_tag_0" rd_phys_0 ++
               bundledPorts "issue_src1_tag_0" rs1_phys_0 ++ bundledPorts "issue_src1_data_0" rs1_data_0 ++
               bundledPorts "issue_src2_tag_0" rs2_phys_0 ++ bundledPorts "issue_src2_data_0" rs2_data_0 ++
               bundledPorts "issue_opcode_1" d1_op ++ bundledPorts "issue_dest_tag_1" rd_phys_1 ++
               bundledPorts "issue_src1_tag_1" rs1_phys_1 ++ bundledPorts "issue_src1_data_1" rs1_data_1 ++
               bundledPorts "issue_src2_tag_1" rs2_phys_1 ++ bundledPorts "issue_src2_data_1" rs2_data_1 ++
               [("cdb_valid_0", cdb_valid_0), ("cdb_valid_1", cdb_valid_1)] ++
               bundledPorts "cdb_tag_0" cdb_tag_0 ++ bundledPorts "cdb_data_0" cdb_data_0 ++
               bundledPorts "cdb_tag_1" cdb_tag_1 ++ bundledPorts "cdb_data_1" cdb_data_1 ++
               [("dispatch_en_0", one), ("dispatch_en_1", one), ("dispatch_valid_0", issue0_valid), ("dispatch_valid_1", issue1_valid)] ++
               bundledPorts "dispatch_opcode_0" dispatch_opcode_0 ++ bundledPorts "dispatch_src1_data_0" dispatch_src1_data_0 ++
               bundledPorts "dispatch_src2_data_0" dispatch_src2_data_0 ++ bundledPorts "dispatch_dest_tag_0" dispatch_dest_tag_0 ++
               bundledPorts "dispatch_opcode_1" dispatch_opcode_1 ++ bundledPorts "dispatch_src1_data_1" dispatch_src1_data_1 ++
               bundledPorts "dispatch_src2_data_1" dispatch_src2_data_1 ++ bundledPorts "dispatch_dest_tag_1" dispatch_dest_tag_1
  }

  -- === EXECUTION UNITS (W2) ===
  let alu_op0 := CPU.makeIndexedWires "alu_op0" 4
  let alu_op1 := CPU.makeIndexedWires "alu_op1" 4
  let optype_mapping := OpType.resolveMapping config.decoderInstrNames aluMappingByName
  let alu_lut_gates0 := mkOpTypeToALU4 "lut0" dispatch_opcode_0 alu_op0 optype_mapping
  let alu_lut_gates1 := mkOpTypeToALU4 "lut1" dispatch_opcode_1 alu_op1 optype_mapping
  
  let result0 := CPU.makeIndexedWires "exec_result0" 32; let tag0 := CPU.makeIndexedWires "exec_tag0" 6
  let result1 := CPU.makeIndexedWires "exec_result1" 32; let tag1 := CPU.makeIndexedWires "exec_tag1" 6

  let exec_inst : CircuitInstance := {
    moduleName := "IntegerExecUnit_W2"
    instName := "u_exec"
    portMap := bundledPorts "a0" dispatch_src1_data_0 ++ bundledPorts "b0" dispatch_src2_data_0 ++
               bundledPorts "opcode0" alu_op0 ++ bundledPorts "dest_tag0" dispatch_dest_tag_0 ++
               bundledPorts "result0" result0 ++ bundledPorts "tag_out0" tag0 ++
               bundledPorts "a1" dispatch_src1_data_1 ++ bundledPorts "b1" dispatch_src2_data_1 ++
               bundledPorts "opcode1" alu_op1 ++ bundledPorts "dest_tag1" dispatch_dest_tag_1 ++
               bundledPorts "result1" result1 ++ bundledPorts "tag_out1" tag1
  }

  -- === CDB MUX (W2) ===
  let cdb_data_gates := ((List.range 32).map (fun i => [Gate.mkBUF result0[i]! cdb_data_0[i]!, Gate.mkBUF result1[i]! cdb_data_1[i]!])).flatten
  let cdb_tag_gates  := ((List.range 6).map (fun i => [Gate.mkBUF tag0[i]! cdb_tag_0[i]!, Gate.mkBUF tag1[i]! cdb_tag_1[i]!])).flatten
  let cdb_valid_gates := [Gate.mkBUF issue0_valid cdb_valid_0, Gate.mkBUF issue1_valid cdb_valid_1]
  let cdb_gates := cdb_data_gates ++ cdb_tag_gates ++ cdb_valid_gates

  -- === Assemble ===
  { name := "CPU_W2"
    inputs := [clock, reset, zero, one] ++ imem_resp_data_0 ++ imem_resp_data_1 ++ dmem_resp_data
    outputs := []
    gates := busy_gates ++ alu_lut_gates0 ++ alu_lut_gates1 ++ cdb_gates
    instances := [fetch_inst, dec0_inst, dec1_inst, rename_inst, rs_int_inst, exec_inst, rob_inst] ++ busy_insts
  }

end Shoumei.RISCV.CPU_W2

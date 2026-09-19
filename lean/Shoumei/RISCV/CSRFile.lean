/-
RISCV/CSRFile.lean - Standalone CSR Register File and Execution Unit

Extracted from CPU.lean into a modular, bus-oriented submodule.
Implements:
- 12 32-bit CSR registers (mscratch, mcycle, mcycleh, minstret, minstreth,
  mstatus, mie, mtvec, mepc, mcause, mtval, mip)
- Address decoding and effective address multiplexing (regular vs trap microcode)
- CSR read multiplexer with privilege and trap-forcing logic
- CSR write logic with WARL masking and arithmetic counter auto-increment
- Floating-point status/control (fflags accumulation and frm register)
- CDB injection and timer interrupt pending generation
-/

import Shoumei.DSL
import Shoumei.RISCV.Config
import Shoumei.RISCV.CPUCircuitHelpers
import Shoumei.RISCV.CPUHelpers
import Shoumei.Circuits.Sequential.Register

namespace Shoumei.RISCV

open Shoumei
open Shoumei.RISCV
open Shoumei.RISCV.CPU

def mkCSRFile (config : CPUConfig) : Circuit :=
  let enableTraps := config.microcodesTraps
  let enableF := config.enableF
  let opcodeWidth := config.opcodeWidth
  let oi := config.opcodeIndex
  let csrDataWidth := if config.xlen == 64 || config.enableD then 64 else 32

  -- Interface wires
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  let csr_addr := (List.range 12).map (fun i => Wire.mk s!"csr_addr_{i}")
  let csr_optype := (List.range opcodeWidth).map (fun i => Wire.mk s!"csr_optype_{i}")
  let xlen := config.xlen
  let csr_rs1cap := (List.range xlen).map (fun i => Wire.mk s!"csr_rs1cap_{i}")
  let csr_zimm := (List.range 5).map (fun i => Wire.mk s!"csr_zimm_{i}")
  let csr_phys := (List.range 6).map (fun i => Wire.mk s!"csr_phys_{i}")
  let csr_rd := (List.range 5).map (fun i => Wire.mk s!"csr_rd_{i}")
  let csr_drain_complete := Wire.mk "csr_drain_complete"

  let useq_active := Wire.mk "useq_active"
  let useq_csr_sel := (List.range 2).map (fun i => Wire.mk s!"useq_csr_sel_{i}")
  let useq_mstatus_trap := Wire.mk "useq_mstatus_trap"
  let useq_mstatus_mret := Wire.mk "useq_mstatus_mret"
  let useq_write_en := Wire.mk "useq_write_en"
  let useq_write_data := (List.range 32).map (fun i => Wire.mk s!"useq_write_data_{i}")

  let retire_valid_0 := Wire.mk "retire_valid_0"
  let retire_valid_1 := Wire.mk "retire_valid_1"
  let mtip_in := Wire.mk "mtip_in"
  let msip_in := Wire.mk "msip_in"
  let meip_in := Wire.mk "meip_in"

  let fp_valid_out := Wire.mk "fp_valid_out"
  let fp_exceptions := (List.range 5).map (fun i => Wire.mk s!"fp_exceptions_{i}")
  let csr_cdb_inject := Wire.mk "csr_cdb_inject"
  let csr_cdb_tag := (List.range 6).map (fun i => Wire.mk s!"csr_cdb_tag_{i}")
  let csr_cdb_data := (List.range csrDataWidth).map (fun i => Wire.mk s!"csr_cdb_data_{i}")
  let frm := (List.range 3).map (fun i => Wire.mk s!"frm_{i}")
  let fflags := (List.range 5).map (fun i => Wire.mk s!"fflags_{i}")
  let irq_pending := Wire.mk "irq_pending"

  -- Internal CSR registers
  let mscratch_reg := (List.range 32).map (fun i => Wire.mk s!"mscratch_e{i}")
  let mscratch_next := (List.range 32).map (fun i => Wire.mk s!"mscratch_nx_e{i}")
  let mcycle_reg := (List.range 32).map (fun i => Wire.mk s!"mcycle_e{i}")
  let mcycle_next := (List.range 32).map (fun i => Wire.mk s!"mcycle_nx_e{i}")
  let mcycleh_reg := (List.range 32).map (fun i => Wire.mk s!"mcycleh_e{i}")
  let mcycleh_next := (List.range 32).map (fun i => Wire.mk s!"mcycleh_nx_e{i}")
  let minstret_reg := (List.range 32).map (fun i => Wire.mk s!"minstret_e{i}")
  let minstret_next := (List.range 32).map (fun i => Wire.mk s!"minstret_nx_e{i}")
  let minstreth_reg := (List.range 32).map (fun i => Wire.mk s!"minstreth_e{i}")
  let minstreth_next := (List.range 32).map (fun i => Wire.mk s!"minstreth_nx_e{i}")
  let mstatus_reg := (List.range 32).map (fun i => Wire.mk s!"mstatus_e{i}")
  let mstatus_next := (List.range 32).map (fun i => Wire.mk s!"mstatus_nx_e{i}")
  let mie_reg := (List.range 32).map (fun i => Wire.mk s!"mie_e{i}")
  let mie_next := (List.range 32).map (fun i => Wire.mk s!"mie_nx_e{i}")
  let mtvec_reg := (List.range 32).map (fun i => Wire.mk s!"mtvec_e{i}")
  let mtvec_next := (List.range 32).map (fun i => Wire.mk s!"mtvec_nx_e{i}")
  let mepc_reg := (List.range 32).map (fun i => Wire.mk s!"mepc_e{i}")
  let mepc_next := (List.range 32).map (fun i => Wire.mk s!"mepc_nx_e{i}")
  let mcause_reg := (List.range 32).map (fun i => Wire.mk s!"mcause_e{i}")
  let mcause_next := (List.range 32).map (fun i => Wire.mk s!"mcause_nx_e{i}")
  let mtval_reg := (List.range 32).map (fun i => Wire.mk s!"mtval_e{i}")
  let mtval_next := (List.range 32).map (fun i => Wire.mk s!"mtval_nx_e{i}")
  let mip_reg := (List.range 32).map (fun i => Wire.mk s!"mip_e{i}")
  let mip_next := (List.range 32).map (fun i => Wire.mk s!"mip_nx_e{i}")

  let mkReg32Inst (name : String) (d : List Wire) (q : List Wire) : CircuitInstance := {
    moduleName := "Register32"
    instName := s!"u_{name}_reg"
    portMap := (d.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
               [("clock", clock), ("reset", reset)] ++
               (q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
  }

  let csr_reg_instances : List CircuitInstance :=
    if config.enableZicsr then
      [mkReg32Inst "mscratch" mscratch_next mscratch_reg,
       mkReg32Inst "mcycle" mcycle_next mcycle_reg,
       mkReg32Inst "mcycleh" mcycleh_next mcycleh_reg,
       mkReg32Inst "minstret" minstret_next minstret_reg,
       mkReg32Inst "minstreth" minstreth_next minstreth_reg,
       mkReg32Inst "mstatus" mstatus_next mstatus_reg,
       mkReg32Inst "mie" mie_next mie_reg,
       mkReg32Inst "mtvec" mtvec_next mtvec_reg,
       mkReg32Inst "mepc" mepc_next mepc_reg,
       mkReg32Inst "mcause" mcause_next mcause_reg,
       mkReg32Inst "mtval" mtval_next mtval_reg,
       { moduleName := "DFlipFlop", instName := "u_mip_reg_7",
         portMap := [("d", mip_next[7]!), ("q", mip_reg[7]!),
                     ("clock", clock), ("reset", reset)] }]
    else []

  let mip_gates : List Gate :=
    (List.range 32).filterMap (fun i =>
      if i == 7 then none
      else some (Gate.mkBUF zero mip_reg[i]!))

  -- Effective address multiplexing
  let eff_csr_addr := if enableTraps then
    (List.range 12).map (fun i => Wire.mk s!"eff_csr_addr_{i}")
  else
    csr_addr
  let eff_csr_addr_gates := if enableTraps then
    let not_useq_active := Wire.mk "not_useq_active"
    let n_useq_s0 := Wire.mk "n_useq_s0"
    let useq_a1 := Wire.mk "useq_a1"
    let useq_a2 := Wire.mk "useq_a2"
    let useq_a6 := Wire.mk "useq_a6"
    [
      Gate.mkNOT useq_active not_useq_active,
      Gate.mkNOT useq_csr_sel[0]! n_useq_s0,
      Gate.mkAND useq_csr_sel[1]! n_useq_s0 useq_a1,
      Gate.mkAND useq_csr_sel[1]! useq_csr_sel[0]! useq_a2,
      Gate.mkXOR useq_csr_sel[0]! useq_csr_sel[1]! useq_a6,
      -- bit 0: MUX(csr_addr[0], useq_csr_sel[0], useq_active)
      Gate.mkMUX csr_addr[0]! useq_csr_sel[0]! useq_active eff_csr_addr[0]!,
      -- bit 1: MUX(csr_addr[1], useq_a1, useq_active)
      Gate.mkMUX csr_addr[1]! useq_a1 useq_active eff_csr_addr[1]!,
      -- bit 2: MUX(csr_addr[2], useq_a2, useq_active)
      Gate.mkMUX csr_addr[2]! useq_a2 useq_active eff_csr_addr[2]!,
      -- bits 3, 4, 5: 0 on trap -> csr_addr[i] AND not_useq_active
      Gate.mkAND csr_addr[3]! not_useq_active eff_csr_addr[3]!,
      Gate.mkAND csr_addr[4]! not_useq_active eff_csr_addr[4]!,
      Gate.mkAND csr_addr[5]! not_useq_active eff_csr_addr[5]!,
      -- bit 6: MUX(csr_addr[6], useq_a6, useq_active)
      Gate.mkMUX csr_addr[6]! useq_a6 useq_active eff_csr_addr[6]!,
      -- bit 7: 0 on trap -> csr_addr[7] AND not_useq_active
      Gate.mkAND csr_addr[7]! not_useq_active eff_csr_addr[7]!,
      -- bits 8, 9: 1 on trap -> csr_addr[i] OR useq_active
      Gate.mkOR csr_addr[8]! useq_active eff_csr_addr[8]!,
      Gate.mkOR csr_addr[9]! useq_active eff_csr_addr[9]!,
      -- bits 10, 11: 0 on trap -> csr_addr[i] AND not_useq_active
      Gate.mkAND csr_addr[10]! not_useq_active eff_csr_addr[10]!,
      Gate.mkAND csr_addr[11]! not_useq_active eff_csr_addr[11]!
    ]
  else []

  -- CSR address decode
  let (csr_addr_decode_gates, is_mscratch, is_mcycle_m, is_mcycleh_m, is_minstret_m, is_minstreth_m,
       is_misa, is_fflags, is_frm, is_fcsr, is_mstatus, is_mie, is_mtvec, is_mepc, is_mcause,
       is_mtval, is_mip, is_mcycle, is_mcycleh, is_minstret, is_minstreth) :=
    mkCsrAddrDecode eff_csr_addr

  -- Floating-point control/status (fflags and frm)
  let fflags_reg := CPU.makeIndexedWires "fflags_reg" 5
  let fflags_new := CPU.makeIndexedWires "fflags_new" 5
  let fflags_acc := CPU.makeIndexedWires "fflags_acc" 5
  let fflags_masked := CPU.makeIndexedWires "fflags_masked" 5
  let fflags_acc_val := CPU.makeIndexedWires "fflags_acc_val" 5
  let frm_reg := CPU.makeIndexedWires "frm_reg" 3
  let frm_new := CPU.makeIndexedWires "frm_new" 3
  let fp_exceptions_ffl := if enableF then fp_exceptions else
    CPU.makeIndexedWires "fp_exceptions_stub" 5
  let fp_exceptions_stub_gates :=
    if enableF then [] else (List.range 5).map (fun i => Gate.mkBUF zero fp_exceptions_ffl[i]!)
  let (fflags_frm_gates, fflags_frm_dff_instances) := mkFPFlags
    enableF zero one clock reset
    (if enableF then fp_valid_out else zero) fp_exceptions_ffl
    fflags_reg fflags_new fflags_acc fflags_masked fflags_acc_val
    frm_reg frm_new

  -- CSR read MUX
  let is_mstatus_for_read := Wire.mk "is_mstatus_forced"
  let mstatus_force_gates : List Gate :=
    if enableTraps then
      [Gate.mkOR useq_mstatus_trap useq_mstatus_mret (Wire.mk "useq_any_mstatus"),
       Gate.mkOR is_mstatus (Wire.mk "useq_any_mstatus") is_mstatus_for_read]
    else
      [Gate.mkBUF is_mstatus is_mstatus_for_read]
  let misa_val : Nat := 0x40000100 +
    (if config.enableM then 0x00001000 else 0) +
    (if config.enableF then 0x00000020 else 0)
  let (csr_read_mux_all_gates, internal_read_data, _mstatus_sd_bit, _mstatus_fs_inv0, _mstatus_fs_inv1) :=
    mkCsrReadMux config enableF zero one misa_val
      is_misa is_mscratch is_mcycle is_mcycleh is_minstret is_minstreth
      is_fflags is_frm is_fcsr
      is_mstatus_for_read is_mie is_mtvec is_mepc is_mcause is_mtval is_mip
      mscratch_reg mcycle_reg mcycleh_reg minstret_reg minstreth_reg
      mstatus_reg mie_reg mtvec_reg mepc_reg mcause_reg mtval_reg
      fflags_reg frm_reg

  -- CSR op decode + write logic
  let (csr_op_decode_gates, csr_write_logic_gates, csr_write_val,
       csr_we_mscratch, csr_we_mcycle, csr_we_mcycleh, csr_we_minstret, csr_we_minstreth,
       csr_we_mstatus, csr_we_mie, csr_we_mtvec, csr_we_mepc, csr_we_mcause, csr_we_mtval,
       _cdbGates) :=
      let (opDecGates, csr_is_rw, csr_is_rs, csr_is_rc, _csr_is_imm, csr_src) :=
        mkCsrOpDecode config oi opcodeWidth zero csr_optype csr_rs1cap csr_zimm
      let (wrGates, wrVal,
           we_mscr, we_mcyc, we_mcych, we_minst, we_minsth,
           we_mstat, we_mie_w, we_mtvec, we_mepc, we_mcause, we_mtval,
           _act_writes, _drain_writes) :=
        mkCsrWriteLogic config zero internal_read_data csr_src csr_is_rw csr_is_rs csr_is_rc
          csr_drain_complete csr_zimm
          is_mscratch is_mcycle_m is_mcycleh_m is_minstret_m is_minstreth_m
          is_fflags is_frm is_fcsr
          is_mstatus is_mie is_mtvec is_mepc is_mcause is_mtval
      (opDecGates, wrGates, wrVal,
       we_mscr, we_mcyc, we_mcych, we_minst, we_minsth,
       we_mstat, we_mie_w, we_mtvec, we_mepc, we_mcause, we_mtval,
       ([] : List Gate))

  -- Absorb unused upper bits of csr_rs1cap when xlen > 32
  let (rs1cap_extra_gates, rs1cap_extra_zero) :=
    if xlen > 32 then
      let zeros := (List.range (xlen - 32)).map fun i =>
        let idx := 32 + i
        let not_w := Wire.mk s!"not_rs1cap_{idx}"
        let z_w := Wire.mk s!"z_rs1cap_{idx}"
        ([Gate.mkNOT (csr_rs1cap[idx]!) not_w,
          Gate.mkAND (csr_rs1cap[idx]!) not_w z_w], z_w)
      let gts := zeros.flatMap (·.1)
      let zwires := zeros.map (·.2)
      let (orGates, finalZero) := zwires.tail.foldl (fun (accGates, curWire) nextWire =>
        let orOut := Wire.mk (curWire.name ++ "_or")
        (accGates ++ [Gate.mkOR curWire nextWire orOut], orOut)
      ) ([], zwires.head!)
      (gts ++ orGates, finalZero)
    else
      ([], zero)

  -- CDB injection gates
  let csr_rd_nonzero := Wire.mk "csr_rd_nonzero"
  let csr_rd_nz_tmp := (List.range 4).map (fun i => Wire.mk s!"csr_rdnz_e{i}")
  let cdb_inject_gates :=
    if config.enableZicsr then
      rs1cap_extra_gates ++
      [Gate.mkOR csr_rd[0]! csr_rd[1]! csr_rd_nz_tmp[0]!,
       Gate.mkOR csr_rd_nz_tmp[0]! csr_rd[2]! csr_rd_nz_tmp[1]!,
       Gate.mkOR csr_rd_nz_tmp[1]! csr_rd[3]! csr_rd_nz_tmp[2]!,
       Gate.mkOR csr_rd_nz_tmp[2]! csr_rd[4]! csr_rd_nz_tmp[3]!,
       Gate.mkOR csr_rd_nz_tmp[3]! rs1cap_extra_zero csr_rd_nonzero,
       Gate.mkAND csr_drain_complete csr_rd_nonzero csr_cdb_inject] ++
      (List.range 6).flatMap (fun i =>
        let not_p := Wire.mk s!"not_csr_phys_{i}"
        let not_not_p := Wire.mk s!"not_not_csr_phys_{i}"
        [Gate.mkNOT (csr_phys[i]!) not_p,
         Gate.mkNOT not_p not_not_p,
         Gate.mkAND (csr_phys[i]!) not_not_p (csr_cdb_tag[i]!)]) ++
      (List.range csrDataWidth).map (fun i => Gate.mkBUF internal_read_data[i]! csr_cdb_data[i]!)
    else
      rs1cap_extra_gates ++
      [Gate.mkBUF zero csr_rd_nonzero,
       Gate.mkBUF zero csr_cdb_inject] ++
      (List.range 6).map (fun i => Gate.mkBUF zero csr_cdb_tag[i]!) ++
      (List.range csrDataWidth).map (fun i => Gate.mkBUF zero csr_cdb_data[i]!)

  -- Trap sequencer merge
  let (merged_csr_write_val, merged_csr_we_mstatus, merged_csr_we_mepc, merged_csr_we_mcause, trap_we_merge_gates) :=
    if enableTraps && config.enableZicsr then
      let merged_wr := CPU.makeIndexedWires "merged_csr_wr" 32
      let merged_we_mstat := Wire.mk "merged_we_mstatus"
      let useq_we_mepc := Wire.mk "useq_we_mepc"
      let useq_we_mcause := Wire.mk "useq_we_mcause"
      let merged_we_mepc := Wire.mk "merged_we_mepc"
      let merged_we_mcause := Wire.mk "merged_we_mcause"
      let useq_write_csr_only := Wire.mk "useq_wr_csr_only"
      let gates :=
        [Gate.mkOR useq_mstatus_trap useq_mstatus_mret (Wire.mk "useq_any_mstat_wr"),
         Gate.mkNOT (Wire.mk "useq_any_mstat_wr") (Wire.mk "useq_not_mstat"),
         Gate.mkAND useq_write_en (Wire.mk "useq_not_mstat") useq_write_csr_only,
         Gate.mkOR csr_we_mstatus (Wire.mk "useq_any_mstat_wr") merged_we_mstat,
         Gate.mkAND useq_write_csr_only is_mepc useq_we_mepc,
         Gate.mkAND useq_write_csr_only is_mcause useq_we_mcause,
         Gate.mkOR csr_we_mepc useq_we_mepc merged_we_mepc,
         Gate.mkOR csr_we_mcause useq_we_mcause merged_we_mcause] ++
        (List.range 32).map (fun i =>
          Gate.mkMUX csr_write_val[i]! useq_write_data[i]! useq_write_en merged_wr[i]!)
      (merged_wr, merged_we_mstat, merged_we_mepc, merged_we_mcause, gates)
    else
      (csr_write_val, csr_we_mstatus, csr_we_mepc, csr_we_mcause, [])

  -- Next value logic + counter auto-increment
  let (csr_next_value_gates, csr_counter_instances) := mkCsrNextValue config enableF zero one
    merged_csr_write_val
    csr_we_mscratch csr_we_mcycle csr_we_mcycleh csr_we_minstret csr_we_minstreth
    merged_csr_we_mstatus csr_we_mie csr_we_mtvec merged_csr_we_mepc merged_csr_we_mcause csr_we_mtval
    mscratch_reg mscratch_next mstatus_reg mstatus_next
    mie_reg mie_next mtvec_reg mtvec_next mepc_reg mepc_next
    mcause_reg mcause_next mtval_reg mtval_next mip_next
    mcycle_reg mcycle_next mcycleh_reg mcycleh_next
    minstret_reg minstret_next minstreth_reg minstreth_next
    retire_valid_0 retire_valid_1

  -- IRQ pending generation
  let irq_gates :=
    if enableTraps then
      let irq_mtip_pre := Wire.mk "irq_mtip_pre"
      let irq_msip_pre := Wire.mk "irq_msip_pre"
      let irq_meip_pre := Wire.mk "irq_meip_pre"
      let irq_or0 := Wire.mk "irq_or0"
      let irq_pre := Wire.mk "irq_pre"
      [Gate.mkAND mip_reg[7]! mie_reg[7]! irq_mtip_pre,
       Gate.mkAND mip_reg[3]! mie_reg[3]! irq_msip_pre,
       Gate.mkAND mip_reg[11]! mie_reg[11]! irq_meip_pre,
       Gate.mkOR irq_mtip_pre irq_msip_pre irq_or0,
       Gate.mkOR irq_or0 irq_meip_pre irq_pre,
       Gate.mkAND irq_pre mstatus_reg[3]! irq_pending]
    else
      [Gate.mkBUF zero irq_pending]

  -- FP output buffer gates
  let fp_out_gates :=
    (List.range 3).map (fun i => Gate.mkBUF frm_reg[i]! frm[i]!) ++
    (List.range 5).map (fun i => Gate.mkBUF fflags_reg[i]! fflags[i]!)

  let all_inputs : List Wire :=
    [clock, reset, zero, one] ++
    csr_addr ++ csr_optype ++ csr_rs1cap ++ csr_zimm ++ csr_phys ++ csr_rd ++
    [csr_drain_complete] ++
    (if enableTraps then
      [useq_active] ++ useq_csr_sel ++
      [useq_mstatus_trap, useq_mstatus_mret, useq_write_en] ++
      useq_write_data
    else []) ++
    [retire_valid_0, retire_valid_1, mtip_in, msip_in, meip_in] ++
    (if enableF then [fp_valid_out] ++ fp_exceptions else [])

  let all_outputs : List Wire :=
    [csr_cdb_inject, csr_rd_nonzero] ++ csr_cdb_tag ++ csr_cdb_data ++
    frm ++ fflags ++ [irq_pending]

  let all_gates :=
    eff_csr_addr_gates ++ fp_exceptions_stub_gates ++ fflags_frm_gates ++
    csr_addr_decode_gates ++ mstatus_force_gates ++ csr_read_mux_all_gates ++
    csr_op_decode_gates ++ csr_write_logic_gates ++ cdb_inject_gates ++
    trap_we_merge_gates ++ csr_next_value_gates ++ irq_gates ++ fp_out_gates ++
    mip_gates

  let all_instances :=
    csr_reg_instances ++ fflags_frm_dff_instances ++ csr_counter_instances

  let sg (n : String) (w : Nat) (ws : List Wire) : SignalGroup :=
    { name := n, width := w, wires := ws }

  let signalGroups : List SignalGroup := [
    sg "csr_addr" 12 csr_addr,
    sg "csr_optype" opcodeWidth csr_optype,
    sg "csr_rs1cap" xlen csr_rs1cap,
    sg "csr_zimm" 5 csr_zimm,
    sg "csr_phys" 6 csr_phys,
    sg "csr_rd" 5 csr_rd,
    sg "csr_cdb_tag" 6 csr_cdb_tag,
    sg "csr_cdb_data" csrDataWidth csr_cdb_data,
    sg "frm" 3 frm,
    sg "fflags" 5 fflags
  ] ++ (if enableTraps then [
    sg "useq_csr_sel" 2 useq_csr_sel,
    sg "useq_write_data" 32 useq_write_data
  ] else []) ++ (if enableF then [
    sg "fp_exceptions" 5 fp_exceptions
  ] else []) ++ [
    sg "mscratch_reg" 32 mscratch_reg,
    sg "mscratch_next" 32 mscratch_next,
    sg "mcycle_reg" 32 mcycle_reg,
    sg "mcycle_next" 32 mcycle_next,
    sg "mcycleh_reg" 32 mcycleh_reg,
    sg "mcycleh_next" 32 mcycleh_next,
    sg "minstret_reg" 32 minstret_reg,
    sg "minstret_next" 32 minstret_next,
    sg "minstreth_reg" 32 minstreth_reg,
    sg "minstreth_next" 32 minstreth_next,
    sg "mstatus_reg" 32 mstatus_reg,
    sg "mstatus_next" 32 mstatus_next,
    sg "mie_reg" 32 mie_reg,
    sg "mie_next" 32 mie_next,
    sg "mtvec_reg" 32 mtvec_reg,
    sg "mtvec_next" 32 mtvec_next,
    sg "mepc_reg" 32 mepc_reg,
    sg "mepc_next" 32 mepc_next,
    sg "mcause_reg" 32 mcause_reg,
    sg "mcause_next" 32 mcause_next,
    sg "mtval_reg" 32 mtval_reg,
    sg "mtval_next" 32 mtval_next,
    sg "mip_reg" 32 mip_reg,
    sg "mip_next" 32 mip_next
  ]

  { name := s!"CSRFile_{config.isaString}"
    inputs := all_inputs
    outputs := all_outputs
    gates := all_gates
    instances := all_instances
    signalGroups := signalGroups }

end Shoumei.RISCV

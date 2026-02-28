/-
Microcode Sequencer - Sequential circuit: FSM + µPC + temp regs + capture latches

Hierarchical circuit using RegisterN instances for state storage,
MicrocodeDecoder for opcode decode, and combinational gates for
next-state logic and ALU operations.

Output interface matches the hardwired serialize FSM so CPU.lean
can config-gate between the two.
-/

import Shoumei.DSL
import Shoumei.RISCV.Microcode.MicrocodeTypes
import Shoumei.RISCV.Microcode.MicrocodeDecoder

namespace Shoumei.RISCV.Microcode

open Shoumei

/-- Build the microcode sequencer circuit.

    Inputs:
    - clock, reset
    - start: trigger from decode (serialize_detected)
    - seq_id[2:0]: which sequence to start (from SequenceID encoding)
    - rs1_val[31:0]: captured rs1/zimm value
    - csr_addr[11:0]: captured CSR address
    - rd_tag[5:0]: physical destination register tag
    - has_rd: instruction writes rd
    - skip_write: suppress CSR write (rs1=x0 for CSRRS/C)
    - csr_flag_in: true=CSR op, false=FENCE.I
    - rob_empty: ROB drain complete
    - sb_empty: store buffer drain complete
    - csr_read_data[31:0]: CSR register file read result
    - rom_data[23:0]: ROM entry at current µPC
    - pipeline_flush: cancel on misprediction

    Outputs:
    - active: sequencer is running (suppresses fetch)
    - fence_i_suppress: stall fetch while active
    - csr_drain_complete: final action done, about to DONE
    - csr_cdb_inject: CDB writeback strobe
    - csr_cdb_tag[5:0]: CDB writeback tag
    - csr_cdb_data[31:0]: CDB writeback data
    - csr_write_en: CSR write strobe
    - csr_write_data[31:0]: CSR write value
    - csr_read_en: CSR read strobe
    - csr_addr_out[11:0]: CSR address for read/write
    - fence_i_redir_valid: fetch redirect strobe
    - fence_i_redir_next[31:0]: redirect target
    - csr_flag_reg: CSR vs FENCE.I flag
    - csr_rename_en: rename allocation at sequence start
    - upc[5:0]: current micro program counter (for ROM address)
    - mstatus_trap_active: asserted during MSTATUS_TRAP µop (CPU handles CSR transform)
    - trap_taken: asserted when TRAP_ENTRY sequence completes (drives rvvi_trap)
-/
def mkMicrocodeSequencer : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"

  -- Input wires
  let start := Wire.mk "start"
  let seq_id := (List.range 3).map (fun i => Wire.mk s!"seq_id_{i}")
  let rs1_val := (List.range 32).map (fun i => Wire.mk s!"rs1_val_{i}")
  let csr_addr_in := (List.range 12).map (fun i => Wire.mk s!"csr_addr_in_{i}")
  let rd_tag_in := (List.range 6).map (fun i => Wire.mk s!"rd_tag_in_{i}")
  let has_rd_in := Wire.mk "has_rd_in"
  let skip_write_in := Wire.mk "skip_write_in"
  let csr_flag_in := Wire.mk "csr_flag_in"
  let rob_empty := Wire.mk "rob_empty"
  let sb_empty := Wire.mk "sb_empty"
  let csr_read_data := (List.range 32).map (fun i => Wire.mk s!"csr_read_data_{i}")
  let pipeline_flush := Wire.mk "pipeline_flush"
  let pc_in := (List.range 32).map (fun i => Wire.mk s!"pc_in_{i}")

  -- State registers (active, upc, temps, capture latches)
  let active_q := Wire.mk "active_q"
  let active_d := Wire.mk "active_d"
  let upc_q := (List.range 6).map (fun i => Wire.mk s!"upc_q_{i}")
  let upc_d := (List.range 6).map (fun i => Wire.mk s!"upc_d_{i}")
  let temp0_q := (List.range 32).map (fun i => Wire.mk s!"temp0_q_{i}")
  let temp0_d := (List.range 32).map (fun i => Wire.mk s!"temp0_d_{i}")
  let temp1_q := (List.range 32).map (fun i => Wire.mk s!"temp1_q_{i}")
  let temp1_d := (List.range 32).map (fun i => Wire.mk s!"temp1_d_{i}")
  let rs1cap_q := (List.range 32).map (fun i => Wire.mk s!"rs1cap_q_{i}")
  let rs1cap_d := (List.range 32).map (fun i => Wire.mk s!"rs1cap_d_{i}")
  let csraddr_q := (List.range 12).map (fun i => Wire.mk s!"csraddr_q_{i}")
  let csraddr_d := (List.range 12).map (fun i => Wire.mk s!"csraddr_d_{i}")
  let rdtag_q := (List.range 6).map (fun i => Wire.mk s!"rdtag_q_{i}")
  let rdtag_d := (List.range 6).map (fun i => Wire.mk s!"rdtag_d_{i}")
  let hasrd_q := Wire.mk "hasrd_q"
  let hasrd_d := Wire.mk "hasrd_d"
  let skipwr_q := Wire.mk "skipwr_q"
  let skipwr_d := Wire.mk "skipwr_d"
  let csrflag_q := Wire.mk "csrflag_q"
  let csrflag_d := Wire.mk "csrflag_d"
  let pccap_q := (List.range 32).map (fun i => Wire.mk s!"pccap_q_{i}")
  let pccap_d := (List.range 32).map (fun i => Wire.mk s!"pccap_d_{i}")

  -- ROM data: 24 bits from ROM lookup (provided externally or via instance)
  let rom_data := (List.range 24).map (fun i => Wire.mk s!"rom_data_{i}")
  let rom_opcode := (List.range 4).map (fun i => rom_data[20 + i]!)
  let rom_dst_0 := rom_data[18]!

  -- Decoder outputs (one-hot)
  let is_drain := Wire.mk "is_drain"
  let is_drain_sb := Wire.mk "is_drain_sb"
  let is_read_csr := Wire.mk "is_read_csr"
  let is_write_csr := Wire.mk "is_write_csr"
  let is_mov_to_rd := Wire.mk "is_mov_to_rd"
  let is_alu_mov := Wire.mk "is_alu_mov"
  let is_alu_or := Wire.mk "is_alu_or"
  let is_alu_andn := Wire.mk "is_alu_andn"
  let is_flush_fetch := Wire.mk "is_flush_fetch"
  let is_set_pc := Wire.mk "is_set_pc"
  let is_done := Wire.mk "is_done"
  let is_load_pc := Wire.mk "is_load_pc"
  let is_load_const := Wire.mk "is_load_const"
  let is_mstatus_trap := Wire.mk "is_mstatus_trap"
  let is_set_csr_addr := Wire.mk "is_set_csr_addr"

  -- Decoder instance
  let decoderInst : CircuitInstance :=
    { moduleName := "MicrocodeDecoder"
      instName := "u_decoder"
      portMap := (List.range 4).map (fun i => (s!"opcode_{i}", rom_opcode[i]!)) ++
        [("is_drain", is_drain), ("is_drain_sb", is_drain_sb),
         ("is_read_csr", is_read_csr), ("is_write_csr", is_write_csr),
         ("is_mov_to_rd", is_mov_to_rd), ("is_alu_mov", is_alu_mov),
         ("is_alu_or", is_alu_or), ("is_alu_andn", is_alu_andn),
         ("is_flush_fetch", is_flush_fetch), ("is_set_pc", is_set_pc),
         ("is_done", is_done),
         ("is_load_pc", is_load_pc), ("is_load_const", is_load_const),
         ("is_mstatus_trap", is_mstatus_trap), ("is_set_csr_addr", is_set_csr_addr)] }

  -- Register instances for state
  let upcReg : CircuitInstance :=
    { moduleName := "Register6"
      instName := "u_upc"
      portMap := (List.range 6).map (fun i => (s!"d_{i}", upc_d[i]!)) ++
                 (List.range 6).map (fun i => (s!"q_{i}", upc_q[i]!)) ++
                 [("clock", clock), ("reset", reset)] }

  let temp0Reg : CircuitInstance :=
    { moduleName := "Register32"
      instName := "u_temp0"
      portMap := (List.range 32).map (fun i => (s!"d_{i}", temp0_d[i]!)) ++
                 (List.range 32).map (fun i => (s!"q_{i}", temp0_q[i]!)) ++
                 [("clock", clock), ("reset", reset)] }

  let temp1Reg : CircuitInstance :=
    { moduleName := "Register32"
      instName := "u_temp1"
      portMap := (List.range 32).map (fun i => (s!"d_{i}", temp1_d[i]!)) ++
                 (List.range 32).map (fun i => (s!"q_{i}", temp1_q[i]!)) ++
                 [("clock", clock), ("reset", reset)] }

  let rs1capReg : CircuitInstance :=
    { moduleName := "Register32"
      instName := "u_rs1cap"
      portMap := (List.range 32).map (fun i => (s!"d_{i}", rs1cap_d[i]!)) ++
                 (List.range 32).map (fun i => (s!"q_{i}", rs1cap_q[i]!)) ++
                 [("clock", clock), ("reset", reset)] }

  let csraddrReg : CircuitInstance :=
    { moduleName := "Register16"
      instName := "u_csraddr"
      portMap := (List.range 12).map (fun i => (s!"d_{i}", csraddr_d[i]!)) ++
                 -- Tie upper 4 bits to ground (only 12 used)
                 (List.range 4).map (fun i => (s!"d_{12 + i}", Wire.mk "tied_low")) ++
                 (List.range 12).map (fun i => (s!"q_{i}", csraddr_q[i]!)) ++
                 (List.range 4).map (fun i => (s!"q_{12 + i}", Wire.mk s!"csraddr_unused_{i}")) ++
                 [("clock", clock), ("reset", reset)] }

  let rdtagReg : CircuitInstance :=
    { moduleName := "Register6"
      instName := "u_rdtag"
      portMap := (List.range 6).map (fun i => (s!"d_{i}", rdtag_d[i]!)) ++
                 (List.range 6).map (fun i => (s!"q_{i}", rdtag_q[i]!)) ++
                 [("clock", clock), ("reset", reset)] }

  let pccapReg : CircuitInstance :=
    { moduleName := "Register32"
      instName := "u_pccap"
      portMap := (List.range 32).map (fun i => (s!"d_{i}", pccap_d[i]!)) ++
                 (List.range 32).map (fun i => (s!"q_{i}", pccap_q[i]!)) ++
                 [("clock", clock), ("reset", reset)] }

  -- DFF instances for single-bit state
  let activeDFF := Gate.mkDFF active_d clock reset active_q
  let hasrdDFF := Gate.mkDFF hasrd_d clock reset hasrd_q
  let skipwrDFF := Gate.mkDFF skipwr_d clock reset skipwr_q
  let csrflagDFF := Gate.mkDFF csrflag_d clock reset csrflag_q

  -- Stall conditions
  let drain_stall := Wire.mk "drain_stall"
  let n_rob_empty := Wire.mk "n_rob_empty"
  let drain_sb_stall := Wire.mk "drain_sb_stall"
  let n_sb_empty := Wire.mk "n_sb_empty"
  let stalling := Wire.mk "stalling"
  let not_stalling := Wire.mk "not_stalling"

  let stallGates := [
    Gate.mkNOT rob_empty n_rob_empty,
    Gate.mkAND is_drain n_rob_empty drain_stall,
    Gate.mkNOT sb_empty n_sb_empty,
    Gate.mkAND is_drain_sb n_sb_empty drain_sb_stall,
    Gate.mkOR drain_stall drain_sb_stall stalling,
    Gate.mkNOT stalling not_stalling
  ]

  -- µPC advance: upc_next = start ? seq_base : (stalling ? upc : upc + 1)
  -- seq_base = seq_id[2:0] << 3 (i.e., seq_id in bits [5:3], zeros in [2:0])
  let upc_plus1 := (List.range 6).map (fun i => Wire.mk s!"upc_p1_{i}")
  let upc_carry := (List.range 7).map (fun i => Wire.mk s!"upc_c_{i}")

  -- 6-bit incrementer
  let incGates :=
    [Gate.mkBUF active_q upc_carry[0]!] ++  -- carry-in = active (only advance when active)
    (List.range 6).map (fun i =>
      Gate.mkXOR upc_q[i]! upc_carry[i]! upc_plus1[i]!) ++
    (List.range 6).map (fun i =>
      Gate.mkAND upc_q[i]! upc_carry[i]! upc_carry[i+1]!)

  -- MUX: stalling ? upc_q : upc_plus1
  let upc_nostall := (List.range 6).map (fun i => Wire.mk s!"upc_ns_{i}")
  let upc_mux_stall := (List.range 6).map (fun i =>
    Gate.mkMUX upc_plus1[i]! upc_q[i]! stalling upc_nostall[i]!)

  -- MUX: start ? seq_base : upc_nostall
  -- seq_base: bits [5:3] = seq_id[2:0], bits [2:0] = 0
  let seq_base := (List.range 6).map (fun i =>
    if i < 3 then Wire.mk "tied_low" else seq_id[i - 3]!)

  let upc_next_mux := (List.range 6).map (fun i =>
    Gate.mkMUX upc_nostall[i]! seq_base[i]! start upc_d[i]!)

  -- DONE or pipeline_flush clears active
  let done_or_flush := Wire.mk "done_or_flush"
  let not_done_flush := Wire.mk "not_done_flush"
  let active_hold := Wire.mk "active_hold"
  let active_next := Wire.mk "active_next"

  let activeGates := [
    Gate.mkOR is_done pipeline_flush done_or_flush,
    Gate.mkNOT done_or_flush not_done_flush,
    Gate.mkAND active_q not_done_flush active_hold,
    Gate.mkOR start active_hold active_next,
    Gate.mkBUF active_next active_d
  ]

  -- Capture latches: on start, latch rs1_val, csr_addr, rd_tag, has_rd, skip_write, csr_flag
  let rs1cap_mux := (List.range 32).map (fun i =>
    Gate.mkMUX rs1cap_q[i]! rs1_val[i]! start rs1cap_d[i]!)
  -- CSR addr: on start, latch from csr_addr_in; on SET_CSR_ADDR, latch from rom_data[11:0]
  let csraddr_after_start := (List.range 12).map (fun i => Wire.mk s!"csra_as_{i}")
  let csraddr_start_mux := (List.range 12).map (fun i =>
    Gate.mkMUX csraddr_q[i]! csr_addr_in[i]! start csraddr_after_start[i]!)
  let csraddr_mux := (List.range 12).map (fun i =>
    Gate.mkMUX csraddr_after_start[i]! rom_data[i]! is_set_csr_addr csraddr_d[i]!)
  let rdtag_mux := (List.range 6).map (fun i =>
    Gate.mkMUX rdtag_q[i]! rd_tag_in[i]! start rdtag_d[i]!)
  let pccap_mux := (List.range 32).map (fun i =>
    Gate.mkMUX pccap_q[i]! pc_in[i]! start pccap_d[i]!)

  let captureBitGates := [
    Gate.mkMUX hasrd_q has_rd_in start hasrd_d,
    Gate.mkMUX skipwr_q skip_write_in start skipwr_d,
    Gate.mkMUX csrflag_q csr_flag_in start csrflag_d
  ]

  -- ALU: compute temp register next values
  -- temp0_d: MUX(hold, csr_read_data, alu_result) based on decoded op
  -- For READ_CSR with dst=0: temp0 := csr_read_data
  -- For ALU_MOV with dst=0: temp0 := rs1cap_q
  -- For ALU_OR with dst=0: temp0 := temp0_q | rs1cap_q (but dst is always 1 for OR/ANDN in ROM)
  -- Default: hold temp0_q

  -- OR: temp_src | rs1cap
  let alu_or_result := (List.range 32).map (fun i => Wire.mk s!"alu_or_{i}")
  let alu_or_gates := (List.range 32).map (fun i =>
    Gate.mkOR temp0_q[i]! rs1cap_q[i]! alu_or_result[i]!)

  -- ANDN: temp_src & ~rs1cap
  let n_rs1cap := (List.range 32).map (fun i => Wire.mk s!"n_rs1cap_{i}")
  let alu_andn_result := (List.range 32).map (fun i => Wire.mk s!"alu_andn_{i}")
  let alu_andn_gates :=
    (List.range 32).map (fun i => Gate.mkNOT rs1cap_q[i]! n_rs1cap[i]!) ++
    (List.range 32).map (fun i => Gate.mkAND temp0_q[i]! n_rs1cap[i]! alu_andn_result[i]!)

  -- temp0_d: on READ_CSR(dst=0) -> csr_read_data, on ALU_MOV(dst=0) -> rs1cap, else hold
  -- In ROM, READ_CSR always has dst=0, ALU_MOV always has dst=1, so temp0 gets csr_read_data
  let t0_sel_read := Wire.mk "t0_sel_read"
  let n_rom_dst_0 := Wire.mk "n_rom_dst_0"
  let t0_read_mux := (List.range 32).map (fun i => Wire.mk s!"t0_rmux_{i}")

  -- LOAD_PC with dst=0: temp0 := pccap_q
  let t0_sel_loadpc := Wire.mk "t0_sel_loadpc"
  let t0_after_loadpc := (List.range 32).map (fun i => Wire.mk s!"t0_alpc_{i}")
  -- LOAD_CONST with dst=0: temp0 := zext(rom_data[15:0])
  let t0_sel_loadconst := Wire.mk "t0_sel_loadconst"
  let t0_after_loadconst := (List.range 32).map (fun i => Wire.mk s!"t0_alc_{i}")

  let temp0Gates :=
    [Gate.mkNOT rom_dst_0 n_rom_dst_0,
     Gate.mkAND is_read_csr n_rom_dst_0 t0_sel_read,
     Gate.mkAND is_load_pc n_rom_dst_0 t0_sel_loadpc,
     Gate.mkAND is_load_const n_rom_dst_0 t0_sel_loadconst] ++
    (List.range 32).map (fun i =>
      Gate.mkMUX temp0_q[i]! csr_read_data[i]! t0_sel_read t0_read_mux[i]!) ++
    -- LOAD_PC: mux pccap into temp0
    (List.range 32).map (fun i =>
      Gate.mkMUX t0_read_mux[i]! pccap_q[i]! t0_sel_loadpc t0_after_loadpc[i]!) ++
    -- LOAD_CONST: mux rom_data[15:0] zero-extended into temp0
    (List.range 16).map (fun i =>
      Gate.mkMUX t0_after_loadpc[i]! rom_data[i]! t0_sel_loadconst t0_after_loadconst[i]!) ++
    (List.range 16).map (fun i =>
      Gate.mkMUX t0_after_loadpc[i + 16]! (Wire.mk "tied_low") t0_sel_loadconst t0_after_loadconst[i + 16]!) ++
    -- On start, clear temp0; otherwise hold or update
    (List.range 32).map (fun i =>
      Gate.mkMUX t0_after_loadconst[i]! (Wire.mk "tied_low") start temp0_d[i]!)

  -- temp1_d: on READ_CSR(dst=1) -> csr_read_data, on ALU_MOV(dst=1) -> rs1cap,
  -- on ALU_OR(dst=1) -> or_result, on ALU_ANDN(dst=1) -> andn_result
  let t1_sel_read := Wire.mk "t1_sel_read"
  let t1_sel_mov := Wire.mk "t1_sel_mov"
  let t1_sel_or := Wire.mk "t1_sel_or"
  let t1_sel_andn := Wire.mk "t1_sel_andn"
  let t1_after_read := (List.range 32).map (fun i => Wire.mk s!"t1_aread_{i}")
  let t1_after_mov := (List.range 32).map (fun i => Wire.mk s!"t1_amov_{i}")
  let t1_after_or := (List.range 32).map (fun i => Wire.mk s!"t1_aor_{i}")
  let t1_after_andn := (List.range 32).map (fun i => Wire.mk s!"t1_aandn_{i}")

  let temp1Gates :=
    [Gate.mkAND is_read_csr rom_dst_0 t1_sel_read,
     Gate.mkAND is_alu_mov rom_dst_0 t1_sel_mov,
     Gate.mkAND is_alu_or rom_dst_0 t1_sel_or,
     Gate.mkAND is_alu_andn rom_dst_0 t1_sel_andn] ++
    (List.range 32).map (fun i =>
      Gate.mkMUX temp1_q[i]! csr_read_data[i]! t1_sel_read t1_after_read[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX t1_after_read[i]! rs1cap_q[i]! t1_sel_mov t1_after_mov[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX t1_after_mov[i]! alu_or_result[i]! t1_sel_or t1_after_or[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX t1_after_or[i]! alu_andn_result[i]! t1_sel_andn t1_after_andn[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX t1_after_andn[i]! (Wire.mk "tied_low") start temp1_d[i]!)

  -- Output signals
  let fence_i_suppress := Wire.mk "fence_i_suppress"
  let csr_drain_complete := Wire.mk "csr_drain_complete"
  let csr_cdb_inject := Wire.mk "csr_cdb_inject"
  let csr_cdb_tag := (List.range 6).map (fun i => Wire.mk s!"csr_cdb_tag_{i}")
  let csr_cdb_data := (List.range 32).map (fun i => Wire.mk s!"csr_cdb_data_{i}")
  let csr_write_en := Wire.mk "csr_write_en"
  let csr_write_data := (List.range 32).map (fun i => Wire.mk s!"csr_write_data_{i}")
  let csr_read_en := Wire.mk "csr_read_en"
  let csr_addr_out := (List.range 12).map (fun i => Wire.mk s!"csr_addr_out_{i}")
  let fence_i_redir_valid := Wire.mk "fence_i_redir_valid"
  let fence_i_redir_next := (List.range 32).map (fun i => Wire.mk s!"fence_i_redir_next_{i}")
  let csr_rename_en_out := Wire.mk "csr_rename_en"
  let mstatus_trap_active := Wire.mk "mstatus_trap_active"
  let trap_taken := Wire.mk "trap_taken"

  -- Output logic
  let n_skipwr := Wire.mk "n_skipwr"
  let write_en_pre := Wire.mk "write_en_pre"
  let active_is_drain := Wire.mk "active_is_drain"
  let active_is_drain_sb := Wire.mk "active_is_drain_sb"
  let active_is_mov := Wire.mk "active_is_mov"
  let active_is_flush := Wire.mk "active_is_flush"
  let active_is_setpc := Wire.mk "active_is_setpc"
  let flush_or_setpc := Wire.mk "flush_or_setpc"

  -- MSTATUS_TRAP or READ_CSR → assert csr_read_en
  let read_or_mstatus := Wire.mk "read_or_mstatus"
  -- MSTATUS_TRAP or WRITE_CSR (non-skip) → assert csr_write_en
  let write_or_mstatus := Wire.mk "write_or_mstatus"

  let outputGates :=
    [-- fence_i_suppress = active_q (stall fetch while sequencer runs)
     Gate.mkBUF active_q fence_i_suppress,
     -- csr_read_en = active AND (is_read_csr OR is_mstatus_trap) AND not_stalling
     Gate.mkOR is_read_csr is_mstatus_trap read_or_mstatus,
     Gate.mkAND active_q read_or_mstatus active_is_drain,  -- reuse wire name
     Gate.mkAND active_is_drain not_stalling csr_read_en,
     -- csr_write_en = active AND (is_write_csr AND NOT(skip) OR is_mstatus_trap) AND not_stalling
     Gate.mkNOT skipwr_q n_skipwr,
     Gate.mkAND is_write_csr n_skipwr write_en_pre,
     Gate.mkOR write_en_pre is_mstatus_trap write_or_mstatus,
     Gate.mkAND active_q write_or_mstatus active_is_drain_sb,
     Gate.mkAND active_is_drain_sb not_stalling csr_write_en,
     -- csr_cdb_inject = active AND is_mov_to_rd AND not_stalling
     Gate.mkAND active_q is_mov_to_rd active_is_mov,
     Gate.mkAND active_is_mov not_stalling csr_cdb_inject,
     -- fence_i_redir_valid = active AND (is_flush_fetch OR is_set_pc) AND not_stalling
     Gate.mkAND active_q is_flush_fetch active_is_flush,
     Gate.mkAND active_q is_set_pc active_is_setpc,
     Gate.mkOR active_is_flush active_is_setpc flush_or_setpc,
     Gate.mkAND flush_or_setpc not_stalling fence_i_redir_valid,
     -- csr_drain_complete = csr_cdb_inject OR fence_i_redir_valid
     Gate.mkOR csr_cdb_inject fence_i_redir_valid csr_drain_complete,
     -- csr_rename_en = start AND csr_flag_in
     Gate.mkAND start csr_flag_in csr_rename_en_out,
     -- mstatus_trap_active = active AND is_mstatus_trap AND not_stalling
     Gate.mkAND active_q is_mstatus_trap (Wire.mk "active_mstatus_pre"),
     Gate.mkAND (Wire.mk "active_mstatus_pre") not_stalling mstatus_trap_active,
     -- trap_taken = is_done AND NOT(csrflag_q) AND active_q AND NOT(is_flush_fetch)
     -- TRAP_ENTRY has csrFlag=false; when DONE fires with csrFlag=false and no flush, it's a trap completion
     -- Actually simpler: trap_taken when SET_PC fires (only TRAP_ENTRY uses SET_PC → temp[src])
     -- SET_PC is used by TRAP_ENTRY to redirect to mtvec
     Gate.mkAND active_is_setpc not_stalling trap_taken] ++
    -- csr_cdb_tag = rdtag_q (direct passthrough)
    (List.range 6).map (fun i => Gate.mkBUF rdtag_q[i]! csr_cdb_tag[i]!) ++
    -- csr_cdb_data = temp0_q (old CSR value, for MOV_TO_RD)
    (List.range 32).map (fun i => Gate.mkBUF temp0_q[i]! csr_cdb_data[i]!) ++
    -- csr_write_data: temp[src] for WRITE_CSR; transformed mstatus for MSTATUS_TRAP
    -- rom_data[16] = src bit: 0 → temp0_q, 1 → temp1_q
    -- MSTATUS_TRAP transform: clear MIE(bit3), copy old MIE→MPIE(bit7), set MPP=M(bits 12:11)
    (List.range 32).map (fun i =>
      let wr_src := Wire.mk s!"wr_src_{i}"
      Gate.mkMUX temp0_q[i]! temp1_q[i]! rom_data[16]! wr_src) ++
    (List.range 32).map (fun i =>
      let mstatus_bit :=
        if i == 3 then Wire.mk "tied_low"            -- MIE = 0
        else if i == 7 then csr_read_data[3]!         -- MPIE = old MIE
        else if i == 11 || i == 12 then Wire.mk "vdd_tie"  -- MPP = M (0b11)
        else csr_read_data[i]!                        -- pass through
      Gate.mkMUX (Wire.mk s!"wr_src_{i}") mstatus_bit is_mstatus_trap csr_write_data[i]!) ++
    -- csr_addr_out: normally csraddr_q; for MSTATUS_TRAP, force 0x300 (mstatus)
    -- 0x300 = 0b001100000000, bit8=1, bit9=1
    (List.range 12).map (fun i =>
      let mstatus_addr_bit :=
        if i == 8 || i == 9 then Wire.mk "vdd_tie" else Wire.mk "tied_low"
      Gate.mkMUX csraddr_q[i]! mstatus_addr_bit is_mstatus_trap csr_addr_out[i]!) ++
    -- fence_i_redir_next: for FLUSH_FETCH use PC+4, for SET_PC use temp[src]
    -- ROM entry src=1 for SET_PC in TRAP_ENTRY (temp1 holds mtvec)
    -- Use rom_data[16] (src bit) to select temp0 vs temp1
    (List.range 32).map (fun i =>
      let temp_src := Wire.mk s!"setpc_src_{i}"
      Gate.mkMUX temp0_q[i]! temp1_q[i]! rom_data[16]! temp_src) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX (Wire.mk s!"redir_pc4_{i}") (Wire.mk s!"setpc_src_{i}") is_set_pc fence_i_redir_next[i]!)

  -- PC+4 redirect input (for FLUSH_FETCH)
  let redir_pc4 := (List.range 32).map (fun i => Wire.mk s!"redir_pc4_{i}")

  -- Tied-low constant
  let tiedLowGate := [Gate.mkNOT (Wire.mk "vdd_tie") (Wire.mk "tied_low")]

  let allGates :=
    tiedLowGate ++
    [activeDFF, hasrdDFF, skipwrDFF, csrflagDFF] ++
    stallGates ++
    incGates ++
    upc_mux_stall ++ upc_next_mux ++
    activeGates ++
    rs1cap_mux ++ csraddr_start_mux ++ csraddr_mux ++ rdtag_mux ++ pccap_mux ++ captureBitGates ++
    alu_or_gates ++ alu_andn_gates ++
    temp0Gates ++ temp1Gates ++
    outputGates

  let allInstances := [decoderInst, upcReg, temp0Reg, temp1Reg, rs1capReg, csraddrReg, rdtagReg, pccapReg]

  { name := "MicrocodeSequencer"
    inputs := [clock, reset, start, Wire.mk "vdd_tie"] ++
              seq_id ++ rs1_val ++ csr_addr_in ++ rd_tag_in ++
              [has_rd_in, skip_write_in, csr_flag_in, rob_empty, sb_empty] ++
              csr_read_data ++ rom_data ++ redir_pc4 ++ [pipeline_flush] ++ pc_in
    outputs := [active_q, fence_i_suppress, csr_drain_complete,
                csr_cdb_inject, csr_write_en, csr_read_en,
                fence_i_redir_valid, csr_rename_en_out, csrflag_q,
                mstatus_trap_active, trap_taken] ++
               csr_cdb_tag ++ csr_cdb_data ++ csr_write_data ++
               csr_addr_out ++ fence_i_redir_next ++ upc_q
    gates := allGates
    instances := allInstances
    signalGroups := [
      { name := "rs1_val", width := 32, wires := rs1_val },
      { name := "csr_addr_in", width := 12, wires := csr_addr_in },
      { name := "rd_tag_in", width := 6, wires := rd_tag_in },
      { name := "csr_read_data", width := 32, wires := csr_read_data },
      { name := "rom_data", width := 24, wires := rom_data },
      { name := "csr_cdb_tag", width := 6, wires := csr_cdb_tag },
      { name := "csr_cdb_data", width := 32, wires := csr_cdb_data },
      { name := "csr_write_data", width := 32, wires := csr_write_data },
      { name := "csr_addr_out", width := 12, wires := csr_addr_out },
      { name := "fence_i_redir_next", width := 32, wires := fence_i_redir_next },
      { name := "upc_q", width := 6, wires := upc_q },
      { name := "redir_pc4", width := 32, wires := redir_pc4 },
      { name := "seq_id", width := 3, wires := seq_id },
      { name := "pc_in", width := 32, wires := pc_in }
    ] }

end Shoumei.RISCV.Microcode

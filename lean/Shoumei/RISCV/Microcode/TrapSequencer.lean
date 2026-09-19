/-
Microcode/TrapSequencer.lean - Dedicated sequencer for TRAP_ENTRY and MRET sequences.

Replaces the generic MicrocodeSequencer for trap handling, eliminating 66 constant
tie-offs (LINT-32) and shared constant nets (LINT-33).
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.Register

namespace Shoumei.RISCV.Microcode

open Shoumei
open Shoumei.Circuits.Sequential

/-- Build the dedicated trap sequencer circuit.

    Inputs:
    - clock, reset
    - start: trigger from decode (useq_start_irq)
    - is_interrupt: interrupt flag (latched on start for mcause)
    - is_mret: 1 for MRET sequence, 0 for TRAP_ENTRY sequence
    - rob_empty: ROB drain complete
    - sb_empty: store buffer drain complete
    - csr_read_data[31:0]: CSR register file read result
    - pipeline_flush: cancel on misprediction
    - pc_in[31:0]: PC of the trapping instruction (latched on start)

    Outputs:
    - active: sequencer is running (suppresses fetch)
    - suppress: stall fetch while active
    - drain_complete: asserted during SET_PC step
    - write_en: CSR write strobe
    - write_data[31:0]: CSR write value
    - addr_out[11:0]: CSR address for read/write
    - redir_next[31:0]: redirect target (mtvec or mepc)
    - mstatus_trap_active: asserted during MSTATUS_TRAP step
    - mstatus_mret_active: asserted during MSTATUS_MRET step
-/
def mkTrapSequencer : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let start := Wire.mk "start"
  let is_interrupt := Wire.mk "is_interrupt"
  let is_mret := Wire.mk "is_mret"
  let rob_empty := Wire.mk "rob_empty"
  let sb_empty := Wire.mk "sb_empty"
  let pipeline_flush := Wire.mk "pipeline_flush"

  let csr_read_data := (List.range 32).map (fun i => Wire.mk s!"csr_read_data_{i}")
  let pc_in := (List.range 32).map (fun i => Wire.mk s!"pc_in_{i}")

  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- Latches for mode
  let is_mret_q := Wire.mk "is_mret_q"
  let is_mret_d := Wire.mk "is_mret_d"
  let is_mret_mux := Gate.mkMUX is_mret_q is_mret start is_mret_d
  let is_mret_dff := Gate.mkDFF is_mret_d clock reset is_mret_q

  let is_irq_q := Wire.mk "is_irq_q"
  let is_irq_d := Wire.mk "is_irq_d"
  let is_irq_mux := Gate.mkMUX is_irq_q is_interrupt start is_irq_d
  let is_irq_dff := Gate.mkDFF is_irq_d clock reset is_irq_q

  let not_is_mret := Wire.mk "not_is_mret"
  let not_is_irq := Wire.mk "not_is_irq"
  let modeInvGates := [
    Gate.mkNOT is_mret_q not_is_mret,
    Gate.mkNOT is_irq_q not_is_irq
  ]

  -- Active state latch
  let active_q := Wire.mk "active_q"
  let active_d := Wire.mk "active_d"
  let active_dff := Gate.mkDFF active_d clock reset active_q

  -- 4-bit Step register
  let step_q := (List.range 4).map (fun i => Wire.mk s!"step_q_{i}")
  let step_d := (List.range 4).map (fun i => Wire.mk s!"step_d_{i}")
  let stepReg : CircuitInstance := {
    moduleName := "Register4"
    instName := "u_step"
    portMap :=
      (step_d.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
      [("clock", clock), ("reset", reset)] ++
      (step_q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
  }

  -- Inverted step bits
  let n_step_q := (List.range 4).map (fun i => Wire.mk s!"n_step_q_{i}")
  let notStepGates := (List.range 4).map (fun i =>
    Gate.mkNOT step_q[i]! n_step_q[i]!)

  -- Decode steps 0 to 12
  let step_is := (List.range 13).map (fun i => Wire.mk s!"step_is_{i}")
  let stepDecGates : List Gate := (List.range 13).flatMap (fun k =>
    let b0 := if k % 2 == 1 then step_q[0]! else n_step_q[0]!
    let b1 := if (k / 2) % 2 == 1 then step_q[1]! else n_step_q[1]!
    let b2 := if (k / 4) % 2 == 1 then step_q[2]! else n_step_q[2]!
    let b3 := if (k / 8) % 2 == 1 then step_q[3]! else n_step_q[3]!
    let t01 := Wire.mk s!"st_t01_{k}"
    let t23 := Wire.mk s!"st_t23_{k}"
    [Gate.mkAND b0 b1 t01,
     Gate.mkAND b2 b3 t23,
     Gate.mkAND t01 t23 step_is[k]!])

  -- Step control signals
  let trap_step_0 := Wire.mk "trap_step_0"
  let trap_step_1 := Wire.mk "trap_step_1"
  let trap_step_2 := Wire.mk "trap_step_2"
  let trap_step_3 := Wire.mk "trap_step_3"
  let trap_step_4 := Wire.mk "trap_step_4"
  let trap_step_5 := Wire.mk "trap_step_5"
  let trap_step_6 := Wire.mk "trap_step_6"
  let trap_step_7 := Wire.mk "trap_step_7"
  let trap_step_8 := Wire.mk "trap_step_8"
  let trap_step_9 := Wire.mk "trap_step_9"
  let trap_step_10 := Wire.mk "trap_step_10"
  let trap_step_11 := Wire.mk "trap_step_11"
  let trap_step_12 := Wire.mk "trap_step_12"

  let mret_step_0 := Wire.mk "mret_step_0"
  let mret_step_1 := Wire.mk "mret_step_1"
  let mret_step_2 := Wire.mk "mret_step_2"
  let mret_step_3 := Wire.mk "mret_step_3"
  let mret_step_4 := Wire.mk "mret_step_4"
  let mret_step_5 := Wire.mk "mret_step_5"
  let mret_step_6 := Wire.mk "mret_step_6"
  let mret_step_7 := Wire.mk "mret_step_7"

  let not_is_mret_act := Wire.mk "not_is_mret_act"
  let is_mret_act := Wire.mk "is_mret_act"
  let modeActGates := [
    Gate.mkAND not_is_mret active_q not_is_mret_act,
    Gate.mkAND is_mret_q active_q is_mret_act
  ]

  let stepModeGates : List Gate := modeActGates ++ [
    Gate.mkAND not_is_mret_act step_is[0]! trap_step_0,
    Gate.mkAND not_is_mret_act step_is[1]! trap_step_1,
    Gate.mkAND not_is_mret_act step_is[2]! trap_step_2,
    Gate.mkAND not_is_mret_act step_is[3]! trap_step_3,
    Gate.mkAND not_is_mret_act step_is[4]! trap_step_4,
    Gate.mkAND not_is_mret_act step_is[5]! trap_step_5,
    Gate.mkAND not_is_mret_act step_is[6]! trap_step_6,
    Gate.mkAND not_is_mret_act step_is[7]! trap_step_7,
    Gate.mkAND not_is_mret_act step_is[8]! trap_step_8,
    Gate.mkAND not_is_mret_act step_is[9]! trap_step_9,
    Gate.mkAND not_is_mret_act step_is[10]! trap_step_10,
    Gate.mkAND not_is_mret_act step_is[11]! trap_step_11,
    Gate.mkAND not_is_mret_act step_is[12]! trap_step_12,

    Gate.mkAND is_mret_act step_is[0]! mret_step_0,
    Gate.mkAND is_mret_act step_is[1]! mret_step_1,
    Gate.mkAND is_mret_act step_is[2]! mret_step_2,
    Gate.mkAND is_mret_act step_is[3]! mret_step_3,
    Gate.mkAND is_mret_act step_is[4]! mret_step_4,
    Gate.mkAND is_mret_act step_is[5]! mret_step_5,
    Gate.mkAND is_mret_act step_is[6]! mret_step_6,
    Gate.mkAND is_mret_act step_is[7]! mret_step_7
  ]

  -- Stall logic
  -- DRAIN step 0 waits on rob_empty
  let is_drain := Wire.mk "is_drain"
  let not_rob_empty := Wire.mk "not_rob_empty"
  let drain_stall := Wire.mk "drain_stall"

  -- DRAIN_SB waits on sb_empty: trap_step_9, mret_step_1, mret_step_3
  let mret_sb13 := Wire.mk "mret_sb13"
  let is_drain_sb := Wire.mk "is_drain_sb"
  let not_sb_empty := Wire.mk "not_sb_empty"
  let drain_sb_stall := Wire.mk "drain_sb_stall"

  let stall_req := Wire.mk "stall_req"
  let stalling := Wire.mk "stalling"
  let not_stalling := Wire.mk "not_stalling"

  let stallGates : List Gate := [
    Gate.mkOR trap_step_0 mret_step_0 is_drain,
    Gate.mkNOT rob_empty not_rob_empty,
    Gate.mkAND is_drain not_rob_empty drain_stall,

    Gate.mkOR mret_step_1 mret_step_3 mret_sb13,
    Gate.mkOR trap_step_9 mret_sb13 is_drain_sb,
    Gate.mkNOT sb_empty not_sb_empty,
    Gate.mkAND is_drain_sb not_sb_empty drain_sb_stall,

    Gate.mkOR drain_stall drain_sb_stall stall_req,
    Gate.mkAND stall_req active_q stalling,
    Gate.mkNOT stalling not_stalling
  ]

  -- Completion / Done logic
  let is_done := Wire.mk "is_done"
  let done_or_flush := Wire.mk "done_or_flush"
  let not_done_flush := Wire.mk "not_done_flush"
  let active_hold := Wire.mk "active_hold"

  let doneGates : List Gate := [
    Gate.mkOR trap_step_12 mret_step_7 is_done,
    Gate.mkOR is_done pipeline_flush done_or_flush,
    Gate.mkNOT done_or_flush not_done_flush,
    Gate.mkAND active_q not_done_flush active_hold,
    Gate.mkOR start active_hold active_d
  ]

  -- Step counter increment logic: step_p1 = step_q + 1
  let c_adv := Wire.mk "c_adv"
  let c := (List.range 4).map (fun i => Wire.mk s!"c_{i}")
  let step_p1 := (List.range 4).map (fun i => Wire.mk s!"step_p1_{i}")
  let step_adv := (List.range 4).map (fun i => Wire.mk s!"step_adv_{i}")
  let step_reset := Wire.mk "step_reset"

  let stepIncGates : List Gate := [
    Gate.mkAND active_q not_stalling c_adv,
    Gate.mkXOR step_q[0]! c_adv step_p1[0]!,
    Gate.mkAND step_q[0]! c_adv c[0]!,

    Gate.mkXOR step_q[1]! c[0]! step_p1[1]!,
    Gate.mkAND step_q[1]! c[0]! c[1]!,

    Gate.mkXOR step_q[2]! c[1]! step_p1[2]!,
    Gate.mkAND step_q[2]! c[1]! c[2]!,

    Gate.mkXOR step_q[3]! c[2]! step_p1[3]!,
    Gate.mkOR start done_or_flush step_reset
  ] ++
  (List.range 4).flatMap (fun i => [
    Gate.mkMUX step_p1[i]! step_q[i]! stalling step_adv[i]!,
    Gate.mkMUX step_adv[i]! zero step_reset step_d[i]!
  ])

  -- PC capture register (u_pccap)
  let pccap_q := (List.range 32).map (fun i => Wire.mk s!"pccap_q_{i}")
  let pccap_d := (List.range 32).map (fun i => Wire.mk s!"pccap_d_{i}")
  let pccapMuxGates := (List.range 32).map (fun i =>
    Gate.mkMUX pccap_q[i]! pc_in[i]! start pccap_d[i]!)
  let pccapReg : CircuitInstance := {
    moduleName := "Register32"
    instName := "u_pccap"
    portMap :=
      (pccap_d.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
      [("clock", clock), ("reset", reset)] ++
      (pccap_q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
  }

  -- Temp0 register (holds pc for mepc, or cause for mcause)
  let temp0_q := (List.range 32).map (fun i => Wire.mk s!"temp0_q_{i}")
  let temp0_d := (List.range 32).map (fun i => Wire.mk s!"temp0_d_{i}")
  let temp0_after_load_pc := (List.range 32).map (fun i => Wire.mk s!"t0_alpc_{i}")

  -- Cause constants: IRQ -> 0x80000007, Exception -> 0x0000000B (11)
  let cause_bits : List Wire := (List.range 32).map (fun i =>
    if i == 31 then is_irq_q
    else if i == 3 then not_is_irq
    else if i == 2 then is_irq_q
    else if i == 1 || i == 0 then one
    else zero)

  let temp0MuxGates : List Gate := (List.range 32).flatMap (fun i => [
    Gate.mkMUX temp0_q[i]! pccap_q[i]! trap_step_3 temp0_after_load_pc[i]!,
    Gate.mkMUX temp0_after_load_pc[i]! cause_bits[i]! trap_step_6 temp0_d[i]!
  ])
  let temp0Reg : CircuitInstance := {
    moduleName := "Register32"
    instName := "u_temp0"
    portMap :=
      (temp0_d.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
      [("clock", clock), ("reset", reset)] ++
      (temp0_q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
  }

  -- Temp1 register (holds CSR read result for mtvec / mepc redirection)
  let temp1_q := (List.range 32).map (fun i => Wire.mk s!"temp1_q_{i}")
  let temp1_d := (List.range 32).map (fun i => Wire.mk s!"temp1_d_{i}")
  let read_csr_sel := Wire.mk "read_csr_sel"
  let read_csr_fire := Wire.mk "read_csr_fire"

  let temp1CtrlGates : List Gate := [
    Gate.mkOR trap_step_10 mret_step_4 read_csr_sel,
    Gate.mkAND read_csr_sel not_stalling read_csr_fire
  ]
  let temp1MuxGates := (List.range 32).map (fun i =>
    Gate.mkMUX temp1_q[i]! csr_read_data[i]! read_csr_fire temp1_d[i]!)
  let temp1Reg : CircuitInstance := {
    moduleName := "Register32"
    instName := "u_temp1"
    portMap :=
      (temp1_d.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
      [("clock", clock), ("reset", reset)] ++
      (temp1_q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
  }

  -- Output controls
  let mstatus_trap_active := Wire.mk "mstatus_trap_active"
  let mstatus_mret_active := Wire.mk "mstatus_mret_active"
  let trap_write_step := Wire.mk "trap_write_step"
  let trap_write_csr := Wire.mk "trap_write_csr"
  let mstatus_any := Wire.mk "mstatus_any"
  let write_en := Wire.mk "write_en"

  let outCtrlGates : List Gate := [
    Gate.mkAND trap_step_1 not_stalling mstatus_trap_active,
    Gate.mkAND mret_step_5 not_stalling mstatus_mret_active,
    Gate.mkOR trap_step_4 trap_step_7 trap_write_step,
    Gate.mkAND trap_write_step not_stalling trap_write_csr,
    Gate.mkOR mstatus_trap_active mstatus_mret_active mstatus_any,
    Gate.mkOR mstatus_any trap_write_csr write_en
  ]

  -- CSR write data logic:
  -- When mstatus_any is high, write transformed mstatus; otherwise write temp0_q
  let write_data := (List.range 32).map (fun i => Wire.mk s!"write_data_{i}")
  let mstatus_write_bits : List (List Gate × Wire) := (List.range 32).map (fun i =>
    if i == 3 then
      -- MIE: 0 on trap, old MPIE (csr_read_data[7]) on mret
      let w := Wire.mk "mst_b3"
      ([Gate.mkMUX zero csr_read_data[7]! mstatus_mret_active w], w)
    else if i == 7 then
      -- MPIE: old MIE (csr_read_data[3]) on trap, 1 on mret
      let w := Wire.mk "mst_b7"
      ([Gate.mkMUX csr_read_data[3]! one mstatus_mret_active w], w)
    else if i == 11 || i == 12 then
      -- MPP: 1 on trap (M-mode), 0 on mret (U-mode)
      let w := Wire.mk s!"mst_b{i}"
      ([Gate.mkMUX one zero mstatus_mret_active w], w)
    else
      ([], csr_read_data[i]!))

  let writeDataGates : List Gate :=
    (mstatus_write_bits.flatMap (fun (gates, _) => gates)) ++
    (List.range 32).map (fun i =>
      let mst_w := mstatus_write_bits[i]!.2
      Gate.mkMUX temp0_q[i]! mst_w mstatus_any write_data[i]!)

  -- CSR Address Decode:
  -- mstatus: 0x300, mepc: 0x341, mcause: 0x342, mtvec: 0x305
  let sel_mepc_trap := Wire.mk "sel_mepc_trap"
  let sel_mepc_mret := Wire.mk "sel_mepc_mret"
  let sel_mepc := Wire.mk "sel_mepc"

  let sel_mcause_steps := Wire.mk "sel_mcause_steps"
  let sel_mcause := Wire.mk "sel_mcause"

  let sel_mtvec_steps0 := Wire.mk "sel_mtvec_steps0"
  let sel_mtvec_steps1 := Wire.mk "sel_mtvec_steps1"
  let sel_mtvec_steps := Wire.mk "sel_mtvec_steps"
  let sel_mtvec := Wire.mk "sel_mtvec"

  let csr_sel_0 := Wire.mk "csr_sel_0"
  let csr_sel_1 := Wire.mk "csr_sel_1"

  let addrDecGates : List Gate := [
    Gate.mkOR trap_step_2 trap_step_3 (Wire.mk "t23"),
    Gate.mkOR (Wire.mk "t23") trap_step_4 sel_mepc_trap,

    Gate.mkOR mret_step_2 mret_step_3 (Wire.mk "m23"),
    Gate.mkOR (Wire.mk "m23") mret_step_4 sel_mepc_mret,

    Gate.mkOR sel_mepc_trap sel_mepc_mret sel_mepc,

    Gate.mkOR trap_step_5 trap_step_6 (Wire.mk "t56"),
    Gate.mkOR (Wire.mk "t56") trap_step_7 sel_mcause_steps,
    Gate.mkAND not_is_mret sel_mcause_steps sel_mcause,

    Gate.mkOR trap_step_8 trap_step_9 sel_mtvec_steps0,
    Gate.mkOR trap_step_10 trap_step_11 sel_mtvec_steps1,
    Gate.mkOR sel_mtvec_steps0 sel_mtvec_steps1 sel_mtvec_steps,
    Gate.mkAND not_is_mret sel_mtvec_steps sel_mtvec,

    -- Dynamic 2-bit CSR select: 00=mstatus, 01=mepc, 10=mcause, 11=mtvec
    Gate.mkOR sel_mepc sel_mtvec csr_sel_0,
    Gate.mkOR sel_mcause sel_mtvec csr_sel_1
  ]

  -- Redirection and Drain Complete
  let set_pc_step := Wire.mk "set_pc_step"
  let drain_complete := Wire.mk "drain_complete"
  let redirGates : List Gate := [
    Gate.mkOR trap_step_11 mret_step_6 set_pc_step,
    Gate.mkAND set_pc_step not_stalling drain_complete
  ]

  -- Outputs
  let active := Wire.mk "active"
  let redir_next := (List.range 32).map (fun i => Wire.mk s!"redir_next_{i}")
  let outBufGates : List Gate :=
    [Gate.mkBUF active_q active] ++
    (List.range 32).map (fun i => Gate.mkBUF temp1_q[i]! redir_next[i]!)

  let allGates : List Gate :=
    [is_mret_mux, is_mret_dff, is_irq_mux, is_irq_dff, active_dff] ++
    modeInvGates ++
    notStepGates ++
    stepDecGates ++
    stepModeGates ++
    stallGates ++
    stepIncGates ++
    doneGates ++
    pccapMuxGates ++
    temp0MuxGates ++
    temp1CtrlGates ++
    temp1MuxGates ++
    outCtrlGates ++
    writeDataGates ++
    addrDecGates ++
    redirGates ++
    outBufGates

  let allInstances : List CircuitInstance := [
    stepReg, pccapReg, temp0Reg, temp1Reg
  ]

  { name := "TrapSequencer"
    inputs := [clock, reset, start, is_interrupt, is_mret, rob_empty, sb_empty] ++
              csr_read_data ++ [pipeline_flush] ++ pc_in
    outputs := [active, drain_complete, write_en] ++
               write_data ++ [csr_sel_0, csr_sel_1] ++ redir_next ++
               [mstatus_trap_active, mstatus_mret_active]
    gates := allGates
    instances := allInstances
    signalGroups := [
      { name := "csr_read_data", width := 32, wires := csr_read_data },
      { name := "pc_in", width := 32, wires := pc_in },
      { name := "write_data", width := 32, wires := write_data },
      { name := "csr_sel", width := 2, wires := [csr_sel_0, csr_sel_1] },
      { name := "redir_next", width := 32, wires := redir_next }
    ]
    keepHierarchy := true
  }

/-- Convenience circuit generator. -/
def trapSequencerCircuit : Circuit := mkTrapSequencer

end Shoumei.RISCV.Microcode

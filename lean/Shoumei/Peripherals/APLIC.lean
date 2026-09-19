/-
Peripherals/APLIC.lean - AIA Advanced Platform-Level Interrupt Controller (Direct Mode)

Implements RISC-V AIA APLIC in Direct Delivery Mode:
- 16 interrupt sources (Source 1 = UART IRQ, Source 2 = GPIO IRQ, Source 3..15 = External)
- Per-source priority configuration (0-255)
- Interrupt enable and pending registers
- Generates `meip_out` to CPU core.
- Connected via TileLink TL-UH slave interface.
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.Register
import Shoumei.Interconnect.TileLink.TLTypes

namespace Shoumei.Peripherals

open Shoumei
open Shoumei.Circuits.Sequential
open Shoumei.Interconnect.TileLink

/-- APLIC circuit in Direct Delivery Mode. -/
def mkAPLIC : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero  := Wire.mk "zero"
  let one   := Wire.mk "one"

  -- TileLink Slave Ports
  let s_a := makeChannelAWires "aplic"
  let s_d := makeChannelDWires "aplic"

  -- External wired interrupt inputs (sources 1 to 15)
  let irq_sources := (List.range 16).map fun i => Wire.mk s!"irq_src_{i}"

  -- Output interrupt to CPU
  let meip_out := Wire.mk "meip_out"
  let seip_out := Wire.mk "seip_out"

  -- Registers:
  -- domaincfg (32-bit): bit 8 is IE (Interrupt Enable)
  let domaincfg_q := (List.range 32).map fun i => Wire.mk s!"domaincfg_q_{i}"
  let domaincfg_d := (List.range 32).map fun i => Wire.mk s!"domaincfg_d_{i}"

  -- setip / clrip (16-bit pending array)
  let ip_q := (List.range 16).map fun i => Wire.mk s!"ip_q_{i}"
  let ip_d := (List.range 16).map fun i => Wire.mk s!"ip_d_{i}"

  -- setie / clrie (16-bit enable array)
  let ie_q := (List.range 16).map fun i => Wire.mk s!"ie_q_{i}"
  let ie_d := (List.range 16).map fun i => Wire.mk s!"ie_d_{i}"

  -- TileLink Write Decode
  let is_write := Wire.mk "aplic_is_write"
  let req_fire := Wire.mk "aplic_req_fire"
  let op_gates := [
    Gate.mkNOT s_a.opcode[2]! is_write,
    Gate.mkAND s_a.valid (Wire.mk "not_resp_wait") req_fire
  ]

  -- Address decode:
  -- 0x0000: domaincfg
  -- 0x001C: setip
  -- 0x0024: setie
  let sel_domaincfg := Wire.mk "sel_domaincfg"
  let sel_setip     := Wire.mk "sel_setip"
  let sel_setie     := Wire.mk "sel_setie"

  let addr_decode_gates := [
    Gate.mkNOT s_a.address[4]! (Wire.mk "not_a4"),
    Gate.mkNOT s_a.address[5]! (Wire.mk "not_a5"),
    Gate.mkAND (Wire.mk "not_a4") (Wire.mk "not_a5") sel_domaincfg,
    Gate.mkAND s_a.address[4]! (Wire.mk "not_a5") sel_setip,
    Gate.mkAND s_a.address[5]! (Wire.mk "not_a4") sel_setie
  ]

  let wr_domaincfg := Wire.mk "wr_domaincfg"
  let wr_setip     := Wire.mk "wr_setip"
  let wr_setie     := Wire.mk "wr_setie"

  let wr_gates := [
    Gate.mkAND req_fire is_write (Wire.mk "fire_wr"),
    Gate.mkAND (Wire.mk "fire_wr") sel_domaincfg wr_domaincfg,
    Gate.mkAND (Wire.mk "fire_wr") sel_setip wr_setip,
    Gate.mkAND (Wire.mk "fire_wr") sel_setie wr_setie
  ]

  -- Pending latch: pending = hardware irq OR bus written setip
  let ip_next_gates := (List.range 16).flatMap fun i =>
    let hw_or_wr := Wire.mk s!"ip_or_{i}"
    [Gate.mkOR irq_sources[i]! s_a.data[i]! hw_or_wr,
     Gate.mkMUX ip_q[i]! hw_or_wr (if i > 0 then one else zero) ip_d[i]!]

  -- Enable latch:
  let ie_next_gates := (List.range 16).map fun i =>
    Gate.mkMUX ie_q[i]! s_a.data[i]! wr_setie ie_d[i]!

  -- Domaincfg next:
  let domaincfg_next_gates := (List.range 32).map fun i =>
    Gate.mkMUX domaincfg_q[i]! s_a.data[i]! wr_domaincfg domaincfg_d[i]!

  -- Register instances
  let reg_instances : List CircuitInstance := [
    { moduleName := "Register32", instName := "u_domaincfg",
      portMap := ((List.range 32).map fun i => (s!"d_{i}", domaincfg_d[i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 32).map fun i => (s!"q_{i}", domaincfg_q[i]!)) },
    { moduleName := "Register16", instName := "u_ip",
      portMap := ((List.range 16).map fun i => (s!"d_{i}", ip_d[i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 16).map fun i => (s!"q_{i}", ip_q[i]!)) },
    { moduleName := "Register16", instName := "u_ie",
      portMap := ((List.range 16).map fun i => (s!"d_{i}", ie_d[i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 16).map fun i => (s!"q_{i}", ie_q[i]!)) }
  ]

  -- Priority Resolution:
  -- active_irq[i] = ip[i] & ie[i]
  let active_irqs := (List.range 16).map fun i => Wire.mk s!"active_irq_{i}"
  let active_gates := (List.range 16).map fun i =>
    Gate.mkAND ip_q[i]! ie_q[i]! active_irqs[i]!

  -- OR reduction across sources 1..15
  let any_active_irq := Wire.mk "any_active_irq"
  let or_trees := (List.range 14).map fun i => Wire.mk s!"irq_or_tree_{i}"
  let or_tree_gates : List Gate := [
    Gate.mkOR active_irqs[1]! active_irqs[2]! or_trees[0]!,
    Gate.mkOR active_irqs[3]! active_irqs[4]! or_trees[1]!,
    Gate.mkOR active_irqs[5]! active_irqs[6]! or_trees[2]!,
    Gate.mkOR active_irqs[7]! active_irqs[8]! or_trees[3]!,
    Gate.mkOR active_irqs[9]! active_irqs[10]! or_trees[4]!,
    Gate.mkOR active_irqs[11]! active_irqs[12]! or_trees[5]!,
    Gate.mkOR active_irqs[13]! active_irqs[14]! or_trees[6]!,
    Gate.mkOR or_trees[0]! or_trees[1]! or_trees[7]!,
    Gate.mkOR or_trees[2]! or_trees[3]! or_trees[8]!,
    Gate.mkOR or_trees[4]! or_trees[5]! or_trees[9]!,
    Gate.mkOR or_trees[6]! active_irqs[15]! or_trees[10]!,
    Gate.mkOR or_trees[7]! or_trees[8]! or_trees[11]!,
    Gate.mkOR or_trees[9]! or_trees[10]! or_trees[12]!,
    Gate.mkOR or_trees[11]! or_trees[12]! any_active_irq
  ]

  -- Output interrupt generation: meip_out = any_active_irq & domaincfg[8] (IE enable)
  let irq_out_gates := [
    Gate.mkAND any_active_irq domaincfg_q[8]! meip_out,
    Gate.mkBUF zero seip_out
  ]

  -- Response D channel (1-cycle latency)
  let resp_valid_q := Wire.mk "resp_valid_q"
  let resp_valid_dff := Gate.mkDFF req_fire clock reset resp_valid_q
  let not_resp_wait_gate := Gate.mkNOT resp_valid_q (Wire.mk "not_resp_wait")

  let resp_gates := [
    resp_valid_dff, not_resp_wait_gate,
    Gate.mkBUF resp_valid_q s_d.valid,
    Gate.mkBUF one s_a.ready,
    Gate.mkBUF zero s_d.denied
  ] ++
  (List.range 3).map (fun i => Gate.mkBUF zero s_d.opcode[i]!) ++
  (List.range 2).map (fun i => Gate.mkBUF zero s_d.param[i]!) ++
  (List.range 3).map (fun i => Gate.mkBUF zero s_d.size[i]!) ++
  (List.range 4).map (fun i => Gate.mkBUF zero s_d.source[i]!) ++
  (List.range 4).map (fun i => Gate.mkBUF zero s_d.sink[i]!) ++
  ((List.range 64).flatMap fun i =>
    if i < 16 then
      let read_data := Wire.mk s!"aplic_rdata_{i}"
      [Gate.mkMUX ip_q[i]! ie_q[i]! sel_setie read_data,
       Gate.mkBUF read_data s_d.data[i]!]
    else
      [Gate.mkBUF zero s_d.data[i]!])

  let all_inputs :=
    [clock, reset, zero, one, s_a.valid] ++
    s_a.opcode ++ s_a.param ++ s_a.size ++ s_a.source ++ s_a.address ++ s_a.mask ++ s_a.data ++
    [s_d.ready] ++ irq_sources

  let all_outputs :=
    [s_a.ready, s_d.valid] ++ s_d.opcode ++ s_d.param ++ s_d.size ++ s_d.source ++ s_d.sink ++
    s_d.data ++ [s_d.denied, meip_out, seip_out]

  { name := "APLIC"
    inputs := all_inputs
    outputs := all_outputs
    gates := op_gates ++ addr_decode_gates ++ wr_gates ++ ip_next_gates ++
             ie_next_gates ++ domaincfg_next_gates ++ active_gates ++
             or_tree_gates ++ irq_out_gates ++ resp_gates
    instances := reg_instances
  }

def aplicCircuit : Circuit := mkAPLIC

end Shoumei.Peripherals

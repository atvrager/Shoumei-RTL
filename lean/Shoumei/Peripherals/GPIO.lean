/-
Peripherals/GPIO.lean - 8-bit GPIO Peripheral with TileLink TL-UH Interface

Registers:
- 0x00: DATA_IN  (R: samples gpio_i)
- 0x04: DATA_OUT (R/W: drives gpio_o)
- 0x08: DIR      (R/W: drives gpio_oen, 1=output, 0=input)
- 0x0C: INT_EN   (R/W: interrupt enable mask)
Outputs:
- gpio_o[7:0], gpio_oen[7:0], gpio_irq (to APLIC source 2)
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.Register
import Shoumei.Interconnect.TileLink.TLTypes

namespace Shoumei.Peripherals

open Shoumei
open Shoumei.Circuits.Sequential
open Shoumei.Interconnect.TileLink

/-- 8-bit GPIO peripheral with TileLink TL-UH slave interface. -/
def mkGPIO : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero  := Wire.mk "zero"
  let one   := Wire.mk "one"

  -- TileLink Slave Ports
  let s_a := makeChannelAWires "gpio"
  let s_d := makeChannelDWires "gpio"

  -- External pins
  let gpio_i   := (List.range 8).map fun i => Wire.mk s!"gpio_i_{i}"
  let gpio_o   := (List.range 8).map fun i => Wire.mk s!"gpio_o_{i}"
  let gpio_oen := (List.range 8).map fun i => Wire.mk s!"gpio_oen_{i}"
  let gpio_irq := Wire.mk "gpio_irq"

  -- Registers:
  -- data_out (8-bit)
  let data_out_q := (List.range 8).map fun i => Wire.mk s!"data_out_q_{i}"
  let data_out_d := (List.range 8).map fun i => Wire.mk s!"data_out_d_{i}"

  -- dir (8-bit)
  let dir_q := (List.range 8).map fun i => Wire.mk s!"dir_q_{i}"
  let dir_d := (List.range 8).map fun i => Wire.mk s!"dir_d_{i}"

  -- int_en (8-bit)
  let int_en_q := (List.range 8).map fun i => Wire.mk s!"int_en_q_{i}"
  let int_en_d := (List.range 8).map fun i => Wire.mk s!"int_en_d_{i}"

  -- TileLink Write Decode
  let is_write := Wire.mk "gpio_is_write"
  let req_fire := Wire.mk "gpio_req_fire"
  let op_gates := [
    Gate.mkNOT s_a.opcode[2]! is_write,
    Gate.mkAND s_a.valid (Wire.mk "not_resp_wait") req_fire
  ]

  -- Address decode:
  -- 0x00: DATA_IN
  -- 0x04: DATA_OUT
  -- 0x08: DIR
  -- 0x0C: INT_EN
  let sel_din  := Wire.mk "sel_din"
  let sel_dout := Wire.mk "sel_dout"
  let sel_dir  := Wire.mk "sel_dir"
  let sel_ie   := Wire.mk "sel_ie"

  let addr_decode_gates := [
    Gate.mkNOT s_a.address[2]! (Wire.mk "not_a2"),
    Gate.mkNOT s_a.address[3]! (Wire.mk "not_a3"),
    Gate.mkAND (Wire.mk "not_a3") (Wire.mk "not_a2") sel_din,
    Gate.mkAND (Wire.mk "not_a3") s_a.address[2]! sel_dout,
    Gate.mkAND s_a.address[3]! (Wire.mk "not_a2") sel_dir,
    Gate.mkAND s_a.address[3]! s_a.address[2]! sel_ie
  ]

  let wr_dout := Wire.mk "wr_dout"
  let wr_dir  := Wire.mk "wr_dir"
  let wr_ie   := Wire.mk "wr_ie"

  let wr_gates := [
    Gate.mkAND req_fire is_write (Wire.mk "fire_wr"),
    Gate.mkAND (Wire.mk "fire_wr") sel_dout wr_dout,
    Gate.mkAND (Wire.mk "fire_wr") sel_dir wr_dir,
    Gate.mkAND (Wire.mk "fire_wr") sel_ie wr_ie
  ]

  -- Next value MUXes
  let reg_mux_gates :=
    ((List.range 8).map fun i =>
      Gate.mkMUX data_out_q[i]! s_a.data[i]! wr_dout data_out_d[i]!) ++
    ((List.range 8).map fun i =>
      Gate.mkMUX dir_q[i]! s_a.data[i]! wr_dir dir_d[i]!) ++
    ((List.range 8).map fun i =>
      Gate.mkMUX int_en_q[i]! s_a.data[i]! wr_ie int_en_d[i]!)

  -- Register instances
  let reg_instances : List CircuitInstance := [
    { moduleName := "Register8", instName := "u_dout",
      portMap := ((List.range 8).map fun i => (s!"d_{i}", data_out_d[i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 8).map fun i => (s!"q_{i}", data_out_q[i]!)) },
    { moduleName := "Register8", instName := "u_dir",
      portMap := ((List.range 8).map fun i => (s!"d_{i}", dir_d[i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 8).map fun i => (s!"q_{i}", dir_q[i]!)) },
    { moduleName := "Register8", instName := "u_ie",
      portMap := ((List.range 8).map fun i => (s!"d_{i}", int_en_d[i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 8).map fun i => (s!"q_{i}", int_en_q[i]!)) }
  ]

  -- Drive output pins
  let pin_drive_gates :=
    ((List.range 8).map fun i => Gate.mkBUF data_out_q[i]! gpio_o[i]!) ++
    ((List.range 8).map fun i => Gate.mkBUF dir_q[i]! gpio_oen[i]!)

  -- Interrupt generation: OR(gpio_i[i] & int_en_q[i])
  let irq_bits := (List.range 8).map fun i => Wire.mk s!"irq_bit_{i}"
  let irq_bit_gates := (List.range 8).map fun i =>
    Gate.mkAND gpio_i[i]! int_en_q[i]! irq_bits[i]!

  let irq_trees := (List.range 6).map fun i => Wire.mk s!"irq_tree_{i}"
  let irq_tree_gates : List Gate := [
    Gate.mkOR irq_bits[0]! irq_bits[1]! irq_trees[0]!,
    Gate.mkOR irq_bits[2]! irq_bits[3]! irq_trees[1]!,
    Gate.mkOR irq_bits[4]! irq_bits[5]! irq_trees[2]!,
    Gate.mkOR irq_bits[6]! irq_bits[7]! irq_trees[3]!,
    Gate.mkOR irq_trees[0]! irq_trees[1]! irq_trees[4]!,
    Gate.mkOR irq_trees[2]! irq_trees[3]! irq_trees[5]!,
    Gate.mkOR irq_trees[4]! irq_trees[5]! gpio_irq
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
    if i < 8 then
      let mux1 := Wire.mk s!"gpio_r_m1_{i}"
      let mux2 := Wire.mk s!"gpio_r_m2_{i}"
      let out_w := Wire.mk s!"gpio_rdata_{i}"
      [Gate.mkMUX gpio_i[i]! data_out_q[i]! sel_dout mux1,
       Gate.mkMUX dir_q[i]! int_en_q[i]! sel_ie mux2,
       Gate.mkMUX mux1 mux2 (Wire.mk s!"sel_high_{i}") out_w,
       Gate.mkOR sel_dir sel_ie (Wire.mk s!"sel_high_{i}"),
       Gate.mkBUF out_w s_d.data[i]!]
    else
      [Gate.mkBUF zero s_d.data[i]!])

  let all_inputs :=
    [clock, reset, zero, one, s_a.valid] ++
    s_a.opcode ++ s_a.param ++ s_a.size ++ s_a.source ++ s_a.address ++ s_a.mask ++ s_a.data ++
    [s_d.ready] ++ gpio_i

  let all_outputs :=
    [s_a.ready, s_d.valid] ++ s_d.opcode ++ s_d.param ++ s_d.size ++ s_d.source ++ s_d.sink ++
    s_d.data ++ [s_d.denied, gpio_irq] ++ gpio_o ++ gpio_oen

  { name := "GPIO"
    inputs := all_inputs
    outputs := all_outputs
    gates := op_gates ++ addr_decode_gates ++ wr_gates ++ reg_mux_gates ++
             pin_drive_gates ++ irq_bit_gates ++ irq_tree_gates ++ resp_gates
    instances := reg_instances
  }

def gpioCircuit : Circuit := mkGPIO

end Shoumei.Peripherals

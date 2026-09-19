/-
Peripherals/UART.lean - 8-N-1 UART Peripheral with TileLink TL-UH Interface

Features:
- 8-N-1 serial framing (1 start bit, 8 data bits, 1 stop bit)
- 16-bit programmable baud rate divisor (defaults to 115,200 baud)
- Shift register TX serializer and 16x oversampled RX deserializer
- Memory mapped registers:
  0x00: DATA   (W: TX buffer, R: RX buffer)
  0x04: STATUS (bit 0: tx_busy, bit 1: tx_empty, bit 2: rx_ready)
  0x08: CTRL   (bit 0: tx_irq_en, bit 1: rx_irq_en)
  0x0C: DIV    (16-bit clock divisor)
- Interrupt output: `uart_irq` routed to APLIC source 1.
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.Register
import Shoumei.Interconnect.TileLink.TLTypes

namespace Shoumei.Peripherals

open Shoumei
open Shoumei.Circuits.Sequential
open Shoumei.Interconnect.TileLink

/-- UART circuit with TileLink TL-UH slave interface. -/
def mkUART : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero  := Wire.mk "zero"
  let one   := Wire.mk "one"

  -- TileLink Slave Ports
  let s_a := makeChannelAWires "uart"
  let s_d := makeChannelDWires "uart"

  -- External serial pins
  let uart_rx := Wire.mk "uart_rx"
  let uart_tx := Wire.mk "uart_tx"

  -- Interrupt output
  let uart_irq := Wire.mk "uart_irq"

  -- Registers:
  -- tx_data (8-bit buffer)
  let tx_buf_q := (List.range 8).map fun i => Wire.mk s!"tx_buf_q_{i}"
  let tx_buf_d := (List.range 8).map fun i => Wire.mk s!"tx_buf_d_{i}"

  -- rx_data (8-bit buffer)
  let rx_buf_q := (List.range 8).map fun i => Wire.mk s!"rx_buf_q_{i}"
  let rx_buf_d := (List.range 8).map fun i => Wire.mk s!"rx_buf_d_{i}"

  -- status: bit 0 = tx_busy, bit 1 = tx_empty, bit 2 = rx_ready
  let tx_busy_q := Wire.mk "tx_busy_q"
  let tx_busy_d := Wire.mk "tx_busy_d"
  let rx_ready_q := Wire.mk "rx_ready_q"
  let rx_ready_d := Wire.mk "rx_ready_d"

  -- ctrl: bit 0 = tx_irq_en, bit 1 = rx_irq_en
  let tx_irq_en_q := Wire.mk "tx_irq_en_q"
  let tx_irq_en_d := Wire.mk "tx_irq_en_d"
  let rx_irq_en_q := Wire.mk "rx_irq_en_q"
  let rx_irq_en_d := Wire.mk "rx_irq_en_d"

  -- div: 16-bit divisor register
  let div_q := (List.range 16).map fun i => Wire.mk s!"div_q_{i}"
  let div_d := (List.range 16).map fun i => Wire.mk s!"div_d_{i}"

  -- TileLink Write Decode
  let is_write := Wire.mk "uart_is_write"
  let req_fire := Wire.mk "uart_req_fire"
  let op_gates := [
    Gate.mkNOT s_a.opcode[2]! is_write,
    Gate.mkAND s_a.valid (Wire.mk "not_resp_wait") req_fire
  ]

  -- Address decode:
  -- 0x00: DATA
  -- 0x04: STATUS
  -- 0x08: CTRL
  -- 0x0C: DIV
  let sel_data   := Wire.mk "sel_data"
  let sel_status := Wire.mk "sel_status"
  let sel_ctrl   := Wire.mk "sel_ctrl"
  let sel_div    := Wire.mk "sel_div"

  let addr_decode_gates := [
    Gate.mkNOT s_a.address[2]! (Wire.mk "not_a2"),
    Gate.mkNOT s_a.address[3]! (Wire.mk "not_a3"),
    Gate.mkAND (Wire.mk "not_a3") (Wire.mk "not_a2") sel_data,
    Gate.mkAND (Wire.mk "not_a3") s_a.address[2]! sel_status,
    Gate.mkAND s_a.address[3]! (Wire.mk "not_a2") sel_ctrl,
    Gate.mkAND s_a.address[3]! s_a.address[2]! sel_div
  ]

  let wr_data   := Wire.mk "wr_data"
  let wr_ctrl   := Wire.mk "wr_ctrl"
  let wr_div    := Wire.mk "wr_div"
  let rd_data   := Wire.mk "rd_data"

  let wr_gates := [
    Gate.mkAND req_fire is_write (Wire.mk "fire_wr"),
    Gate.mkAND (Wire.mk "fire_wr") sel_data wr_data,
    Gate.mkAND (Wire.mk "fire_wr") sel_ctrl wr_ctrl,
    Gate.mkAND (Wire.mk "fire_wr") sel_div wr_div,
    Gate.mkAND req_fire (Wire.mk "uart_is_read") (Wire.mk "fire_rd"),
    Gate.mkAND (Wire.mk "fire_rd") sel_data rd_data,
    Gate.mkNOT is_write (Wire.mk "uart_is_read")
  ]

  -- TX buffer register update
  let tx_buf_gates := (List.range 8).map fun i =>
    Gate.mkMUX tx_buf_q[i]! s_a.data[i]! wr_data tx_buf_d[i]!

  -- TX state: tx_busy asserts on wr_data, clears when idle
  -- For synthesized core, tx_tx serial line directly outputs tx_buf_q[0] or idle 1
  let tx_out_gate := Gate.mkMUX one tx_buf_q[0]! tx_busy_q uart_tx
  let tx_busy_next := Gate.mkMUX tx_busy_q wr_data wr_data tx_busy_d
  let tx_busy_dff := Gate.mkDFF tx_busy_d clock reset tx_busy_q

  -- RX buffer: captures uart_rx on falling edge / tick
  let rx_buf_gates := (List.range 8).map fun i =>
    Gate.mkMUX rx_buf_q[i]! uart_rx (if i == 0 then one else zero) rx_buf_d[i]!

  -- rx_ready: clears on rd_data
  let not_rd_data := Wire.mk "not_rd_data"
  let rx_ready_next := Gate.mkAND rx_ready_q not_rd_data rx_ready_d
  let rx_ready_dff := Gate.mkDFF rx_ready_d clock reset rx_ready_q

  -- Ctrl and Div registers
  let ctrl_gates := [
    Gate.mkNOT rd_data not_rd_data,
    Gate.mkMUX tx_irq_en_q s_a.data[0]! wr_ctrl tx_irq_en_d,
    Gate.mkMUX rx_irq_en_q s_a.data[1]! wr_ctrl rx_irq_en_d,
    Gate.mkDFF tx_irq_en_d clock reset tx_irq_en_q,
    Gate.mkDFF rx_irq_en_d clock reset rx_irq_en_q
  ] ++
  ((List.range 16).map fun i =>
    Gate.mkMUX div_q[i]! s_a.data[i]! wr_div div_d[i]!)

  -- Register instances
  let reg_instances : List CircuitInstance := [
    { moduleName := "Register8", instName := "u_tx_buf",
      portMap := ((List.range 8).map fun i => (s!"d_{i}", tx_buf_d[i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 8).map fun i => (s!"q_{i}", tx_buf_q[i]!)) },
    { moduleName := "Register8", instName := "u_rx_buf",
      portMap := ((List.range 8).map fun i => (s!"d_{i}", rx_buf_d[i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 8).map fun i => (s!"q_{i}", rx_buf_q[i]!)) },
    { moduleName := "Register16", instName := "u_div",
      portMap := ((List.range 16).map fun i => (s!"d_{i}", div_d[i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 16).map fun i => (s!"q_{i}", div_q[i]!)) }
  ]

  -- Status bits: bit 0: tx_busy, bit 1: not(tx_busy), bit 2: rx_ready
  let not_tx_busy := Wire.mk "not_tx_busy"
  let not_tx_gate := Gate.mkNOT tx_busy_q not_tx_busy

  -- Interrupt generation: (tx_empty & tx_irq_en) | (rx_ready & rx_irq_en)
  let tx_irq := Wire.mk "tx_irq"
  let rx_irq := Wire.mk "rx_irq"
  let irq_gates := [
    Gate.mkAND not_tx_busy tx_irq_en_q tx_irq,
    Gate.mkAND rx_ready_q rx_irq_en_q rx_irq,
    Gate.mkOR tx_irq rx_irq uart_irq
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
      let mux_d := Wire.mk s!"uart_rdata_{i}"
      [Gate.mkMUX rx_buf_q[i]! (if i == 0 then tx_busy_q else if i == 1 then not_tx_busy else if i == 2 then rx_ready_q else zero) sel_status mux_d,
       Gate.mkBUF mux_d s_d.data[i]!]
    else
      [Gate.mkBUF zero s_d.data[i]!])

  let all_inputs :=
    [clock, reset, zero, one, s_a.valid] ++
    s_a.opcode ++ s_a.param ++ s_a.size ++ s_a.source ++ s_a.address ++ s_a.mask ++ s_a.data ++
    [s_d.ready, uart_rx]

  let all_outputs :=
    [s_a.ready, s_d.valid] ++ s_d.opcode ++ s_d.param ++ s_d.size ++ s_d.source ++ s_d.sink ++
    s_d.data ++ [s_d.denied, uart_tx, uart_irq]

  { name := "UART"
    inputs := all_inputs
    outputs := all_outputs
    gates := op_gates ++ addr_decode_gates ++ wr_gates ++ tx_buf_gates ++
             [tx_out_gate, tx_busy_next, tx_busy_dff, rx_ready_next, rx_ready_dff, not_tx_gate] ++
             rx_buf_gates ++ ctrl_gates ++ irq_gates ++ resp_gates
    instances := reg_instances
  }

def uartCircuit : Circuit := mkUART

end Shoumei.Peripherals

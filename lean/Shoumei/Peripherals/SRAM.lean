/-
Peripherals/SRAM.lean - On-Chip Scratchpad SRAM with TileLink TL-UH Interface

Provides fast on-chip scratchpad RAM with byte-write enables for standalone execution.
Responds with AccessAck on writes and AccessAckData on reads.
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.Register
import Shoumei.Interconnect.TileLink.TLTypes

namespace Shoumei.Peripherals

open Shoumei
open Shoumei.Circuits.Sequential
open Shoumei.Interconnect.TileLink

/-- On-Chip Scratchpad SRAM circuit with TileLink TL-UH slave interface. -/
def mkSRAM : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero  := Wire.mk "zero"
  let one   := Wire.mk "one"

  -- TileLink Slave Ports
  let s_a := makeChannelAWires "sram"
  let s_d := makeChannelDWires "sram"

  -- Request handshake
  let req_fire := Wire.mk "sram_req_fire"
  let is_write := Wire.mk "sram_is_write"
  let is_get   := Wire.mk "sram_is_get"

  let op_gates := [
    Gate.mkNOT s_a.opcode[2]! is_write,
    Gate.mkBUF s_a.opcode[2]! is_get,
    Gate.mkAND s_a.valid (Wire.mk "not_resp_wait") req_fire
  ]

  -- 64-bit Scratchpad storage word
  let mem_q := (List.range 64).map fun i => Wire.mk s!"sram_q_{i}"
  let mem_d := (List.range 64).map fun i => Wire.mk s!"sram_d_{i}"

  -- Byte-masked write enables
  let byte_we := (List.range 8).map fun byte => Wire.mk s!"sram_bwe_{byte}"
  let bwe_gates := (List.range 8).map fun byte =>
    Gate.mkAND req_fire (Wire.mk s!"wr_mask_{byte}") byte_we[byte]!
  let mask_gates := (List.range 8).map fun byte =>
    Gate.mkAND is_write s_a.mask[byte]! (Wire.mk s!"wr_mask_{byte}")

  let data_mux_gates := (List.range 64).map fun i =>
    let byte := i / 8
    Gate.mkMUX mem_q[i]! s_a.data[i]! byte_we[byte]! mem_d[i]!

  let reg_instances : List CircuitInstance := [
    { moduleName := "Register32", instName := "u_sram_lo",
      portMap := ((List.range 32).map fun i => (s!"d_{i}", mem_d[i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 32).map fun i => (s!"q_{i}", mem_q[i]!)) },
    { moduleName := "Register32", instName := "u_sram_hi",
      portMap := ((List.range 32).map fun i => (s!"d_{i}", mem_d[32 + i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 32).map fun i => (s!"q_{i}", mem_q[32 + i]!)) }
  ]

  -- Response D channel (1-cycle read/write latency)
  let resp_valid_q := Wire.mk "resp_valid_q"
  let resp_valid_dff := Gate.mkDFF req_fire clock reset resp_valid_q
  let not_resp_wait_gate := Gate.mkNOT resp_valid_q (Wire.mk "not_resp_wait")

  let resp_gates := [
    resp_valid_dff, not_resp_wait_gate,
    Gate.mkBUF resp_valid_q s_d.valid,
    Gate.mkBUF one s_a.ready,
    Gate.mkBUF zero s_d.denied
  ] ++
  (List.range 3).map (fun i => Gate.mkBUF (if i == 0 then is_get else zero) s_d.opcode[i]!) ++
  (List.range 2).map (fun i => Gate.mkBUF zero s_d.param[i]!) ++
  (List.range 3).map (fun i => Gate.mkBUF zero s_d.size[i]!) ++
  (List.range 4).map (fun i => Gate.mkBUF zero s_d.source[i]!) ++
  (List.range 4).map (fun i => Gate.mkBUF zero s_d.sink[i]!) ++
  (List.range 64).map (fun i => Gate.mkBUF mem_q[i]! s_d.data[i]!)

  let all_inputs :=
    [clock, reset, zero, one, s_a.valid] ++
    s_a.opcode ++ s_a.param ++ s_a.size ++ s_a.source ++ s_a.address ++ s_a.mask ++ s_a.data ++
    [s_d.ready]

  let all_outputs :=
    [s_a.ready, s_d.valid] ++ s_d.opcode ++ s_d.param ++ s_d.size ++ s_d.source ++ s_d.sink ++
    s_d.data ++ [s_d.denied]

  { name := "SRAM"
    inputs := all_inputs
    outputs := all_outputs
    gates := op_gates ++ bwe_gates ++ mask_gates ++ data_mux_gates ++ resp_gates
    instances := reg_instances
  }

def sramCircuit : Circuit := mkSRAM

end Shoumei.Peripherals

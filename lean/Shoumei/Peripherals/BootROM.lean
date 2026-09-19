/-
Peripherals/BootROM.lean - On-Chip Bootloader ROM with TileLink TL-UH Interface

Read-only TileLink TL-UH slave containing the first-stage bootloader code.
Responds with AccessAckData on Channel D.
-/

import Shoumei.DSL
import Shoumei.Interconnect.TileLink.TLTypes

namespace Shoumei.Peripherals

open Shoumei
open Shoumei.Interconnect.TileLink

/-- On-Chip Bootloader ROM circuit with TileLink TL-UH slave interface. -/
def mkBootROM : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero  := Wire.mk "zero"
  let one   := Wire.mk "one"

  -- TileLink Slave Ports
  let s_a := makeChannelAWires "bootrom"
  let s_d := makeChannelDWires "bootrom"

  let req_fire := Wire.mk "brom_req_fire"
  let fire_gate := Gate.mkAND s_a.valid (Wire.mk "not_resp_wait") req_fire

  -- Response valid register (1-cycle read latency)
  let resp_valid_q := Wire.mk "resp_valid_q"
  let resp_valid_dff := Gate.mkDFF req_fire clock reset resp_valid_q
  let not_resp_wait_gate := Gate.mkNOT resp_valid_q (Wire.mk "not_resp_wait")

  -- Default bootloader payload:
  -- Minimal instructions: jump to SRAM 0x20000000
  -- lui a0, 0x20000; jr a0 (or nop loop)
  let rom_data := (List.range 64).map fun i =>
    -- Word 0: 0x20000537 (lui a0, 0x20000)
    -- Word 1: 0x00050067 (jr a0)
    if i == 0 || i == 1 || i == 2 || i == 4 || i == 6 || i == 8 || i == 29 then one
    else if i == 32 + 0 || i == 32 + 1 || i == 32 + 2 || i == 32 + 5 || i == 32 + 6 || i == 32 + 16 || i == 32 + 18 then one
    else zero

  let resp_gates := [
    fire_gate, resp_valid_dff, not_resp_wait_gate,
    Gate.mkBUF resp_valid_q s_d.valid,
    Gate.mkBUF one s_a.ready,
    Gate.mkBUF zero s_d.denied
  ] ++
  (List.range 3).map (fun i => Gate.mkBUF (if i == 0 then one else zero) s_d.opcode[i]!) ++ -- 3'b001 = AccessAckData
  (List.range 2).map (fun i => Gate.mkBUF zero s_d.param[i]!) ++
  (List.range 3).map (fun i => Gate.mkBUF zero s_d.size[i]!) ++
  (List.range 4).map (fun i => Gate.mkBUF zero s_d.source[i]!) ++
  (List.range 4).map (fun i => Gate.mkBUF zero s_d.sink[i]!) ++
  (List.range 64).map (fun i => Gate.mkBUF rom_data[i]! s_d.data[i]!)

  let all_inputs :=
    [clock, reset, zero, one, s_a.valid] ++
    s_a.opcode ++ s_a.param ++ s_a.size ++ s_a.source ++ s_a.address ++ s_a.mask ++ s_a.data ++
    [s_d.ready]

  let all_outputs :=
    [s_a.ready, s_d.valid] ++ s_d.opcode ++ s_d.param ++ s_d.size ++ s_d.source ++ s_d.sink ++
    s_d.data ++ [s_d.denied]

  { name := "BootROM"
    inputs := all_inputs
    outputs := all_outputs
    gates := resp_gates
    instances := []
  }

def bootROMCircuit : Circuit := mkBootROM

end Shoumei.Peripherals

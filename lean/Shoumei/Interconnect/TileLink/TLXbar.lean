/-
Interconnect/TileLink/TLXbar.lean - 1-to-N TileLink TL-UH Interconnect Crossbar

Decodes Channel A addresses and routes requests to 8 memory-mapped slave endpoints:
- Slave 0: Boot ROM       (0x0001_0000 .. 0x0001_1FFF, base 16'h0001)
- Slave 1: ACLINT MTIMER  (0x0200_0000 .. 0x0200_3FFF, base 16'h0200, sub 0)
- Slave 2: ACLINT MSWI    (0x0200_4000 .. 0x0200_7FFF, base 16'h0200, sub 1)
- Slave 3: ACLINT SSWI    (0x0200_8000 .. 0x0200_BFFF, base 16'h0200, sub 2)
- Slave 4: AIA APLIC      (0x0C00_0000 .. 0x0C3F_FFFF, base 16'h0C00)
- Slave 5: UART           (0x1000_0000 .. 0x1000_0FFF, base 16'h1000, sub 0)
- Slave 6: GPIO           (0x1000_1000 .. 0x1000_1FFF, base 16'h1000, sub 1)
- Slave 7: Scratchpad SRAM(0x2000_0000 .. 0x2003_FFFF, base 16'h2000)
-/

import Shoumei.DSL
import Shoumei.Interconnect.TileLink.TLTypes

namespace Shoumei.Interconnect.TileLink

open Shoumei

/-- TLXbar8: 1 Master to 8 Slaves TileLink Crossbar. -/
def mkTLXbar8 : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero  := Wire.mk "zero"
  let one   := Wire.mk "one"

  -- Master Channel A
  let m_a := makeChannelAWires "m"
  -- Master Channel D
  let m_d := makeChannelDWires "m"

  -- Slave select decode wires (one-hot)
  let sel := (List.range 8).map fun i => Wire.mk s!"sel_s{i}"

  -- Slaves 0 to 7 wires
  let s_a := (List.range 8).map fun i => makeChannelAWires s!"s{i}"
  let s_d := (List.range 8).map fun i => makeChannelDWires s!"s{i}"

  -- Address decode on address bits [31:12]
  -- S0 (Boot ROM): 0x0001_xxxx (addr[31:16] == 0x0001)
  -- S1 (MTIMER):   0x0200_0xxx..3xxx
  -- S2 (MSWI):     0x0200_4xxx..7xxx
  -- S3 (SSWI):     0x0200_8xxx..Bxxx
  -- S4 (APLIC):    0x0C00_xxxx
  -- S5 (UART):     0x1000_0xxx
  -- S6 (GPIO):     0x1000_1xxx
  -- S7 (SRAM):     0x2000_xxxx

  -- Match gates for prefix matching:
  -- We decode primary region from address[31:16]
  let is_0001 := Wire.mk "addr_is_0001"
  let is_0200 := Wire.mk "addr_is_0200"
  let is_0C00 := Wire.mk "addr_is_0C00"
  let is_1000 := Wire.mk "addr_is_1000"
  let is_2000 := Wire.mk "addr_is_2000"

  -- Decode gates for the 8 targets
  let decode_gates : List Gate := [
    -- S0: Boot ROM (0x0001)
    Gate.mkAND m_a.address[16]! (Wire.mk "not_a29") is_0001,
    Gate.mkBUF is_0001 sel[0]!,

    -- 0x0200 region (bit 25 is 1, bit 24 is 0)
    Gate.mkAND m_a.address[25]! (Wire.mk "not_a24") is_0200,
    -- S1 (MTIMER): 0x0200 with addr[14:13] == 00
    Gate.mkAND is_0200 (Wire.mk "not_a14") sel[1]!,
    -- S2 (MSWI): 0x0200 with addr[14] == 1, addr[15] == 0
    Gate.mkAND is_0200 m_a.address[14]! sel[2]!,
    -- S3 (SSWI): 0x0200 with addr[15] == 1
    Gate.mkAND is_0200 m_a.address[15]! sel[3]!,

    -- S4: APLIC (0x0C00: addr[27:26] == 11)
    Gate.mkAND m_a.address[27]! m_a.address[26]! is_0C00,
    Gate.mkBUF is_0C00 sel[4]!,

    -- 0x1000 region: addr[28] == 1
    Gate.mkAND m_a.address[28]! (Wire.mk "not_a29_b") is_1000,
    -- S5 (UART): addr[12] == 0
    Gate.mkAND is_1000 (Wire.mk "not_a12") sel[5]!,
    -- S6 (GPIO): addr[12] == 1
    Gate.mkAND is_1000 m_a.address[12]! sel[6]!,

    -- S7: SRAM (0x2000: addr[29] == 1)
    Gate.mkAND m_a.address[29]! (Wire.mk "not_a31") is_2000,
    Gate.mkBUF is_2000 sel[7]!,

    -- Helper not gates
    Gate.mkNOT m_a.address[29]! (Wire.mk "not_a29"),
    Gate.mkNOT m_a.address[29]! (Wire.mk "not_a29_b"),
    Gate.mkNOT m_a.address[24]! (Wire.mk "not_a24"),
    Gate.mkNOT m_a.address[14]! (Wire.mk "not_a14"),
    Gate.mkNOT m_a.address[12]! (Wire.mk "not_a12"),
    Gate.mkNOT m_a.address[31]! (Wire.mk "not_a31")
  ]

  -- Channel A routing:
  -- s_a[k].valid = m_a.valid & sel[k]
  -- Broadcast common payload signals from m_a to all s_a[k]
  let a_valid_gates := (List.range 8).map fun i =>
    Gate.mkAND m_a.valid sel[i]! s_a[i]!.valid

  let a_payload_gates := (List.range 8).flatMap fun k =>
    (List.range 3).map (fun i => Gate.mkBUF m_a.opcode[i]! s_a[k]!.opcode[i]!) ++
    (List.range 3).map (fun i => Gate.mkBUF m_a.param[i]! s_a[k]!.param[i]!) ++
    (List.range 3).map (fun i => Gate.mkBUF m_a.size[i]! s_a[k]!.size[i]!) ++
    (List.range 4).map (fun i => Gate.mkBUF m_a.source[i]! s_a[k]!.source[i]!) ++
    (List.range 32).map (fun i => Gate.mkBUF m_a.address[i]! s_a[k]!.address[i]!) ++
    (List.range 8).map (fun i => Gate.mkBUF m_a.mask[i]! s_a[k]!.mask[i]!) ++
    (List.range 64).map (fun i => Gate.mkBUF m_a.data[i]! s_a[k]!.data[i]!)

  -- Master ready routing: m_a.ready = OR(sel[k] & s_a[k].ready)
  let s_ready_gated := (List.range 8).map fun i => Wire.mk s!"s_rdy_g{i}"
  let rdy_gate_gates := (List.range 8).map fun i =>
    Gate.mkAND sel[i]! s_a[i]!.ready s_ready_gated[i]!

  let rdy_tree := (List.range 7).map fun i => Wire.mk s!"rdy_tree_{i}"
  let rdy_tree_gates : List Gate := [
    Gate.mkOR s_ready_gated[0]! s_ready_gated[1]! rdy_tree[0]!,
    Gate.mkOR s_ready_gated[2]! s_ready_gated[3]! rdy_tree[1]!,
    Gate.mkOR s_ready_gated[4]! s_ready_gated[5]! rdy_tree[2]!,
    Gate.mkOR s_ready_gated[6]! s_ready_gated[7]! rdy_tree[3]!,
    Gate.mkOR rdy_tree[0]! rdy_tree[1]! rdy_tree[4]!,
    Gate.mkOR rdy_tree[2]! rdy_tree[3]! rdy_tree[5]!,
    Gate.mkOR rdy_tree[4]! rdy_tree[5]! m_a.ready
  ]

  -- Channel D response routing:
  -- m_d.valid = OR(s_d[k].valid)
  -- Data is OR'd/muxed by active slave response
  let d_valid_tree := (List.range 7).map fun i => Wire.mk s!"d_val_tree_{i}"
  let d_valid_gates : List Gate := [
    Gate.mkOR s_d[0]!.valid s_d[1]!.valid d_valid_tree[0]!,
    Gate.mkOR s_d[2]!.valid s_d[3]!.valid d_valid_tree[1]!,
    Gate.mkOR s_d[4]!.valid s_d[5]!.valid d_valid_tree[2]!,
    Gate.mkOR s_d[6]!.valid s_d[7]!.valid d_valid_tree[3]!,
    Gate.mkOR d_valid_tree[0]! d_valid_tree[1]! d_valid_tree[4]!,
    Gate.mkOR d_valid_tree[2]! d_valid_tree[3]! d_valid_tree[5]!,
    Gate.mkOR d_valid_tree[4]! d_valid_tree[5]! m_d.valid
  ]

  -- Master ready broadcast to slaves
  let d_ready_gates := (List.range 8).map fun i =>
    Gate.mkBUF m_d.ready s_d[i]!.ready

  -- Data bus MUX for Channel D (OR of gated data since non-responding slaves output 0)
  let d_data_gates := (List.range 64).flatMap fun bit =>
    let bit_wires := (List.range 7).map fun i => Wire.mk s!"d_data_b{bit}_t{i}"
    [Gate.mkOR s_d[0]!.data[bit]! s_d[1]!.data[bit]! bit_wires[0]!,
     Gate.mkOR s_d[2]!.data[bit]! s_d[3]!.data[bit]! bit_wires[1]!,
     Gate.mkOR s_d[4]!.data[bit]! s_d[5]!.data[bit]! bit_wires[2]!,
     Gate.mkOR s_d[6]!.data[bit]! s_d[7]!.data[bit]! bit_wires[3]!,
     Gate.mkOR bit_wires[0]! bit_wires[1]! bit_wires[4]!,
     Gate.mkOR bit_wires[2]! bit_wires[3]! bit_wires[5]!,
     Gate.mkOR bit_wires[4]! bit_wires[5]! m_d.data[bit]!]

  -- Opcode and size MUX for Channel D
  let d_opcode_gates := (List.range 3).flatMap fun bit =>
    let bit_wires := (List.range 7).map fun i => Wire.mk s!"d_op_b{bit}_t{i}"
    [Gate.mkOR s_d[0]!.opcode[bit]! s_d[1]!.opcode[bit]! bit_wires[0]!,
     Gate.mkOR s_d[2]!.opcode[bit]! s_d[3]!.opcode[bit]! bit_wires[1]!,
     Gate.mkOR s_d[4]!.opcode[bit]! s_d[5]!.opcode[bit]! bit_wires[2]!,
     Gate.mkOR s_d[6]!.opcode[bit]! s_d[7]!.opcode[bit]! bit_wires[3]!,
     Gate.mkOR bit_wires[0]! bit_wires[1]! bit_wires[4]!,
     Gate.mkOR bit_wires[2]! bit_wires[3]! bit_wires[5]!,
     Gate.mkOR bit_wires[4]! bit_wires[5]! m_d.opcode[bit]!]

  let d_param_gates := (List.range 2).map fun i => Gate.mkBUF zero m_d.param[i]!
  let d_size_gates := (List.range 3).map fun i => Gate.mkBUF zero m_d.size[i]!
  let d_source_gates := (List.range 4).map fun i => Gate.mkBUF zero m_d.source[i]!
  let d_sink_gates := (List.range 4).map fun i => Gate.mkBUF zero m_d.sink[i]!
  let d_denied_gate := Gate.mkBUF zero m_d.denied

  let all_inputs :=
    [clock, reset, zero, one, m_a.valid] ++
    m_a.opcode ++ m_a.param ++ m_a.size ++ m_a.source ++ m_a.address ++ m_a.mask ++ m_a.data ++
    [m_d.ready] ++
    (List.range 8).flatMap (fun k =>
      [s_a[k]!.ready, s_d[k]!.valid] ++ s_d[k]!.opcode ++ s_d[k]!.data)

  let all_outputs :=
    [m_a.ready, m_d.valid] ++ m_d.opcode ++ m_d.param ++ m_d.size ++ m_d.source ++ m_d.sink ++
    m_d.data ++ [m_d.denied] ++
    (List.range 8).flatMap (fun k =>
      [s_a[k]!.valid] ++ s_a[k]!.opcode ++ s_a[k]!.param ++ s_a[k]!.size ++ s_a[k]!.source ++
      s_a[k]!.address ++ s_a[k]!.mask ++ s_a[k]!.data ++ [s_d[k]!.ready])

  { name := "TLXbar8"
    inputs := all_inputs
    outputs := all_outputs
    gates := decode_gates ++ a_valid_gates ++ a_payload_gates ++ rdy_gate_gates ++
             rdy_tree_gates ++ d_valid_gates ++ d_ready_gates ++ d_data_gates ++
             d_opcode_gates ++ d_param_gates ++ d_size_gates ++ d_source_gates ++
             d_sink_gates ++ [d_denied_gate]
    instances := []
  }

def tlXbar8Circuit : Circuit := mkTLXbar8

end Shoumei.Interconnect.TileLink

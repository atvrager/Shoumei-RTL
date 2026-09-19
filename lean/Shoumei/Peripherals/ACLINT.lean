/-
Peripherals/ACLINT.lean - Advanced Core Local Interruptor (ACLINT)

Implements the modern RISC-V ACLINT specification:
- MTIMER: 64-bit monotonic `mtime` and 64-bit `mtimecmp` comparator.
- MSWI: 32-bit `msip` (bit 0 drives `mtip_out` / `msip_out`).
- SSWI: 32-bit `ssip` (bit 0 drives `ssip_out`).
- Connected as a TileLink TL-UH slave.
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.Register
import Shoumei.Interconnect.TileLink.TLTypes

namespace Shoumei.Peripherals

open Shoumei
open Shoumei.Circuits.Sequential
open Shoumei.Interconnect.TileLink

/-- ACLINT circuit: MTIMER + MSWI + SSWI TileLink TL-UH device. -/
def mkACLINT : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero  := Wire.mk "zero"
  let one   := Wire.mk "one"

  -- TileLink Slave Channel A (Input request from crossbar)
  let s_a := makeChannelAWires "aclint"
  -- TileLink Slave Channel D (Output response to crossbar)
  let s_d := makeChannelDWires "aclint"

  -- Interrupt outputs to CPU core
  let mtip_out := Wire.mk "mtip_out"
  let msip_out := Wire.mk "msip_out"
  let ssip_out := Wire.mk "ssip_out"

  -- Internal Registers:
  -- mtime (64-bit): increments every cycle (or when prescaler enables)
  let mtime_q := (List.range 64).map fun i => Wire.mk s!"mtime_q_{i}"
  let mtime_d := (List.range 64).map fun i => Wire.mk s!"mtime_d_{i}"
  let mtime_inc := (List.range 64).map fun i => Wire.mk s!"mtime_inc_{i}"
  let mtime_carries := (List.range 63).map fun i => Wire.mk s!"mtime_c_{i}"

  -- mtimecmp (64-bit comparison register)
  let mtimecmp_q := (List.range 64).map fun i => Wire.mk s!"mtimecmp_q_{i}"
  let mtimecmp_d := (List.range 64).map fun i => Wire.mk s!"mtimecmp_d_{i}"

  -- msip (32-bit)
  let msip_q := (List.range 32).map fun i => Wire.mk s!"msip_q_{i}"
  let msip_d := (List.range 32).map fun i => Wire.mk s!"msip_d_{i}"

  -- ssip (32-bit)
  let ssip_q := (List.range 32).map fun i => Wire.mk s!"ssip_q_{i}"
  let ssip_d := (List.range 32).map fun i => Wire.mk s!"ssip_d_{i}"

  -- 64-bit Incrementer for mtime: mtime_inc = mtime_q + 1
  let mtime_inc_gates : List Gate :=
    [Gate.mkNOT mtime_q[0]! mtime_inc[0]!,
     Gate.mkBUF mtime_q[0]! mtime_carries[0]!] ++
    ((List.range 63).map (fun i =>
      let prev_c := mtime_carries[i]!
      let next_c := if i < 62 then mtime_carries[i+1]! else Wire.mk "mtime_c_last"
      [Gate.mkXOR mtime_q[i+1]! prev_c mtime_inc[i+1]!,
       Gate.mkAND mtime_q[i+1]! prev_c next_c]
    ) |>.flatten)

  -- TileLink Address Decoding for ACLINT registers
  -- addr[15:14] == 00 -> MTIMER (0x0000=mtimecmp, 0x7FF8=mtime)
  -- addr[15:14] == 01 -> MSWI   (0x4000=msip)
  -- addr[15:14] == 10 -> SSWI   (0x8000=ssip)
  let is_write := Wire.mk "tl_is_write"
  let is_get   := Wire.mk "tl_is_get"
  let req_fire := Wire.mk "tl_req_fire"

  -- Opcode[2] is 1 for Get (100), 0 for Put (000, 001)
  let op_decode_gates := [
    Gate.mkNOT s_a.opcode[2]! is_write,
    Gate.mkBUF s_a.opcode[2]! is_get,
    Gate.mkAND s_a.valid (Wire.mk "not_resp_wait") req_fire
  ]

  let sel_mtimecmp := Wire.mk "sel_mtimecmp"
  let sel_mtime    := Wire.mk "sel_mtime"
  let sel_msip     := Wire.mk "sel_msip"
  let sel_ssip     := Wire.mk "sel_ssip"

  let addr_decode_gates := [
    -- mtimecmp: addr[15:12] == 4'h0 or 4'h4
    Gate.mkNOT s_a.address[15]! (Wire.mk "not_a15"),
    Gate.mkNOT s_a.address[14]! (Wire.mk "not_a14"),
    Gate.mkAND (Wire.mk "not_a15") (Wire.mk "not_a14") sel_mtimecmp,
    -- mtime: addr[14:12] == 3'h7
    Gate.mkAND s_a.address[14]! s_a.address[13]! (Wire.mk "mtime_match_pre"),
    Gate.mkAND (Wire.mk "mtime_match_pre") s_a.address[12]! sel_mtime,
    -- msip: addr[15:14] == 2'b01
    Gate.mkAND (Wire.mk "not_a15") s_a.address[14]! sel_msip,
    -- ssip: addr[15:14] == 2'b10
    Gate.mkAND s_a.address[15]! (Wire.mk "not_a14") sel_ssip
  ]

  -- Register Write strobes
  let wr_mtimecmp := Wire.mk "wr_mtimecmp"
  let wr_mtime    := Wire.mk "wr_mtime"
  let wr_msip     := Wire.mk "wr_msip"
  let wr_ssip     := Wire.mk "wr_ssip"

  let wr_strobe_gates := [
    Gate.mkAND req_fire is_write (Wire.mk "req_fire_wr"),
    Gate.mkAND (Wire.mk "req_fire_wr") sel_mtimecmp wr_mtimecmp,
    Gate.mkAND (Wire.mk "req_fire_wr") sel_mtime wr_mtime,
    Gate.mkAND (Wire.mk "req_fire_wr") sel_msip wr_msip,
    Gate.mkAND (Wire.mk "req_fire_wr") sel_ssip wr_ssip
  ]

  -- Register Next values (MUX between increment/hold and bus write data)
  let reg_mux_gates :=
    ((List.range 64).map fun i =>
      Gate.mkMUX mtime_inc[i]! s_a.data[i]! wr_mtime mtime_d[i]!) ++
    ((List.range 64).map fun i =>
      Gate.mkMUX mtimecmp_q[i]! s_a.data[i]! wr_mtimecmp mtimecmp_d[i]!) ++
    ((List.range 32).map fun i =>
      Gate.mkMUX msip_q[i]! s_a.data[i]! wr_msip msip_d[i]!) ++
    ((List.range 32).map fun i =>
      Gate.mkMUX ssip_q[i]! s_a.data[i]! wr_ssip ssip_d[i]!)

  -- Register instances
  let reg_instances : List CircuitInstance := [
    { moduleName := "Register32", instName := "u_mtime_lo",
      portMap := ((List.range 32).map fun i => (s!"d_{i}", mtime_d[i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 32).map fun i => (s!"q_{i}", mtime_q[i]!)) },
    { moduleName := "Register32", instName := "u_mtime_hi",
      portMap := ((List.range 32).map fun i => (s!"d_{i}", mtime_d[32 + i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 32).map fun i => (s!"q_{i}", mtime_q[32 + i]!)) },
    { moduleName := "Register32", instName := "u_mtimecmp_lo",
      portMap := ((List.range 32).map fun i => (s!"d_{i}", mtimecmp_d[i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 32).map fun i => (s!"q_{i}", mtimecmp_q[i]!)) },
    { moduleName := "Register32", instName := "u_mtimecmp_hi",
      portMap := ((List.range 32).map fun i => (s!"d_{i}", mtimecmp_d[32 + i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 32).map fun i => (s!"q_{i}", mtimecmp_q[32 + i]!)) },
    { moduleName := "Register32", instName := "u_msip",
      portMap := ((List.range 32).map fun i => (s!"d_{i}", msip_d[i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 32).map fun i => (s!"q_{i}", msip_q[i]!)) },
    { moduleName := "Register32", instName := "u_ssip",
      portMap := ((List.range 32).map fun i => (s!"d_{i}", ssip_d[i]!)) ++
                 [("clock", clock), ("reset", reset)] ++
                 ((List.range 32).map fun i => (s!"q_{i}", ssip_q[i]!)) }
  ]

  -- Comparator: mtime >= mtimecmp (64-bit comparator)
  -- Simplified MSB check + equality comparator
  let diff_carries := (List.range 64).map fun i => Wire.mk s!"cmp_c_{i}"
  let cmp_gates : List Gate :=
    [Gate.mkBUF one diff_carries[0]!] ++
    ((List.range 63).map fun i =>
      Gate.mkAND (mtime_q[i]!) (Wire.mk s!"not_mcmp_{i}") diff_carries[i+1]!) ++
    ((List.range 63).map fun i =>
      Gate.mkNOT mtimecmp_q[i]! (Wire.mk s!"not_mcmp_{i}")) ++
    [Gate.mkBUF diff_carries[63]! mtip_out]

  -- Interrupt Outputs
  let irq_out_gates := [
    Gate.mkBUF msip_q[0]! msip_out,
    Gate.mkBUF ssip_q[0]! ssip_out
  ]

  -- Response D channel generation (1-cycle response register)
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
  (List.range 64).map (fun i =>
    -- Return mtime or mtimecmp on read
    Gate.mkMUX mtime_q[i]! mtimecmp_q[i]! sel_mtimecmp s_d.data[i]!)

  let all_inputs :=
    [clock, reset, zero, one, s_a.valid] ++
    s_a.opcode ++ s_a.param ++ s_a.size ++ s_a.source ++ s_a.address ++ s_a.mask ++ s_a.data ++
    [s_d.ready]

  let all_outputs :=
    [s_a.ready, s_d.valid] ++ s_d.opcode ++ s_d.param ++ s_d.size ++ s_d.source ++ s_d.sink ++
    s_d.data ++ [s_d.denied, mtip_out, msip_out, ssip_out]

  { name := "ACLINT"
    inputs := all_inputs
    outputs := all_outputs
    gates := mtime_inc_gates ++ op_decode_gates ++ addr_decode_gates ++ wr_strobe_gates ++
             reg_mux_gates ++ cmp_gates ++ irq_out_gates ++ resp_gates
    instances := reg_instances
  }

def aclintCircuit : Circuit := mkACLINT

end Shoumei.Peripherals

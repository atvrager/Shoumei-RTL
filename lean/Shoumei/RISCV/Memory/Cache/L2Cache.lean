/-
RISCV/Memory/Cache/L2Cache.lean - Shared L2 Cache

2-way set-associative, 8-set, 32B line, shared between L1I and L1D.
Behavioral model + structural circuit.

D-side requests have priority over I-side.
On L2 miss: sends request to main memory.
-/

import Shoumei.DSL
import Shoumei.RISCV.Memory.Cache.CacheTypes
import Shoumei.Circuits.Sequential.Register
import Shoumei.Circuits.Combinational.Comparator
import Shoumei.Circuits.Combinational.MuxTree

namespace Shoumei.RISCV.Memory.Cache

open Shoumei
open Shoumei.Circuits.Sequential
open Shoumei.Circuits.Combinational

/-! ## Behavioral Model -/

/-- L2 Cache State: 2-way, 8-set, shared. -/
structure L2CacheState where
  /-- Cache lines: ways[way][set] -/
  ways : Fin 2 → Fin 8 → CacheLine 24
  /-- LRU bit per set -/
  lru : Fin 8 → Bool
  /-- FSM state -/
  fsm : L2CacheFSM
  /-- Which L1 initiated the current request -/
  source : CacheSource
  /-- Pending address -/
  pendingAddr : UInt32
  /-- Writeback buffer for dirty eviction to main memory -/
  writebackBuf : Fin 8 → UInt32
  /-- Writeback address -/
  writebackAddr : UInt32

instance : Inhabited L2CacheState where
  default := {
    ways := fun _ _ => CacheLine.empty
    lru := fun _ => false
    fsm := .IDLE
    source := .ICache
    pendingAddr := 0
    writebackBuf := fun _ => 0
    writebackAddr := 0
  }

def L2CacheState.empty : L2CacheState := default

def L2CacheState.victimWay (s : L2CacheState) (set : Fin 8) : Fin 2 :=
  if s.lru set then 1 else 0

/-- Lookup in L2. Returns `some (way, lineData)` on hit. -/
def L2CacheState.lookup (s : L2CacheState) (addr : UInt32) : Option (Fin 2 × (Fin 8 → UInt32)) :=
  let idx := extractL2Index addr
  let tag := extractL2Tag addr
  let line0 := s.ways 0 idx
  if line0.valid && line0.tag == tag then
    some (0, line0.data)
  else
    let line1 := s.ways 1 idx
    if line1.valid && line1.tag == tag then
      some (1, line1.data)
    else
      none

/-- Install a cache line in L2 after main memory refill. -/
def L2CacheState.refill (s : L2CacheState) (addr : UInt32)
    (lineData : Fin 8 → UInt32) : L2CacheState :=
  let idx := extractL2Index addr
  let tag := extractL2Tag addr
  let victim := s.victimWay idx
  { s with
    ways := fun w i =>
      if w == victim && i == idx then
        { valid := true, dirty := false, tag := tag, data := lineData }
      else
        s.ways w i
    lru := fun i =>
      if i == idx then (victim == 0)
      else s.lru i
  }

/-- Write back a dirty line from L1D to L2. Updates the line if present, allocates if not. -/
def L2CacheState.writeBack (s : L2CacheState) (addr : UInt32)
    (lineData : Fin 8 → UInt32) : L2CacheState :=
  let idx := extractL2Index addr
  let tag := extractL2Tag addr
  -- Check if line exists in L2
  match s.lookup addr with
  | some (way, _) =>
    -- Update existing line
    { s with
      ways := fun w i =>
        if w == way && i == idx then
          { valid := true, dirty := true, tag := tag, data := lineData }
        else
          s.ways w i
    }
  | none =>
    -- Allocate into victim way
    let victim := s.victimWay idx
    { s with
      ways := fun w i =>
        if w == victim && i == idx then
          { valid := true, dirty := true, tag := tag, data := lineData }
        else
          s.ways w i
      lru := fun i =>
        if i == idx then (victim == 0)
        else s.lru i
    }

/-! ## Structural Circuit -/

/-- Build the L2 Cache structural circuit.

    Ports:
    - Inputs: clock, reset,
              l1i_req_valid, l1i_req_addr[31:0],
              l1d_req_valid, l1d_req_addr[31:0], l1d_req_we, l1d_req_data[255:0],
              mem_resp_valid, mem_resp_data[255:0]
    - Outputs: l1i_resp_valid, l1i_resp_data[255:0],
               l1d_resp_valid, l1d_resp_data[255:0],
               mem_req_valid, mem_req_addr[31:0], mem_req_we, mem_req_data[255:0],
               stall_i, stall_d
-/
def mkL2Cache : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"

  -- L1I interface
  let l1i_req_valid := Wire.mk "l1i_req_valid"
  let l1i_req_addr := (List.range 32).map fun i => Wire.mk s!"l1i_req_addr_{i}"
  let l1i_resp_valid := Wire.mk "l1i_resp_valid"
  let l1i_resp_data := (List.range 256).map fun i => Wire.mk s!"l1i_resp_data_{i}"

  -- L1D interface
  let l1d_req_valid := Wire.mk "l1d_req_valid"
  let l1d_req_addr := (List.range 32).map fun i => Wire.mk s!"l1d_req_addr_{i}"
  let l1d_req_we := Wire.mk "l1d_req_we"
  let l1d_req_data := (List.range 256).map fun i => Wire.mk s!"l1d_req_data_{i}"
  let l1d_resp_valid := Wire.mk "l1d_resp_valid"
  let l1d_resp_data := (List.range 256).map fun i => Wire.mk s!"l1d_resp_data_{i}"

  -- Main memory interface
  let mem_resp_valid := Wire.mk "mem_resp_valid"
  let mem_resp_data := (List.range 256).map fun i => Wire.mk s!"mem_resp_data_{i}"
  let mem_req_valid := Wire.mk "mem_req_valid"
  let mem_req_addr := (List.range 32).map fun i => Wire.mk s!"mem_req_addr_{i}"
  let mem_req_we := Wire.mk "mem_req_we"
  let mem_req_data := (List.range 256).map fun i => Wire.mk s!"mem_req_data_{i}"

  let stall_i := Wire.mk "stall_i"
  let stall_d := Wire.mk "stall_d"

  -- FSM: 3-bit state register
  let fsm_d := (List.range 3).map fun i => Wire.mk s!"l2_fsm_d_{i}"
  let fsm_q := (List.range 3).map fun i => Wire.mk s!"l2_fsm_q_{i}"
  let fsm_gates := (List.range 3).map fun i =>
    Gate.mkDFF fsm_d[i]! clock reset fsm_q[i]!

  -- Source register (1 bit: 0=ICache, 1=DCache)
  let src_d := Wire.mk "src_d"
  let src_q := Wire.mk "src_q"
  let src_gate := Gate.mkDFF src_d clock reset src_q

  -- Tag storage: 2 ways × 8 sets × 24 bits
  let tag_instances := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 8).map (fun set =>
      CircuitInstance.mk "Register24" s!"u_l2_tag_w{way}_s{set}"
        ((List.range 24).map (fun b => (s!"d_{b}", Wire.mk s!"l2_tag_d_w{way}_s{set}_{b}")) ++
         [("clock", clock), ("reset", reset)] ++
         (List.range 24).map (fun b => (s!"q_{b}", Wire.mk s!"l2_tag_q_w{way}_s{set}_{b}"))))
  ) []

  -- Valid/dirty/LRU bits
  let valid_d := (List.range 16).map fun i => Wire.mk s!"l2_valid_d_{i}"
  let valid_q := (List.range 16).map fun i => Wire.mk s!"l2_valid_q_{i}"
  let valid_dffs := (List.range 16).map fun i =>
    Gate.mkDFF valid_d[i]! clock reset valid_q[i]!

  let lru_d := (List.range 8).map fun i => Wire.mk s!"l2_lru_d_{i}"
  let lru_q := (List.range 8).map fun i => Wire.mk s!"l2_lru_q_{i}"
  let lru_dffs := (List.range 8).map fun i =>
    Gate.mkDFF lru_d[i]! clock reset lru_q[i]!

  -- Data storage: 2 ways × 8 sets × 256 bits
  let data_instances := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 8).map (fun set =>
      CircuitInstance.mk "Register256" s!"u_l2_data_w{way}_s{set}"
        ((List.range 256).map (fun b => (s!"d_{b}", Wire.mk s!"l2_data_d_w{way}_s{set}_{b}")) ++
         [("clock", clock), ("reset", reset)] ++
         (List.range 256).map (fun b => (s!"q_{b}", Wire.mk s!"l2_data_q_w{way}_s{set}_{b}"))))
  ) []

  -- Arbiter: D-side priority
  -- arb_valid = l1d_req_valid OR l1i_req_valid
  -- arb_sel_d = l1d_req_valid (D-side wins when both request)
  let arb_sel_d := Wire.mk "arb_sel_d"
  let arb_gates := [Gate.mkBUF l1d_req_valid arb_sel_d]

  -- Const zero for placeholder outputs
  let const_zero_gates := [
    Gate.mkNOT reset (Wire.mk "l2_not_reset"),
    Gate.mkAND reset (Wire.mk "l2_not_reset") (Wire.mk "l2_const_zero")
  ]

  -- Simplified: placeholder for complex FSM-driven output logic
  -- In full implementation, this would include tag comparison, hit detection,
  -- and FSM state transitions
  let placeholder_outputs :=
    [Gate.mkBUF (Wire.mk "l2_const_zero") l1i_resp_valid] ++
    (l1i_resp_data.map fun w => Gate.mkBUF (Wire.mk "l2_const_zero") w) ++
    [Gate.mkBUF (Wire.mk "l2_const_zero") l1d_resp_valid] ++
    (l1d_resp_data.map fun w => Gate.mkBUF (Wire.mk "l2_const_zero") w) ++
    [Gate.mkBUF (Wire.mk "l2_const_zero") mem_req_valid] ++
    (mem_req_addr.map fun w => Gate.mkBUF (Wire.mk "l2_const_zero") w) ++
    [Gate.mkBUF (Wire.mk "l2_const_zero") mem_req_we] ++
    (mem_req_data.map fun w => Gate.mkBUF (Wire.mk "l2_const_zero") w) ++
    [Gate.mkBUF (Wire.mk "l2_const_zero") stall_i,
     Gate.mkBUF (Wire.mk "l2_const_zero") stall_d]

  -- Hold registers (simplified)
  let fsm_hold := (List.range 3).map fun i =>
    Gate.mkBUF (Wire.mk "l2_const_zero") fsm_d[i]!
  let src_hold := Gate.mkBUF src_q src_d
  let valid_hold := (List.range 16).map fun i => Gate.mkBUF valid_q[i]! valid_d[i]!
  let lru_hold := (List.range 8).map fun i => Gate.mkBUF lru_q[i]! lru_d[i]!

  let tag_hold := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 8).foldl (fun acc2 set =>
      acc2 ++ (List.range 24).map (fun b =>
        Gate.mkBUF (Wire.mk s!"l2_tag_q_w{way}_s{set}_{b}") (Wire.mk s!"l2_tag_d_w{way}_s{set}_{b}"))
    ) []
  ) []

  let data_hold := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 8).foldl (fun acc2 set =>
      acc2 ++ (List.range 256).map (fun b =>
        Gate.mkBUF (Wire.mk s!"l2_data_q_w{way}_s{set}_{b}") (Wire.mk s!"l2_data_d_w{way}_s{set}_{b}"))
    ) []
  ) []

  { name := "L2Cache"
    inputs := [clock, reset, l1i_req_valid] ++ l1i_req_addr ++
              [l1d_req_valid] ++ l1d_req_addr ++ [l1d_req_we] ++ l1d_req_data ++
              [mem_resp_valid] ++ mem_resp_data
    outputs := [l1i_resp_valid] ++ l1i_resp_data ++
               [l1d_resp_valid] ++ l1d_resp_data ++
               [mem_req_valid] ++ mem_req_addr ++ [mem_req_we] ++ mem_req_data ++
               [stall_i, stall_d]
    gates := fsm_gates ++ [src_gate] ++ valid_dffs ++ lru_dffs ++
             arb_gates ++ const_zero_gates ++ placeholder_outputs ++
             fsm_hold ++ [src_hold] ++ valid_hold ++ lru_hold ++
             tag_hold ++ data_hold
    instances := tag_instances ++ data_instances
    signalGroups := [
      { name := "l1i_req_addr", width := 32, wires := l1i_req_addr },
      { name := "l1d_req_addr", width := 32, wires := l1d_req_addr },
      { name := "l1d_req_data", width := 256, wires := l1d_req_data },
      { name := "l1i_resp_data", width := 256, wires := l1i_resp_data },
      { name := "l1d_resp_data", width := 256, wires := l1d_resp_data },
      { name := "mem_resp_data", width := 256, wires := mem_resp_data },
      { name := "mem_req_addr", width := 32, wires := mem_req_addr },
      { name := "mem_req_data", width := 256, wires := mem_req_data }
    ]
  }

end Shoumei.RISCV.Memory.Cache

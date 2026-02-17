/-
RISCV/Memory/Cache/L1DCache.lean - L1 Data Cache

2-way set-associative, 4-set, 32B line, write-back data cache.
Behavioral model + structural circuit.

Operations:
- Read hit: return word in 1 cycle
- Write hit: update word, set dirty
- Read/Write miss: evict victim (writeback if dirty), then refill from L2
- FENCE.I: write back all dirty lines to L2
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

/-- L1 Data Cache State: 2-way, 4-set. -/
structure L1DCacheState where
  /-- Cache lines: ways[way][set] -/
  ways : Fin 2 → Fin 4 → CacheLine 25
  /-- LRU bit per set: false = evict way 0, true = evict way 1 -/
  lru : Fin 4 → Bool
  /-- FSM state -/
  fsm : L1DCacheFSM
  /-- Pending address for in-flight miss -/
  pendingAddr : UInt32
  /-- Writeback buffer (line being written back) -/
  writebackBuf : Fin 8 → UInt32
  /-- Writeback address (line address being written back) -/
  writebackAddr : UInt32
  /-- FENCE.I: current set being scanned for dirty lines -/
  fenceISet : Fin 4
  /-- FENCE.I: current way being scanned -/
  fenceIWay : Fin 2

instance : Inhabited L1DCacheState where
  default := {
    ways := fun _ _ => CacheLine.empty
    lru := fun _ => false
    fsm := .IDLE
    pendingAddr := 0
    writebackBuf := fun _ => 0
    writebackAddr := 0
    fenceISet := 0
    fenceIWay := 0
  }

def L1DCacheState.empty : L1DCacheState := default

/-- Determine which way is the victim for eviction in a given set. -/
def L1DCacheState.victimWay (s : L1DCacheState) (set : Fin 4) : Fin 2 :=
  if s.lru set then 1 else 0

/-- Lookup an address in the L1D cache. Returns `some (way, word)` on hit. -/
def L1DCacheState.lookup (s : L1DCacheState) (addr : UInt32) : Option (Fin 2 × UInt32) :=
  let idx := extractL1DIndex addr
  let tag := extractL1DTag addr
  let wordOff := extractWordOffset addr
  -- Check way 0
  let line0 := s.ways 0 idx
  if line0.valid && line0.tag == tag then
    some (0, line0.data wordOff)
  else
    -- Check way 1
    let line1 := s.ways 1 idx
    if line1.valid && line1.tag == tag then
      some (1, line1.data wordOff)
    else
      none

/-- Simple lookup returning just the data word. -/
def L1DCacheState.lookupData (s : L1DCacheState) (addr : UInt32) : Option UInt32 :=
  (s.lookup addr).map (·.2)

/-- Write a word to a specific way/set, setting the dirty bit. -/
def L1DCacheState.writeToWay (s : L1DCacheState) (way : Fin 2) (addr : UInt32) (val : UInt32)
    : L1DCacheState :=
  let idx := extractL1DIndex addr
  let wordOff := extractWordOffset addr
  { s with
    ways := fun w i =>
      if w == way && i == idx then
        let line := s.ways w i
        { line with
          dirty := true
          data := fun j => if j == wordOff then val else line.data j }
      else
        s.ways w i
    -- Update LRU: mark the OTHER way as victim (we just used 'way')
    lru := fun i =>
      if i == idx then (way == 0)  -- if we used way 0, evict way 1 next; vice versa
      else s.lru i
  }

/-- Write on hit: find the hitting way and write. -/
def L1DCacheState.write (s : L1DCacheState) (addr : UInt32) (val : UInt32)
    : Option L1DCacheState :=
  match s.lookup addr with
  | some (way, _) => some (s.writeToWay way addr val)
  | none => none

/-- Install a complete cache line after refill. Installs into the victim way. -/
def L1DCacheState.refill (s : L1DCacheState) (addr : UInt32)
    (lineData : Fin 8 → UInt32) : L1DCacheState :=
  let idx := extractL1DIndex addr
  let tag := extractL1DTag addr
  let victim := s.victimWay idx
  { s with
    ways := fun w i =>
      if w == victim && i == idx then
        { valid := true, dirty := false, tag := tag, data := lineData }
      else
        s.ways w i
    -- Update LRU: victim way was just filled, mark other way as next victim
    lru := fun i =>
      if i == idx then (victim == 0)
      else s.lru i
  }

/-- Get the eviction data for a set's victim way. -/
def L1DCacheState.getEvictionData (s : L1DCacheState) (set : Fin 4)
    : CacheLine 25 :=
  let victim := s.victimWay set
  s.ways victim set

/-- Write back all dirty lines (for FENCE.I). Returns list of (addr, lineData) pairs. -/
def L1DCacheState.getAllDirtyLines (s : L1DCacheState)
    : List (UInt32 × (Fin 8 → UInt32)) :=
  let ways : List (Fin 2) := [0, 1]
  let sets : List (Fin 4) := [0, 1, 2, 3]
  ways.foldl (fun acc way =>
    sets.foldl (fun acc2 setIdx =>
      let line := s.ways way setIdx
      if line.valid && line.dirty then
        let addr := reconstructL1DAddr line.tag setIdx
        acc2 ++ [(addr, line.data)]
      else acc2
    ) acc
  ) []

/-- Clear all dirty bits (after FENCE.I writeback is complete). -/
def L1DCacheState.clearAllDirty (s : L1DCacheState) : L1DCacheState :=
  { s with
    ways := fun w i =>
      let line := s.ways w i
      { line with dirty := false }
  }

/-! ## Structural Circuit -/

/-- Build the L1D Cache structural circuit.

    Ports:
    - Inputs: clock, reset, req_valid, req_we, req_addr[31:0], req_wdata[31:0], req_size[1:0],
              refill_valid, refill_data[255:0], wb_ack, fence_i
    - Outputs: resp_valid, resp_data[31:0], miss_valid, miss_addr[31:0],
               wb_valid, wb_addr[31:0], wb_data[255:0], stall, fence_i_busy
-/
def mkL1DCache : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let req_valid := Wire.mk "req_valid"
  let req_we := Wire.mk "req_we"
  let req_addr := (List.range 32).map fun i => Wire.mk s!"req_addr_{i}"
  let req_wdata := (List.range 32).map fun i => Wire.mk s!"req_wdata_{i}"
  let req_size := (List.range 2).map fun i => Wire.mk s!"req_size_{i}"
  let refill_valid := Wire.mk "refill_valid"
  let refill_data := (List.range 256).map fun i => Wire.mk s!"refill_data_{i}"
  let wb_ack := Wire.mk "wb_ack"
  let fence_i := Wire.mk "fence_i"

  -- Outputs
  let resp_valid := Wire.mk "resp_valid"
  let resp_data := (List.range 32).map fun i => Wire.mk s!"resp_data_{i}"
  let miss_valid := Wire.mk "miss_valid"
  let miss_addr := (List.range 32).map fun i => Wire.mk s!"miss_addr_{i}"
  let wb_valid := Wire.mk "wb_valid"
  let wb_addr := (List.range 32).map fun i => Wire.mk s!"wb_addr_{i}"
  let wb_data := (List.range 256).map fun i => Wire.mk s!"wb_data_{i}"
  let stall := Wire.mk "stall"
  let fence_i_busy := Wire.mk "fence_i_busy"

  -- Index bits (addr[6:5]) for 4-set cache
  let idx_bits := [req_addr[5]!, req_addr[6]!]
  -- Tag bits (addr[31:7]) = 25 bits
  let tag_bits := (List.range 25).map fun i => req_addr[i + 7]!
  -- Word offset (addr[4:2])
  let word_sel := [req_addr[2]!, req_addr[3]!, req_addr[4]!]

  -- FSM: 3-bit state register (6 states)
  let fsm_d := (List.range 3).map fun i => Wire.mk s!"fsm_d_{i}"
  let fsm_q := (List.range 3).map fun i => Wire.mk s!"fsm_q_{i}"
  let fsm_gates := (List.range 3).map fun i =>
    Gate.mkDFF fsm_d[i]! clock reset fsm_q[i]!

  -- LRU bits: 4 DFFs (one per set)
  let lru_d := (List.range 4).map fun i => Wire.mk s!"lru_d_{i}"
  let lru_q := (List.range 4).map fun i => Wire.mk s!"lru_q_{i}"
  let lru_gates := (List.range 4).map fun i =>
    Gate.mkDFF lru_d[i]! clock reset lru_q[i]!

  -- Tag storage: 2 ways × 4 sets × 25 bits
  let tag_instances := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 4).map (fun set =>
      CircuitInstance.mk "Register25" s!"u_tag_w{way}_s{set}"
        ((List.range 25).map (fun b => (s!"d_{b}", Wire.mk s!"tag_d_w{way}_s{set}_{b}")) ++
         [("clock", clock), ("reset", reset)] ++
         (List.range 25).map (fun b => (s!"q_{b}", Wire.mk s!"tag_q_w{way}_s{set}_{b}"))))
  ) []

  -- Valid bits: 2 ways × 4 sets = 8 DFFs
  let valid_d := (List.range 8).map fun i => Wire.mk s!"valid_d_{i}"
  let valid_q := (List.range 8).map fun i => Wire.mk s!"valid_q_{i}"
  let valid_dffs := (List.range 8).map fun i =>
    Gate.mkDFF valid_d[i]! clock reset valid_q[i]!

  -- Dirty bits: 2 ways × 4 sets = 8 DFFs
  let dirty_d := (List.range 8).map fun i => Wire.mk s!"dirty_d_{i}"
  let dirty_q := (List.range 8).map fun i => Wire.mk s!"dirty_q_{i}"
  let dirty_dffs := (List.range 8).map fun i =>
    Gate.mkDFF dirty_d[i]! clock reset dirty_q[i]!

  -- Data storage: 2 ways × 4 sets × 256 bits
  let data_instances := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 4).map (fun set =>
      CircuitInstance.mk "Register256" s!"u_data_w{way}_s{set}"
        ((List.range 256).map (fun b => (s!"d_{b}", Wire.mk s!"data_d_w{way}_s{set}_{b}")) ++
         [("clock", clock), ("reset", reset)] ++
         (List.range 256).map (fun b => (s!"q_{b}", Wire.mk s!"data_q_w{way}_s{set}_{b}"))))
  ) []

  -- Tag comparators: 2 ways, each comparing stored tag with request tag
  let way_hit := (List.range 2).map fun w => Wire.mk s!"way{w}_hit"
  let way_tag_match := (List.range 2).map fun w => Wire.mk s!"way{w}_tag_match"
  let way_valid_sel := (List.range 2).map fun w => Wire.mk s!"way{w}_valid_sel"

  -- For each way: mux the tag from the selected set, then compare
  let tag_mux_instances := (List.range 2).map fun way =>
    let sel_tag := (List.range 25).map fun b => Wire.mk s!"sel_tag_w{way}_{b}"
    CircuitInstance.mk "Mux4x25" s!"u_tag_mux_w{way}"
      ((List.range 4).foldl (fun acc set =>
        acc ++ (List.range 25).map (fun b =>
          (s!"in_{set}_{b}", Wire.mk s!"tag_q_w{way}_s{set}_{b}"))
      ) [] ++
      (List.range 2).map (fun i => (s!"sel_{i}", idx_bits[i]!)) ++
      (List.range 25).map (fun b => (s!"out_{b}", sel_tag[b]!)))

  let tag_cmp_instances := (List.range 2).map fun way =>
    let sel_tag := (List.range 25).map fun b => Wire.mk s!"sel_tag_w{way}_{b}"
    CircuitInstance.mk "EqualityComparator25" s!"u_tag_cmp_w{way}"
      ((List.range 25).map (fun b => (s!"a_{b}", sel_tag[b]!)) ++
       (List.range 25).map (fun b => (s!"b_{b}", tag_bits[b]!)) ++
       [("eq", way_tag_match[way]!)])

  -- Valid mux per way: 4:1 mux of valid bits
  -- way 0: valid_q[0..3], way 1: valid_q[4..7]
  let valid_mux_gates := (List.range 2).foldl (fun acc way =>
    let base := way * 4
    -- Simple 4:1 mux using decoder + AND + OR
    let not_sel := (List.range 2).map fun i => Wire.mk s!"not_sel_w{way}_{i}"
    let dec := (List.range 4).map fun i => Wire.mk s!"valid_dec_w{way}_{i}"
    let dec_and := (List.range 4).map fun i => Wire.mk s!"valid_and_w{way}_{i}"
    acc ++
    [Gate.mkNOT idx_bits[0]! not_sel[0]!,
     Gate.mkNOT idx_bits[1]! not_sel[1]!] ++
    -- 2-to-4 decoder
    [Gate.mkAND not_sel[0]! not_sel[1]! dec[0]!,
     Gate.mkAND idx_bits[0]! not_sel[1]! dec[1]!,
     Gate.mkAND not_sel[0]! idx_bits[1]! dec[2]!,
     Gate.mkAND idx_bits[0]! idx_bits[1]! dec[3]!] ++
    -- AND with valid bits
    (List.range 4).map (fun i =>
      Gate.mkAND dec[i]! valid_q[base + i]! dec_and[i]!) ++
    -- OR tree
    [Gate.mkOR dec_and[0]! dec_and[1]! (Wire.mk s!"valid_or01_w{way}"),
     Gate.mkOR dec_and[2]! dec_and[3]! (Wire.mk s!"valid_or23_w{way}"),
     Gate.mkOR (Wire.mk s!"valid_or01_w{way}") (Wire.mk s!"valid_or23_w{way}") way_valid_sel[way]!]
  ) []

  -- Hit per way = valid_sel AND tag_match
  let hit_gates := (List.range 2).map fun w =>
    Gate.mkAND way_valid_sel[w]! way_tag_match[w]! way_hit[w]!

  -- Overall hit = way0_hit OR way1_hit
  let hit := Wire.mk "hit"
  let hit_gate := Gate.mkOR way_hit[0]! way_hit[1]! hit

  -- Data read mux: for each way, select the set, then select the word
  -- Then use hit way to select the final data
  let way_word := (List.range 2).map fun way =>
    (List.range 32).map fun b => Wire.mk s!"way{way}_word_{b}"

  -- Per-way: set mux → word mux
  let data_set_mux_instances := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 8).map (fun wordIdx =>
      CircuitInstance.mk "Mux4x32" s!"u_data_set_mux_w{way}_wd{wordIdx}"
        ((List.range 4).foldl (fun acc2 set =>
          acc2 ++ (List.range 32).map (fun b =>
            (s!"in_{set}_{b}", Wire.mk s!"data_q_w{way}_s{set}_{wordIdx * 32 + b}"))
        ) [] ++
        (List.range 2).map (fun i => (s!"sel_{i}", idx_bits[i]!)) ++
        (List.range 32).map (fun b =>
          (s!"out_{b}", Wire.mk s!"data_set_w{way}_wd{wordIdx}_{b}"))))
  ) []

  let data_word_mux_instances := (List.range 2).map fun way =>
    CircuitInstance.mk "Mux8x32" s!"u_data_word_mux_w{way}"
      ((List.range 8).foldl (fun acc wordIdx =>
        acc ++ (List.range 32).map (fun b =>
          (s!"in_{wordIdx}_{b}", Wire.mk s!"data_set_w{way}_wd{wordIdx}_{b}"))
      ) [] ++
      (List.range 3).map (fun i => (s!"sel_{i}", word_sel[i]!)) ++
      (List.range 32).map (fun b => (s!"out_{b}", (way_word[way]!)[b]!)))

  -- Final data mux: way1_hit selects between way0 and way1 data
  let resp_data_mux_gates := (List.range 32).map fun b =>
    Gate.mkMUX way_hit[1]! (way_word[0]![b]!) (way_word[1]![b]!) resp_data[b]!

  -- FSM decode
  let not_fsm := (List.range 3).map fun i => Wire.mk s!"not_fsm_{i}"
  let is_idle := Wire.mk "is_idle"
  let fsm_decode_gates :=
    (List.range 3).map (fun i => Gate.mkNOT fsm_q[i]! not_fsm[i]!) ++
    [-- IDLE = 000
     Gate.mkAND not_fsm[0]! not_fsm[1]! (Wire.mk "idle_01"),
     Gate.mkAND (Wire.mk "idle_01") not_fsm[2]! is_idle]

  -- resp_valid = hit AND req_valid AND is_idle AND NOT req_we
  let not_we := Wire.mk "not_we"
  let resp_valid_gates := [
    Gate.mkNOT req_we not_we,
    Gate.mkAND req_valid hit (Wire.mk "rv_tmp1"),
    Gate.mkAND (Wire.mk "rv_tmp1") is_idle (Wire.mk "rv_tmp2"),
    Gate.mkAND (Wire.mk "rv_tmp2") not_we resp_valid
  ]

  -- miss_valid, miss_addr, stall, wb_valid, wb_addr, wb_data, fence_i_busy
  -- Simplified: these are driven by FSM state
  let not_hit := Wire.mk "not_hit"
  let miss_detect := Wire.mk "miss_detect"
  let miss_gates := [
    Gate.mkNOT hit not_hit,
    Gate.mkAND is_idle req_valid (Wire.mk "miss_tmp1"),
    Gate.mkAND (Wire.mk "miss_tmp1") not_hit miss_detect
  ]

  -- miss_valid = miss_detect
  let miss_valid_gate := Gate.mkBUF miss_detect miss_valid

  -- miss_addr: line-aligned request address
  let miss_addr_gates := (List.range 32).map fun i =>
    if i < 5 then
      Gate.mkAND reset (Wire.mk s!"not_fsm_0") (miss_addr[i]!)  -- const 0 approx
    else
      Gate.mkBUF req_addr[i]! miss_addr[i]!

  -- stall
  let not_idle := Wire.mk "not_idle"
  let stall_gates := [
    Gate.mkNOT is_idle not_idle,
    Gate.mkOR not_idle miss_detect (Wire.mk "stall_tmp"),
    Gate.mkAND (Wire.mk "stall_tmp") req_valid stall
  ]

  -- Placeholder connections for wb_valid, wb_addr, wb_data, fence_i_busy
  -- In full implementation these would be FSM-driven
  let wb_valid_gate := Gate.mkBUF (Wire.mk "const_zero_l1d") wb_valid
  let wb_addr_gates := (List.range 32).map fun i =>
    Gate.mkBUF (Wire.mk "const_zero_l1d") wb_addr[i]!
  let wb_data_gates := (List.range 256).map fun i =>
    Gate.mkBUF (Wire.mk "const_zero_l1d") wb_data[i]!
  let fence_busy_gate := Gate.mkBUF (Wire.mk "const_zero_l1d") fence_i_busy

  -- Const zero
  let const_zero_gates := [
    Gate.mkNOT reset (Wire.mk "not_reset_l1d"),
    Gate.mkAND reset (Wire.mk "not_reset_l1d") (Wire.mk "const_zero_l1d")
  ]

  -- LRU, valid, dirty, tag, data next-state logic (simplified: hold current values)
  -- Full implementation would include write-hit path and refill path
  let lru_hold_gates := (List.range 4).map fun i =>
    Gate.mkBUF lru_q[i]! lru_d[i]!
  let valid_hold_gates := (List.range 8).map fun i =>
    Gate.mkBUF valid_q[i]! valid_d[i]!
  let dirty_hold_gates := (List.range 8).map fun i =>
    Gate.mkBUF dirty_q[i]! dirty_d[i]!

  -- FSM next-state (simplified: stay in IDLE)
  let fsm_next_gates := (List.range 3).map fun i =>
    Gate.mkBUF (Wire.mk "const_zero_l1d") fsm_d[i]!

  -- Tag/data hold (instances manage their own state, driven by d wires)
  let tag_hold_gates := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 4).foldl (fun acc2 set =>
      acc2 ++ (List.range 25).map (fun b =>
        Gate.mkBUF (Wire.mk s!"tag_q_w{way}_s{set}_{b}") (Wire.mk s!"tag_d_w{way}_s{set}_{b}"))
    ) []
  ) []

  let data_hold_gates := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 4).foldl (fun acc2 set =>
      acc2 ++ (List.range 256).map (fun b =>
        Gate.mkBUF (Wire.mk s!"data_q_w{way}_s{set}_{b}") (Wire.mk s!"data_d_w{way}_s{set}_{b}"))
    ) []
  ) []

  let allGates :=
    fsm_gates ++ lru_gates ++ valid_dffs ++ dirty_dffs ++
    valid_mux_gates ++ hit_gates ++ [hit_gate] ++
    resp_data_mux_gates ++ fsm_decode_gates ++ resp_valid_gates ++
    miss_gates ++ [miss_valid_gate] ++ miss_addr_gates ++ stall_gates ++
    [wb_valid_gate] ++ wb_addr_gates ++ wb_data_gates ++ [fence_busy_gate] ++
    const_zero_gates ++
    lru_hold_gates ++ valid_hold_gates ++ dirty_hold_gates ++ fsm_next_gates ++
    tag_hold_gates ++ data_hold_gates

  let allInstances :=
    tag_instances ++ data_instances ++
    tag_mux_instances ++ tag_cmp_instances ++
    data_set_mux_instances ++ data_word_mux_instances

  { name := "L1DCache"
    inputs := [clock, reset, req_valid, req_we] ++ req_addr ++ req_wdata ++ req_size ++
              [refill_valid] ++ refill_data ++ [wb_ack, fence_i]
    outputs := [resp_valid] ++ resp_data ++ [miss_valid] ++ miss_addr ++
               [wb_valid] ++ wb_addr ++ wb_data ++ [stall, fence_i_busy]
    gates := allGates
    instances := allInstances
    signalGroups := [
      { name := "req_addr", width := 32, wires := req_addr },
      { name := "req_wdata", width := 32, wires := req_wdata },
      { name := "req_size", width := 2, wires := req_size },
      { name := "refill_data", width := 256, wires := refill_data },
      { name := "resp_data", width := 32, wires := resp_data },
      { name := "miss_addr", width := 32, wires := miss_addr },
      { name := "wb_addr", width := 32, wires := wb_addr },
      { name := "wb_data", width := 256, wires := wb_data }
    ]
  }

end Shoumei.RISCV.Memory.Cache

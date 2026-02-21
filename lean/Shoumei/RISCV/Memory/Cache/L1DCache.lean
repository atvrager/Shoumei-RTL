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

  -- Outputs (registered for 1-cycle hit latency)
  let resp_valid := Wire.mk "resp_valid"
  let resp_data := (List.range 32).map fun i => Wire.mk s!"resp_data_{i}"
  -- Combinational versions (before register)
  let resp_valid_comb := Wire.mk "resp_valid_comb"
  let resp_data_comb := (List.range 32).map fun i => Wire.mk s!"resp_data_comb_{i}"
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
  -- IDLE=000, REFILL_WAIT=001 (waiting for L2 refill response)
  let fsm_d := (List.range 3).map fun i => Wire.mk s!"fsm_d_{i}"
  let fsm_q := (List.range 3).map fun i => Wire.mk s!"fsm_q_{i}"
  let fsm_gates := (List.range 3).map fun i =>
    Gate.mkDFF fsm_d[i]! clock reset fsm_q[i]!

  -- Pending address register: captures req_addr on miss_detect
  let pend_d := (List.range 32).map fun i => Wire.mk s!"pend_d_{i}"
  let pend_q := (List.range 32).map fun i => Wire.mk s!"pend_q_{i}"
  let pend_dffs := (List.range 32).map fun i =>
    Gate.mkDFF pend_d[i]! clock reset pend_q[i]!

  -- Pending victim way register: captures LRU victim on miss_detect
  let pend_victim_d := Wire.mk "pend_victim_d"
  let pend_victim_q := Wire.mk "pend_victim_q"
  let pend_victim_dff := Gate.mkDFF pend_victim_d clock reset pend_victim_q

  -- Pending store capture: latch req_we, be, word_dec, wdata_shifted on miss_detect
  -- so write-allocate merge during refill uses stable values
  let pend_we_d := Wire.mk "pend_we_d"
  let pend_we_q := Wire.mk "pend_we_q"
  let pend_we_dff := Gate.mkDFF pend_we_d clock reset pend_we_q
  let pend_be_d := (List.range 4).map fun i => Wire.mk s!"pend_be_d_{i}"
  let pend_be_q := (List.range 4).map fun i => Wire.mk s!"pend_be_q_{i}"
  let pend_be_dffs := (List.range 4).map fun i =>
    Gate.mkDFF pend_be_d[i]! clock reset pend_be_q[i]!
  let pend_wdc_d := (List.range 8).map fun i => Wire.mk s!"pend_wdc_d_{i}"
  let pend_wdc_q := (List.range 8).map fun i => Wire.mk s!"pend_wdc_q_{i}"
  let pend_wdc_dffs := (List.range 8).map fun i =>
    Gate.mkDFF pend_wdc_d[i]! clock reset pend_wdc_q[i]!
  let pend_wds_d := (List.range 32).map fun i => Wire.mk s!"pend_wds_d_{i}"
  let pend_wds_q := (List.range 32).map fun i => Wire.mk s!"pend_wds_q_{i}"
  let pend_wds_dffs := (List.range 32).map fun i =>
    Gate.mkDFF pend_wds_d[i]! clock reset pend_wds_q[i]!

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

  -- Data storage: 2 RAMs (depth=4, width=256), one per way
  -- Read port: addr=idx_bits (for hit data)
  -- Write port: addr=MUX(pend_idx,idx_bits,is_refill), data=MUX(refill,merged), en=refill|write_hit
  let data_ram_rd := (List.range 2).map fun way =>
    (List.range 256).map fun b => Wire.mk s!"data_rd_w{way}_{b}"
  let data_ram_wr_en := (List.range 2).map fun way => Wire.mk s!"data_wr_en_w{way}"
  let data_ram_wr_addr := (List.range 2).map fun way =>
    (List.range 2).map fun i => Wire.mk s!"data_wr_addr_w{way}_{i}"
  let data_ram_wr_data := (List.range 2).map fun way =>
    (List.range 256).map fun b => Wire.mk s!"data_wr_data_w{way}_{b}"
  let data_rams := (List.range 2).map fun way =>
    RAMPrimitive.mk s!"data_ram_w{way}" 4 256
      [{ en := data_ram_wr_en[way]!
         addr := data_ram_wr_addr[way]!
         data := data_ram_wr_data[way]! }]
      [{ addr := idx_bits
         data := data_ram_rd[way]! }]
      false clock

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
          (s!"in{set}_{b}", Wire.mk s!"tag_q_w{way}_s{set}_{b}"))
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

  -- Per-way word mux: select word from RAM-read 256-bit line
  -- data_rd_w{way} is the selected set's line (from RAM read port)
  let data_word_mux_instances := (List.range 2).map fun way =>
    CircuitInstance.mk "Mux8x32" s!"u_data_word_mux_w{way}"
      ((List.range 8).foldl (fun acc wordIdx =>
        acc ++ (List.range 32).map (fun b =>
          (s!"in{wordIdx}_{b}", (data_ram_rd[way]!)[wordIdx * 32 + b]!))
      ) [] ++
      (List.range 3).map (fun i => (s!"sel_{i}", word_sel[i]!)) ++
      (List.range 32).map (fun b => (s!"out_{b}", (way_word[way]!)[b]!)))

  -- Hit data mux: way1_hit selects between way0 and way1 data
  let hit_data := (List.range 32).map fun b => Wire.mk s!"hit_data_{b}"
  let hit_data_mux_gates := (List.range 32).map fun b =>
    Gate.mkMUX (way_word[0]![b]!) (way_word[1]![b]!) way_hit[1]! hit_data[b]!

  -- Refill word mux: extract the requested word from 256-bit refill data using pend_q[4:2]
  let pend_word_sel := [pend_q[2]!, pend_q[3]!, pend_q[4]!]
  let refill_word := (List.range 32).map fun b => Wire.mk s!"refill_word_{b}"

  let refill_word_mux_inst := CircuitInstance.mk "Mux8x32" "u_refill_word_mux"
    ((List.range 8).foldl (fun acc wordIdx =>
      acc ++ (List.range 32).map (fun b =>
        (s!"in{wordIdx}_{b}", refill_data[wordIdx * 32 + b]!))
    ) [] ++
    (List.range 3).map (fun i => (s!"sel_{i}", pend_word_sel[i]!)) ++
    (List.range 32).map (fun b => (s!"out_{b}", refill_word[b]!)))

  -- Final resp_data_comb: MUX(hit_data, refill_word, refill_done)
  -- On refill_done, return the word from refill data; otherwise return hit data
  let resp_data_mux_gates := (List.range 32).map fun b =>
    Gate.mkMUX hit_data[b]! refill_word[b]! (Wire.mk "refill_done") resp_data_comb[b]!

  -- FSM decode
  let not_fsm := (List.range 3).map fun i => Wire.mk s!"not_fsm_{i}"
  let is_idle := Wire.mk "is_idle"
  let fsm_decode_gates :=
    (List.range 3).map (fun i => Gate.mkNOT fsm_q[i]! not_fsm[i]!) ++
    [-- IDLE = 000
     Gate.mkAND not_fsm[0]! not_fsm[1]! (Wire.mk "idle_01"),
     Gate.mkAND (Wire.mk "idle_01") not_fsm[2]! is_idle]

  -- resp_valid_comb = (read_hit AND is_idle) OR refill_done
  let not_we := Wire.mk "not_we"
  let read_hit := Wire.mk "read_hit"
  let resp_valid_gates := [
    Gate.mkNOT req_we not_we,
    Gate.mkAND req_valid hit (Wire.mk "rv_tmp1"),
    Gate.mkAND (Wire.mk "rv_tmp1") not_we (Wire.mk "rv_tmp2"),
    Gate.mkAND (Wire.mk "rv_tmp2") is_idle read_hit,
    Gate.mkOR read_hit (Wire.mk "refill_done") resp_valid_comb
  ]

  -- Register resp_valid and resp_data for 1-cycle hit latency
  let resp_reg_gates :=
    [Gate.mkDFF resp_valid_comb clock reset resp_valid] ++
    (List.range 32).map fun b =>
      Gate.mkDFF resp_data_comb[b]! clock reset resp_data[b]!

  -- miss_valid, miss_addr, stall, wb_valid, wb_addr, wb_data, fence_i_busy
  -- Simplified: these are driven by FSM state
  let not_hit := Wire.mk "not_hit"
  let miss_detect := Wire.mk "miss_detect"
  let miss_gates := [
    Gate.mkNOT hit not_hit,
    Gate.mkAND is_idle req_valid (Wire.mk "miss_tmp1"),
    Gate.mkAND (Wire.mk "miss_tmp1") not_hit miss_detect
  ]

  -- miss_valid = miss_clean OR is_refill_wait (keep requesting until L2 accepts)
  -- miss_clean = miss with clean victim (skip WB); is_refill_wait covers both paths
  -- is_refill_wait is computed later in FSM next-state section; use forward ref
  let miss_valid_gate := Gate.mkOR (Wire.mk "miss_clean") (Wire.mk "is_refill_wait") miss_valid

  -- miss_addr: line-aligned address, use pend_q when in REFILL_WAIT, else req_addr
  -- MUX(req_addr, pend_q, is_refill_wait) per bit, with low 5 bits forced to 0
  let miss_addr_gates := (List.range 32).map fun i =>
    if i < 5 then
      Gate.mkBUF (Wire.mk "const_zero_l1d") miss_addr[i]!
    else
      Gate.mkMUX req_addr[i]! pend_q[i]! (Wire.mk "is_refill_wait") miss_addr[i]!

  -- stall: when not idle or on miss_detect
  let not_idle := Wire.mk "not_idle"
  let stall_gates := [
    Gate.mkNOT is_idle not_idle,
    Gate.mkOR not_idle miss_detect stall
  ]

  -- === Victim capture registers (tag + data, latched on miss_detect for dirty writeback) ===
  -- Victim data MUX: select victim way's RAM data
  let victim_data_mux := (List.range 256).map fun b =>
    Gate.mkMUX (data_ram_rd[0]!)[b]! (data_ram_rd[1]!)[b]! (Wire.mk "victim_lru") (Wire.mk s!"vdata_mux_{b}")
  -- Victim tag MUX: select victim way's tag
  let victim_tag_mux := (List.range 25).map fun b =>
    Gate.mkMUX (Wire.mk s!"sel_tag_w0_{b}") (Wire.mk s!"sel_tag_w1_{b}") (Wire.mk "victim_lru") (Wire.mk s!"vtag_mux_{b}")
  -- Capture registers: hold on miss_dirty, else hold previous
  let wb_data_d := (List.range 256).map fun b => Wire.mk s!"wb_data_d_{b}"
  let wb_data_q := (List.range 256).map fun b => Wire.mk s!"wb_data_q_{b}"
  let wb_tag_d := (List.range 25).map fun b => Wire.mk s!"wb_tag_d_{b}"
  let wb_tag_q := (List.range 25).map fun b => Wire.mk s!"wb_tag_q_{b}"
  let wb_capture_gates :=
    (List.range 256).foldl (fun acc b =>
      acc ++ [
        Gate.mkMUX wb_data_q[b]! (Wire.mk s!"vdata_mux_{b}") miss_detect wb_data_d[b]!,
        Gate.mkDFF wb_data_d[b]! clock reset wb_data_q[b]!
      ]
    ) [] ++
    (List.range 25).foldl (fun acc b =>
      acc ++ [
        Gate.mkMUX wb_tag_q[b]! (Wire.mk s!"vtag_mux_{b}") miss_detect wb_tag_d[b]!,
        Gate.mkDFF wb_tag_d[b]! clock reset wb_tag_q[b]!
      ]
    ) []

  -- wb_valid = is_wb (asserted during WB state)
  let wb_valid_gate := Gate.mkBUF (Wire.mk "is_wb") wb_valid
  -- wb_addr = {wb_tag_q[24:0], pend_idx[1:0], 5'b00000}
  let wb_addr_gates := (List.range 32).map fun i =>
    if i < 5 then
      Gate.mkBUF (Wire.mk "const_zero_l1d") wb_addr[i]!
    else if i < 7 then
      Gate.mkBUF pend_q[i]! wb_addr[i]!
    else
      Gate.mkBUF wb_tag_q[i - 7]! wb_addr[i]!
  -- wb_data from captured victim data register
  let wb_data_gates := (List.range 256).map fun i =>
    Gate.mkBUF wb_data_q[i]! wb_data[i]!
  let fence_busy_gate := Gate.mkBUF (Wire.mk "const_zero_l1d") fence_i_busy

  -- Const zero
  let const_zero_gates := [
    Gate.mkNOT reset (Wire.mk "not_reset_l1d"),
    Gate.mkAND reset (Wire.mk "not_reset_l1d") (Wire.mk "const_zero_l1d")
  ]

  -- === Set decoder for current req_addr (for hit detection + write-hit) ===
  let set_dec := (List.range 4).map fun i => Wire.mk s!"valid_dec_w0_{i}"

  -- === Pending set decoder (for refill install) ===
  let pend_idx := [pend_q[5]!, pend_q[6]!]
  let not_pidx := (List.range 2).map fun i => Wire.mk s!"not_pidx_{i}"
  let pend_dec := (List.range 4).map fun i => Wire.mk s!"pend_dec_{i}"
  let pend_dec_gates :=
    (List.range 2).map (fun i => Gate.mkNOT pend_idx[i]! not_pidx[i]!) ++
    [Gate.mkAND not_pidx[0]! not_pidx[1]! pend_dec[0]!,
     Gate.mkAND pend_idx[0]! not_pidx[1]! pend_dec[1]!,
     Gate.mkAND not_pidx[0]! pend_idx[1]! pend_dec[2]!,
     Gate.mkAND pend_idx[0]! pend_idx[1]! pend_dec[3]!]

  -- === Pending tag bits (from pend_q[31:7]) ===
  let pend_tag := (List.range 25).map fun i => pend_q[i + 7]!

  -- === LRU victim way for current set (used at miss_detect time) ===
  let victim_lru := Wire.mk "victim_lru"
  let not_victim := Wire.mk "not_victim"
  let lru_mux_gates :=
    let la := (List.range 4).map fun i => Wire.mk s!"lru_and_{i}"
    (List.range 4).map (fun i => Gate.mkAND set_dec[i]! lru_q[i]! la[i]!) ++
    [Gate.mkOR la[0]! la[1]! (Wire.mk "lru_or01"),
     Gate.mkOR la[2]! la[3]! (Wire.mk "lru_or23"),
     Gate.mkOR (Wire.mk "lru_or01") (Wire.mk "lru_or23") victim_lru,
     Gate.mkNOT victim_lru not_victim]

  -- === Pending victim (from register, for refill install) ===
  let not_pend_victim := Wire.mk "not_pend_victim"
  let pend_victim_not_gate := Gate.mkNOT pend_victim_q not_pend_victim

  -- === Write-hit detection ===
  let write_hit := Wire.mk "write_hit"
  let write_hit_gates := [
    Gate.mkAND req_valid req_we (Wire.mk "wh_t1"),
    Gate.mkAND (Wire.mk "wh_t1") hit (Wire.mk "wh_t2"),
    Gate.mkAND (Wire.mk "wh_t2") is_idle write_hit
  ]

  -- === Word decoder (3-to-8) for write-hit ===
  let not_ws := (List.range 3).map fun i => Wire.mk s!"nws_{i}"
  let not_ws_gates := (List.range 3).map fun i => Gate.mkNOT word_sel[i]! not_ws[i]!
  let word_dec := (List.range 8).map fun i => Wire.mk s!"wdc_{i}"
  let word_dec_gates := (List.range 8).foldl (fun acc i =>
    let b0 := if i % 2 == 0 then not_ws[0]! else word_sel[0]!
    let b1 := if (i / 2) % 2 == 0 then not_ws[1]! else word_sel[1]!
    let b2 := if (i / 4) % 2 == 0 then not_ws[2]! else word_sel[2]!
    acc ++ [Gate.mkAND b0 b1 (Wire.mk s!"wdct_{i}"), Gate.mkAND (Wire.mk s!"wdct_{i}") b2 word_dec[i]!]
  ) []

  -- === NOT way1_hit for way 0 matching ===
  let not_way1_hit_gate := Gate.mkNOT way_hit[1]! (Wire.mk "not_w1h")

  -- === Refill + write-hit enables per way/set ===
  -- Refill uses pend_dec (pending address) and pend_victim (latched victim way)
  -- Write-hit uses set_dec (current address) and way_hit
  let refill_wh_gates := (List.range 2).foldl (fun acc way =>
    let vmatch := if way == 0 then not_pend_victim else pend_victim_q
    let hmatch := if way == 0 then (Wire.mk "not_w1h") else way_hit[1]!
    acc ++ (List.range 4).foldl (fun acc2 set =>
      acc2 ++ [
        Gate.mkAND refill_valid pend_dec[set]! (Wire.mk s!"rfs_{way}_{set}"),
        Gate.mkAND (Wire.mk s!"rfs_{way}_{set}") vmatch (Wire.mk s!"rfe_{way}_{set}"),
        Gate.mkAND write_hit set_dec[set]! (Wire.mk s!"whs_{way}_{set}"),
        Gate.mkAND (Wire.mk s!"whs_{way}_{set}") hmatch (Wire.mk s!"whe_{way}_{set}")
      ]
    ) []
  ) []

  -- === Byte-enable decode from req_size[1:0] + req_addr[1:0] ===
  -- req_size: 00=byte, 01=halfword, 10=word
  -- be_0..be_3: per-byte enables
  let not_sz := (List.range 2).map fun i => Wire.mk s!"not_sz_{i}"
  let not_ba := (List.range 2).map fun i => Wire.mk s!"not_ba_{i}"
  let be := (List.range 4).map fun i => Wire.mk s!"be_{i}"
  let byte_en_gates :=
    [Gate.mkNOT req_size[0]! not_sz[0]!, Gate.mkNOT req_size[1]! not_sz[1]!,
     Gate.mkNOT req_addr[0]! not_ba[0]!, Gate.mkNOT req_addr[1]! not_ba[1]!] ++
    -- is_byte = NOT sz1 AND NOT sz0;  is_half = NOT sz1 AND sz0;  is_word = sz1
    -- be_0: word OR (half AND NOT addr1) OR (byte AND NOT addr1 AND NOT addr0)
    [Gate.mkAND not_sz[1]! not_sz[0]! (Wire.mk "is_byte"),
     Gate.mkAND not_sz[1]! req_size[0]! (Wire.mk "is_half"),
     -- be_0: byte AND ba==00, OR half AND ba1==0, OR word
     Gate.mkAND (Wire.mk "is_byte") not_ba[1]! (Wire.mk "be0_bt"),
     Gate.mkAND (Wire.mk "be0_bt") not_ba[0]! (Wire.mk "be0_b"),
     Gate.mkAND (Wire.mk "is_half") not_ba[1]! (Wire.mk "be0_h"),
     Gate.mkOR (Wire.mk "be0_b") (Wire.mk "be0_h") (Wire.mk "be0_bh"),
     Gate.mkOR (Wire.mk "be0_bh") req_size[1]! be[0]!,
     -- be_1: byte AND ba==01, OR half AND ba1==0, OR word
     Gate.mkAND (Wire.mk "is_byte") not_ba[1]! (Wire.mk "be1_bt"),
     Gate.mkAND (Wire.mk "be1_bt") req_addr[0]! (Wire.mk "be1_b"),
     Gate.mkOR (Wire.mk "be1_b") (Wire.mk "be0_h") (Wire.mk "be1_bh"),
     Gate.mkOR (Wire.mk "be1_bh") req_size[1]! be[1]!,
     -- be_2: byte AND ba==10, OR half AND ba1==1, OR word
     Gate.mkAND (Wire.mk "is_byte") req_addr[1]! (Wire.mk "be2_bt"),
     Gate.mkAND (Wire.mk "be2_bt") not_ba[0]! (Wire.mk "be2_b"),
     Gate.mkAND (Wire.mk "is_half") req_addr[1]! (Wire.mk "be2_h"),
     Gate.mkOR (Wire.mk "be2_b") (Wire.mk "be2_h") (Wire.mk "be2_bh"),
     Gate.mkOR (Wire.mk "be2_bh") req_size[1]! be[2]!,
     -- be_3: byte AND ba==11, OR half AND ba1==1, OR word
     Gate.mkAND (Wire.mk "be2_bt") req_addr[0]! (Wire.mk "be3_b"),
     Gate.mkOR (Wire.mk "be3_b") (Wire.mk "be2_h") (Wire.mk "be3_bh"),
     Gate.mkOR (Wire.mk "be3_bh") req_size[1]! be[3]!]

  -- === Shifted write data: replicate store data to correct byte lanes ===
  -- wdata_shifted[7:0]   = req_wdata[7:0]  (always)
  -- wdata_shifted[15:8]  = is_byte ? req_wdata[7:0] : req_wdata[15:8]
  -- wdata_shifted[23:16] = is_word ? req_wdata[23:16] : req_wdata[7:0]
  -- wdata_shifted[31:24] = is_word ? req_wdata[31:24] : (is_byte ? req_wdata[7:0] : req_wdata[15:8])
  let wdata_shifted := (List.range 32).map fun i => Wire.mk s!"wds_{i}"
  let wdata_shift_gates :=
    -- Byte 0: passthrough
    (List.range 8).map (fun i =>
      Gate.mkBUF req_wdata[i]! wdata_shifted[i]!) ++
    -- Byte 1: MUX(req_wdata[15:8], req_wdata[7:0], is_byte)
    --   = is_byte ? req_wdata[7:0] : req_wdata[15:8]
    (List.range 8).map (fun i =>
      Gate.mkMUX req_wdata[8+i]! req_wdata[i]! (Wire.mk "is_byte") wdata_shifted[8+i]!) ++
    -- Byte 2: MUX(req_wdata[7:0], req_wdata[23:16], req_size[1])
    --   = is_word ? req_wdata[23:16] : req_wdata[7:0]
    (List.range 8).map (fun i =>
      Gate.mkMUX req_wdata[i]! req_wdata[16+i]! req_size[1]! wdata_shifted[16+i]!) ++
    -- Byte 3: first MUX byte vs half source, then word override
    --   temp = is_byte ? req_wdata[7:0] : req_wdata[15:8]
    --   result = is_word ? req_wdata[31:24] : temp
    (List.range 8).map (fun i =>
      Gate.mkMUX req_wdata[8+i]! req_wdata[i]! (Wire.mk "is_byte") (Wire.mk s!"wds3t_{i}")) ++
    (List.range 8).map (fun i =>
      Gate.mkMUX (Wire.mk s!"wds3t_{i}") req_wdata[24+i]! req_size[1]! wdata_shifted[24+i]!)

  -- === FSM next-state ===
  -- IDLE(000) → WB(010) on miss_detect AND victim_dirty
  -- IDLE(000) → REFILL_WAIT(001) on miss_detect AND NOT victim_dirty
  -- WB(010) → REFILL_WAIT(001) on wb_ack
  -- REFILL_WAIT(001) → IDLE(000) on refill_valid, else stay
  let is_refill_wait := Wire.mk "is_refill_wait"
  let is_wb := Wire.mk "is_wb"
  let refill_done := Wire.mk "refill_done"
  let not_refill_valid := Wire.mk "not_refill_valid"
  -- Victim dirty detection: look up dirty bit for the victim way+set
  -- victim_dirty = dirty_q[victim_lru * 4 + set_index]
  -- For each possible (way, set) pair, MUX based on victim_lru and idx_bits
  let victim_dirty := Wire.mk "victim_dirty"
  let victim_dirty_gates :=
    -- First, MUX way0 dirty vs way1 dirty for each set using victim_lru
    (List.range 4).map (fun set =>
      Gate.mkMUX dirty_q[set]! dirty_q[4 + set]! victim_lru (Wire.mk s!"vd_set_{set}")) ++
    -- Then, MUX across sets using idx_bits[0..1]
    [Gate.mkMUX (Wire.mk "vd_set_0") (Wire.mk "vd_set_1") idx_bits[0]! (Wire.mk "vd_sel_01"),
     Gate.mkMUX (Wire.mk "vd_set_2") (Wire.mk "vd_set_3") idx_bits[0]! (Wire.mk "vd_sel_23"),
     Gate.mkMUX (Wire.mk "vd_sel_01") (Wire.mk "vd_sel_23") idx_bits[1]! victim_dirty]
  let not_victim_dirty := Wire.mk "not_victim_dirty"
  let miss_dirty := Wire.mk "miss_dirty"
  let miss_clean := Wire.mk "miss_clean"
  let miss_dirty_gates := [
    Gate.mkNOT victim_dirty not_victim_dirty,
    Gate.mkAND miss_detect victim_dirty miss_dirty,
    Gate.mkAND miss_detect not_victim_dirty miss_clean
  ]
  let fsm_next_gates := [
    -- Decode is_refill_wait (state 001)
    Gate.mkAND fsm_q[0]! (Wire.mk "not_fsm_1") (Wire.mk "rw_01"),
    Gate.mkAND (Wire.mk "rw_01") (Wire.mk "not_fsm_2") is_refill_wait,
    -- Decode is_wb (state 010)
    Gate.mkAND fsm_q[1]! (Wire.mk "not_fsm_0") (Wire.mk "wb_10"),
    Gate.mkAND (Wire.mk "wb_10") (Wire.mk "not_fsm_2") is_wb,
    -- Transitions
    Gate.mkAND is_refill_wait refill_valid refill_done,
    Gate.mkNOT refill_valid not_refill_valid,
    Gate.mkAND is_refill_wait not_refill_valid (Wire.mk "stay_rw"),
    Gate.mkAND is_wb wb_ack (Wire.mk "wb_done"),
    Gate.mkNOT wb_ack (Wire.mk "not_wb_ack"),
    Gate.mkAND is_wb (Wire.mk "not_wb_ack") (Wire.mk "stay_wb"),
    -- fsm_d[0] = miss_clean OR stay_rw OR wb_done
    Gate.mkOR miss_clean (Wire.mk "stay_rw") (Wire.mk "fsm0_tmp"),
    Gate.mkOR (Wire.mk "fsm0_tmp") (Wire.mk "wb_done") fsm_d[0]!,
    -- fsm_d[1] = miss_dirty OR stay_wb
    Gate.mkOR miss_dirty (Wire.mk "stay_wb") fsm_d[1]!,
    -- fsm_d[2] = 0
    Gate.mkBUF (Wire.mk "const_zero_l1d") fsm_d[2]!
  ]
  -- Note: NOT gates for fsm_q[0..2] already exist in fsm_decode_gates

  -- === Pending address capture: MUX(hold, req_addr, miss_detect) ===
  let pend_capture_gates := (List.range 32).map fun i =>
    Gate.mkMUX pend_q[i]! req_addr[i]! miss_detect pend_d[i]!

  -- === Pending victim capture: MUX(hold, victim_lru, miss_detect) ===
  let pend_victim_capture := Gate.mkMUX pend_victim_q victim_lru miss_detect pend_victim_d

  -- === Pending store capture: MUX(hold, live, miss_detect) ===
  let pend_store_capture :=
    [Gate.mkMUX pend_we_q req_we miss_detect pend_we_d] ++
    (List.range 4).map (fun i =>
      Gate.mkMUX pend_be_q[i]! be[i]! miss_detect pend_be_d[i]!) ++
    (List.range 8).map (fun i =>
      Gate.mkMUX pend_wdc_q[i]! word_dec[i]! miss_detect pend_wdc_d[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX pend_wds_q[i]! wdata_shifted[i]! miss_detect pend_wds_d[i]!)

  -- === Tag next: MUX(hold, pend_tag, refill_en) ===
  -- Use pend_tag (from pending address) for refill tag installation
  let tag_next_gates := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 4).foldl (fun acc2 set =>
      acc2 ++ (List.range 25).map (fun b =>
        Gate.mkMUX (Wire.mk s!"tag_q_w{way}_s{set}_{b}") pend_tag[b]!
          (Wire.mk s!"rfe_{way}_{set}") (Wire.mk s!"tag_d_w{way}_s{set}_{b}"))
    ) []
  ) []

  -- === Data RAM write logic ===
  -- Per-way: write_en, write_addr, write_data
  -- refill_for_way = refill_valid AND (way matches pend_victim)
  -- write_hit_for_way = write_hit AND way_hit[way]
  let ram_refill_w0 := Wire.mk "ram_refill_w0"
  let ram_refill_w1 := Wire.mk "ram_refill_w1"
  let ram_wh_w0 := Wire.mk "ram_wh_w0"
  let ram_wh_w1 := Wire.mk "ram_wh_w1"
  let data_ram_ctl_gates := [
    Gate.mkAND refill_valid not_pend_victim ram_refill_w0,
    Gate.mkAND refill_valid pend_victim_q ram_refill_w1,
    Gate.mkAND write_hit (Wire.mk "not_w1h") ram_wh_w0,
    Gate.mkAND write_hit way_hit[1]! ram_wh_w1,
    -- write enables
    Gate.mkOR ram_refill_w0 ram_wh_w0 data_ram_wr_en[0]!,
    Gate.mkOR ram_refill_w1 ram_wh_w1 data_ram_wr_en[1]!
  ]
  -- Write address: refill uses pend_idx, write-hit uses idx_bits
  -- Since refill and write-hit are mutually exclusive, MUX on refill_valid
  let data_ram_addr_gates := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 2).map (fun i =>
      Gate.mkMUX idx_bits[i]! pend_idx[i]! refill_valid (data_ram_wr_addr[way]!)[i]!)
  ) []
  -- Write data: refill uses refill_data (merged with pending store), write-hit uses merge(ram_rd, wdata_shifted)
  -- Merge logic: for each bit, MUX(ram_rd[b], wdata_shifted[b%32], write_hit_byte_en)
  -- write_hit_byte_en for bit b = word_dec[b/32] AND be[(b%32)/8]
  -- Note: word_dec and be are already computed (shared across ways)
  -- Write-allocate: when refill arrives for a store miss, merge store data into refill line
  -- Uses PENDING captured signals (pend_we_q, pend_wdc_q, pend_be_q, pend_wds_q)
  -- because live req_* signals may have changed since the miss
  let refill_merge_gates := (List.range 256).foldl (fun acc b =>
    let wd := b / 32
    let bb := b % 32
    let byte := bb / 8
    -- refill_store_en_{b} = pend_we_q AND pend_wdc_q[wd] AND pend_be_q[byte]
    -- refill_merged_{b} = MUX(refill_data[b], pend_wds_q[bb], refill_store_en_{b})
    acc ++ [
      Gate.mkAND pend_we_q pend_wdc_q[wd]! (Wire.mk s!"rse_tmp_{b}"),
      Gate.mkAND (Wire.mk s!"rse_tmp_{b}") pend_be_q[byte]! (Wire.mk s!"refill_store_en_{b}"),
      Gate.mkMUX refill_data[b]! pend_wds_q[bb]!
        (Wire.mk s!"refill_store_en_{b}") (Wire.mk s!"refill_merged_{b}")
    ]
  ) []
  let data_ram_merge_gates := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 256).foldl (fun acc2 b =>
      let wd := b / 32
      let bb := b % 32
      let byte := bb / 8
      -- merged_{way}_{b} = MUX(ram_rd, wdata_shifted, wdc AND be)
      acc2 ++ [
        Gate.mkAND word_dec[wd]! be[byte]! (Wire.mk s!"ram_be_w{way}_{b}"),
        Gate.mkMUX (data_ram_rd[way]!)[b]! wdata_shifted[bb]!
          (Wire.mk s!"ram_be_w{way}_{b}") (Wire.mk s!"ram_merged_w{way}_{b}"),
        -- Final write data: MUX(merged, refill_merged, refill_valid)
        Gate.mkMUX (Wire.mk s!"ram_merged_w{way}_{b}") (Wire.mk s!"refill_merged_{b}")
          refill_valid (data_ram_wr_data[way]!)[b]!
      ]
    ) []
  ) []

  -- === Valid next: set on refill (rfe uses pend_dec already) ===
  let valid_next_gates := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 4).map (fun set =>
      Gate.mkOR valid_q[way * 4 + set]! (Wire.mk s!"rfe_{way}_{set}") valid_d[way * 4 + set]!)
  ) []

  -- === Dirty next: set on write-hit OR write-allocate refill, clear on read refill, hold otherwise ===
  -- write-allocate refill: refill_enable AND req_we (store miss that was merged)
  let dirty_next_gates := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 4).foldl (fun acc2 set =>
      let idx := way * 4 + set
      acc2 ++ [
        -- refill_we_{way}_{set} = rfe AND pend_we_q (write-allocate sets dirty)
        Gate.mkAND (Wire.mk s!"rfe_{way}_{set}") pend_we_q (Wire.mk s!"refill_we_{way}_{set}"),
        Gate.mkNOT (Wire.mk s!"rfe_{way}_{set}") (Wire.mk s!"nrfe_{way}_{set}"),
        Gate.mkAND dirty_q[idx]! (Wire.mk s!"nrfe_{way}_{set}") (Wire.mk s!"dh_{way}_{set}"),
        Gate.mkOR (Wire.mk s!"dh_{way}_{set}") (Wire.mk s!"whe_{way}_{set}") (Wire.mk s!"dh2_{way}_{set}"),
        Gate.mkOR (Wire.mk s!"dh2_{way}_{set}") (Wire.mk s!"refill_we_{way}_{set}") dirty_d[idx]!
      ]
    ) []
  ) []

  -- === LRU next: update on refill (using pend_dec) or write-hit (using set_dec) ===
  let lru_next_gates := (List.range 4).foldl (fun acc set =>
    acc ++ [
      Gate.mkAND refill_valid pend_dec[set]! (Wire.mk s!"lru_rf_{set}"),
      Gate.mkAND write_hit set_dec[set]! (Wire.mk s!"lru_wh_{set}"),
      Gate.mkOR (Wire.mk s!"lru_rf_{set}") (Wire.mk s!"lru_wh_{set}") (Wire.mk s!"lru_en_{set}"),
      -- On refill: new LRU = NOT pend_victim (mark other way as next victim)
      -- On write-hit: new LRU = NOT way1_hit (if hit way0, evict way1 next)
      Gate.mkMUX (Wire.mk "not_w1h") not_pend_victim refill_valid (Wire.mk s!"lru_nv_{set}"),
      Gate.mkMUX lru_q[set]! (Wire.mk s!"lru_nv_{set}") (Wire.mk s!"lru_en_{set}") lru_d[set]!
    ]
  ) []

  let allGates :=
    fsm_gates ++ pend_dffs ++ [pend_victim_dff] ++
    [pend_we_dff] ++ pend_be_dffs ++ pend_wdc_dffs ++ pend_wds_dffs ++
    lru_gates ++ valid_dffs ++ dirty_dffs ++
    valid_mux_gates ++ hit_gates ++ [hit_gate] ++
    hit_data_mux_gates ++ resp_data_mux_gates ++ fsm_decode_gates ++ resp_valid_gates ++ resp_reg_gates ++
    miss_gates ++ [miss_valid_gate] ++ miss_addr_gates ++ stall_gates ++
    victim_data_mux ++ victim_tag_mux ++ wb_capture_gates ++
    [wb_valid_gate] ++ wb_addr_gates ++ wb_data_gates ++ [fence_busy_gate] ++
    victim_dirty_gates ++ miss_dirty_gates ++
    const_zero_gates ++
    pend_dec_gates ++ lru_mux_gates ++ [pend_victim_not_gate] ++
    write_hit_gates ++ not_ws_gates ++ word_dec_gates ++
    [not_way1_hit_gate] ++ refill_wh_gates ++ byte_en_gates ++ wdata_shift_gates ++
    fsm_next_gates ++ pend_capture_gates ++ [pend_victim_capture] ++ pend_store_capture ++
    tag_next_gates ++ data_ram_ctl_gates ++ data_ram_addr_gates ++ refill_merge_gates ++ data_ram_merge_gates ++
    valid_next_gates ++ dirty_next_gates ++ lru_next_gates

  let allInstances :=
    tag_instances ++
    tag_mux_instances ++ tag_cmp_instances ++
    data_word_mux_instances ++
    [refill_word_mux_inst]

  { name := "L1DCache"
    inputs := [clock, reset, req_valid, req_we] ++ req_addr ++ req_wdata ++ req_size ++
              [refill_valid] ++ refill_data ++ [wb_ack, fence_i]
    outputs := [resp_valid] ++ resp_data ++ [miss_valid] ++ miss_addr ++
               [wb_valid] ++ wb_addr ++ wb_data ++ [stall, fence_i_busy]
    gates := allGates
    instances := allInstances
    rams := data_rams
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

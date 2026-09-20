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
import Shoumei.RISCV.Config
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
              refill_valid, refill_data[lineBits-1:0], wb_ack, fence_i
    - Outputs: resp_valid, resp_data[31:0], miss_valid, miss_addr[31:0],
               wb_valid, wb_addr[31:0], wb_data[lineBits-1:0], stall, fence_i_busy
-/
def mkL1DCache (g : CacheGeom := CacheGeom.default) : Circuit :=
  -- Geometry, derived once: the structure below is written in terms of these.
  let sets := g.l1dSets
  let ways := g.l1dWays
  let lineBits := g.lineBytes * 8
  let offsetBits := log2Ceil g.lineBytes
  let idxBits := log2Ceil sets
  let wordBits := offsetBits - 2
  let lineWords := lineBits / 32
  let tagBits := 32 - idxBits - offsetBits
  let lines := ways * sets
  let waySelBits := if ways ≤ 1 then 0 else Nat.log2 ways
  let flushIdxBits := idxBits + waySelBits
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let req_valid := Wire.mk "req_valid"
  let req_we := Wire.mk "req_we"
  let req_addr := (List.range 32).map fun i => Wire.mk s!"req_addr_{i}"
  let req_wdata := (List.range 64).map fun i => Wire.mk s!"req_wdata_{i}"
  let req_size := (List.range 2).map fun i => Wire.mk s!"req_size_{i}"
  let refill_valid := Wire.mk "refill_valid"
  let refill_data := (List.range lineBits).map fun i => Wire.mk s!"refill_data_{i}"
  let wb_ack := Wire.mk "wb_ack"
  let fence_i := Wire.mk "fence_i"

  -- Outputs (registered for 1-cycle hit latency)
  let resp_valid := Wire.mk "resp_valid"
  let resp_data := (List.range 64).map fun i => Wire.mk s!"resp_data_{i}"
  -- Combinational versions (before register)
  let resp_valid_comb := Wire.mk "resp_valid_comb"
  let resp_data_comb := (List.range 64).map fun i => Wire.mk s!"resp_data_comb_{i}"
  let miss_valid := Wire.mk "miss_valid"
  let miss_addr := (List.range 32).map fun i => Wire.mk s!"miss_addr_{i}"
  let wb_valid := Wire.mk "wb_valid"
  let wb_addr := (List.range 32).map fun i => Wire.mk s!"wb_addr_{i}"
  let wb_data := (List.range lineBits).map fun i => Wire.mk s!"wb_data_{i}"
  let stall := Wire.mk "stall"
  let fence_i_busy := Wire.mk "fence_i_busy"

  -- Index bits: addr[offsetBits + idxBits - 1 : offsetBits]
  let idx_bits := (List.range idxBits).map fun i => req_addr[offsetBits + i]!
  -- Tag bits: everything above index + offset
  let tag_bits := (List.range tagBits).map fun i => req_addr[offsetBits + idxBits + i]!
  -- Word offset within the line: addr[offsetBits-1 : 2]
  let word_sel := (List.range wordBits).map fun i => req_addr[2 + i]!

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

  -- Replacement: one tree-PLRU per set (it degenerates to the single LRU bit
  -- at two ways), each updated by the refill or write-hit that touches its set.
  -- one-hot selects used across the module (declared before their gates)
  let victim_oh := (List.range ways).map fun w => Wire.mk s!"victim_oh_{w}"
  let pend_victim_oh := (List.range ways).map fun w => Wire.mk s!"pend_victim_oh_{w}"
  let pend_victim_d := (List.range ways).map fun w => Wire.mk s!"pend_victim_d_{w}"
  let plru_victim := (List.range sets).map (fun st =>
    (List.range ways).map (fun w => Wire.mk s!"plru_victim_{st}_{w}"))
  let plru_upd_en := (List.range sets).map fun st => Wire.mk s!"plru_upd_en_{st}"
  let plru_upd_way := (List.range sets).map (fun st =>
    (List.range ways).map (fun w => Wire.mk s!"plru_upd_way_{st}_{w}"))
  let plru_gates : List Gate :=
    -- the update source: a refill writes pend_victim, a write-hit touches the
    -- hitting way; the two events are mutually exclusive
    (List.range sets).map (fun st => Gate.mkAND (Wire.mk "refill_done") (Wire.mk s!"pend_dec_{st}")
      (Wire.mk s!"plru_rf_evt_{st}")) ++
    (List.range sets).map (fun st => Gate.mkAND (Wire.mk "write_hit") (Wire.mk s!"valid_dec_w0_{st}")
      (Wire.mk s!"plru_wh_evt_{st}")) ++
    (List.range sets).map (fun st =>
      Gate.mkOR (Wire.mk s!"plru_rf_evt_{st}") (Wire.mk s!"plru_wh_evt_{st}") plru_upd_en[st]!) ++
    List.flatten ((List.range sets).map (fun st =>
      List.flatten ((List.range ways).map (fun w =>
        [Gate.mkAND (Wire.mk s!"plru_rf_evt_{st}") (Wire.mk s!"pend_victim_oh_{w}")
           (Wire.mk s!"plru_rf_w_{st}_{w}"),
         Gate.mkAND (Wire.mk s!"plru_wh_evt_{st}") (Wire.mk s!"way{w}_hit")
           (Wire.mk s!"plru_wh_w_{st}_{w}"),
         Gate.mkOR (Wire.mk s!"plru_rf_w_{st}_{w}") (Wire.mk s!"plru_wh_w_{st}_{w}")
           plru_upd_way[st]![w]!]))))
  let plru_insts : List CircuitInstance := (List.range sets).map fun st =>
    CircuitInstance.mk s!"PLRU{ways}" s!"u_plru_s{st}"
      ([("clock", clock), ("reset", reset),
        ("zero", Wire.mk "const_zero_l1d"), ("one", Wire.mk "const_one_l1d"),
        ("upd_en", plru_upd_en[st]!)] ++
       (List.range ways).map (fun w => (s!"upd_way_oh_{w}", plru_upd_way[st]![w]!)) ++
       (List.range ways).map (fun w => (s!"victim_oh_{w}", plru_victim[st]![w]!)))

  -- Tag storage: ways × sets × tagBits
  let tag_instances := (List.range ways).foldl (fun acc way =>
    acc ++ (List.range sets).map (fun set =>
      CircuitInstance.mk s!"Register{tagBits}" s!"u_tag_w{way}_s{set}"
        ((List.range tagBits).map (fun b => (s!"d_{b}", Wire.mk s!"tag_d_w{way}_s{set}_{b}")) ++
         [("clock", clock), ("reset", reset)] ++
         (List.range tagBits).map (fun b => (s!"q_{b}", Wire.mk s!"tag_q_w{way}_s{set}_{b}"))))
  ) []

  -- Valid bits: one per line (ways × sets)
  let valid_d := (List.range lines).map fun i => Wire.mk s!"valid_d_{i}"
  let valid_q := (List.range lines).map fun i => Wire.mk s!"valid_q_{i}"
  let valid_dffs := (List.range lines).map fun i =>
    Gate.mkDFF valid_d[i]! clock reset valid_q[i]!

  -- Dirty bits: one per line
  let dirty_d := (List.range lines).map fun i => Wire.mk s!"dirty_d_{i}"
  let dirty_q := (List.range lines).map fun i => Wire.mk s!"dirty_q_{i}"
  let dirty_dffs := (List.range lines).map fun i =>
    Gate.mkDFF dirty_d[i]! clock reset dirty_q[i]!

  -- Data storage: 2 RAMs (depth=4, width=256), one per way
  -- Read port: addr=MUX(idx_bits, pend_idx, is_writeback) — use pend_idx during WRITEBACK
  --   to read victim data for writeback; idx_bits during normal operation for hit detection.
  -- Write port: addr=MUX(pend_idx,idx_bits,is_refill), data=MUX(refill,merged), en=refill|write_hit
  let data_ram_rd_addr := (List.range idxBits).map fun i => Wire.mk s!"data_rd_addr_{i}"
  let data_ram_rd_addr_mux := (List.range idxBits).map fun i =>
    Gate.mkMUX idx_bits[i]! pend_q[offsetBits + i]! (Wire.mk "wb_active") data_ram_rd_addr[i]!
  let data_ram_rd := (List.range ways).map fun way =>
    (List.range lineBits).map fun b => Wire.mk s!"data_rd_w{way}_{b}"
  let data_ram_wr_en := (List.range ways).map fun way => Wire.mk s!"data_wr_en_w{way}"
  let data_ram_wr_addr := (List.range ways).map fun way =>
    (List.range idxBits).map fun i => Wire.mk s!"data_wr_addr_w{way}_{i}"
  let data_ram_wr_data := (List.range ways).map fun way =>
    (List.range lineBits).map fun b => Wire.mk s!"data_wr_data_w{way}_{b}"
  let data_rams := (List.range ways).map fun way =>
    RAMPrimitive.mk s!"data_ram_w{way}" sets lineBits
      [{ en := data_ram_wr_en[way]!
         addr := data_ram_wr_addr[way]!
         data := data_ram_wr_data[way]! }]
      [{ addr := data_ram_rd_addr
         data := data_ram_rd[way]! }]
      false clock
      -- 1R1W contract: separate read/write addresses, asynchronous read
      (portKind := .r1w1)

  -- Tag comparators: 2 ways, each comparing stored tag with request tag
  let way_hit := (List.range ways).map fun w => Wire.mk s!"way{w}_hit"
  let way_tag_match := (List.range ways).map fun w => Wire.mk s!"way{w}_tag_match"
  let way_valid_sel := (List.range ways).map fun w => Wire.mk s!"way{w}_valid_sel"

  -- For each way: mux the tag from the selected set, then compare
  -- Use data_ram_rd_addr (MUXed idx_bits/pend_idx) for tag select too,
  -- so tag reads use pend_idx during WRITEBACK (for correct wb_addr)
  let tag_mux_instances := (List.range ways).map fun way =>
    let sel_tag := (List.range tagBits).map fun b => Wire.mk s!"sel_tag_w{way}_{b}"
    CircuitInstance.mk s!"Mux{sets}x{tagBits}" s!"u_tag_mux_w{way}"
      ((List.range sets).foldl (fun acc set =>
        acc ++ (List.range tagBits).map (fun b =>
          (s!"in{set}_{b}", Wire.mk s!"tag_q_w{way}_s{set}_{b}"))
      ) [] ++
      (List.range idxBits).map (fun i => (s!"sel_{i}", data_ram_rd_addr[i]!)) ++
      (List.range tagBits).map (fun b => (s!"out_{b}", sel_tag[b]!)))

  let tag_cmp_instances := (List.range ways).map fun way =>
    let sel_tag := (List.range tagBits).map fun b => Wire.mk s!"sel_tag_w{way}_{b}"
    CircuitInstance.mk s!"EqualityComparator{tagBits}" s!"u_tag_cmp_w{way}"
      ((List.range tagBits).map (fun b => (s!"a_{b}", sel_tag[b]!)) ++
       (List.range tagBits).map (fun b => (s!"b_{b}", tag_bits[b]!)) ++
       [("eq", way_tag_match[way]!)])

  -- Valid mux per way: 4:1 mux of valid bits
  -- way 0: valid_q[0..3], way 1: valid_q[4..7]
  -- Per-way set select: the parametric Decoder builds the one-hot set select
  -- the way muxes and the PLRU update need (idxBits -> sets: 2 -> 4 at the
  -- default geometry, 6 -> 64 at the MCU one).
  let valid_dec := (List.range ways).map (fun way =>
    (List.range sets).map (fun st => Wire.mk s!"valid_dec_w{way}_{st}"))
  let valid_dec_insts : List CircuitInstance := (List.range ways).map fun way =>
    CircuitInstance.mk s!"Decoder{idxBits}" s!"u_valid_dec_w{way}"
      ((List.range idxBits).map (fun i => (s!"in_{i}", idx_bits[i]!)) ++
       (List.range sets).map (fun st => (s!"out_{st}", valid_dec[way]![st]!)))
  -- Way select = OR over sets of (set select AND that set's bit)
  let way_sel_gates (q : List Wire) (pfx : String) (out : List Wire) : List Gate :=
    List.flatten ((List.range ways).map (fun way =>
      let t := (List.range sets).map (fun st => Wire.mk s!"{pfx}_and_w{way}_{st}")
      List.flatten ((List.range sets).map (fun st =>
        [Gate.mkAND valid_dec[way]![st]! q[way * sets + st]! t[st]!]))
      ++ mkOrTree t out[way]!))
  let valid_mux_gates : List Gate := way_sel_gates valid_q "valid" way_valid_sel
  let dirty_mux_gates : List Gate :=
    way_sel_gates dirty_q "dirty" ((List.range ways).map fun w => Wire.mk s!"dirty_sel_w{w}")

  -- Victim dirty detection: victim_needs_wb = valid AND dirty of the victim way
  let victim_wb_gates : List Gate :=
    List.flatten ((List.range ways).map (fun w =>
      [Gate.mkAND victim_oh[w]! way_valid_sel[w]! (Wire.mk s!"vv_and_{w}"),
       Gate.mkAND victim_oh[w]! (Wire.mk s!"dirty_sel_w{w}") (Wire.mk s!"vd_and_{w}")])) ++
    mkOrTree ((List.range ways).map (fun w => Wire.mk s!"vv_and_{w}")) (Wire.mk "victim_valid") ++
    mkOrTree ((List.range ways).map (fun w => Wire.mk s!"vd_and_{w}")) (Wire.mk "victim_dirty") ++
    [Gate.mkAND (Wire.mk "victim_valid") (Wire.mk "victim_dirty") (Wire.mk "victim_needs_wb")]

  -- Hit per way = valid_sel AND tag_match
  let hit_gates := (List.range ways).map fun w =>
    Gate.mkAND way_valid_sel[w]! way_tag_match[w]! way_hit[w]!

  -- Overall hit = way0_hit OR way1_hit
  let hit := Wire.mk "hit"
  let hit_gate := Gate.mkOR way_hit[0]! way_hit[1]! hit

  -- Data read mux: for each way, select the set, then select the word
  -- Then use hit way to select the final data
  let way_word := (List.range ways).map fun way =>
    (List.range 32).map fun b => Wire.mk s!"way{way}_word_{b}"

  -- Per-way word mux: select word from RAM-read 256-bit line (bits 0..31)
  -- data_rd_w{way} is the selected set's line (from RAM read port)
  let data_word_mux_instances := (List.range ways).map fun way =>
    CircuitInstance.mk s!"Mux{lineWords}x32" s!"u_data_word_mux_w{way}"
      ((List.range lineWords).foldl (fun acc wordIdx =>
        acc ++ (List.range 32).map (fun b =>
          (s!"in{wordIdx}_{b}", (data_ram_rd[way]!)[wordIdx * 32 + b]!))
      ) [] ++
      (List.range wordBits).map (fun i => (s!"sel_{i}", word_sel[i]!)) ++
      (List.range 32).map (fun b => (s!"out_{b}", (way_word[way]!)[b]!)))

  -- Per-way doubleword-high mux: select upper 32 bits of 64-bit dword (words 1, 3, 5, 7)
  let dword_sel := (List.range (wordBits - 1)).map fun i => req_addr[3 + i]!
  let way_dword_hi := (List.range ways).map fun way =>
    (List.range 32).map fun b => Wire.mk s!"way{way}_dwhi_{b}"

  let data_dwhi_mux_instances := (List.range ways).map fun way =>
    CircuitInstance.mk s!"Mux{lineWords / 2}x32" s!"u_data_dwhi_mux_w{way}"
      ((List.range (lineWords / 2)).foldl (fun acc dwIdx =>
        let wordIdx := dwIdx * 2 + 1
        acc ++ (List.range 32).map (fun b =>
          (s!"in{dwIdx}_{b}", (data_ram_rd[way]!)[wordIdx * 32 + b]!))
      ) [] ++
      (List.range (wordBits - 1)).map (fun i => (s!"sel_{i}", dword_sel[i]!)) ++
      (List.range 32).map (fun b => (s!"out_{b}", (way_dword_hi[way]!)[b]!)))

  -- Hit data mux (64 bits): way1_hit selects between way0 and way1 data
  let hit_data := (List.range 64).map fun b => Wire.mk s!"hit_data_{b}"
  let hit_data_mux_gates : List Gate :=
    List.flatten ((List.range 32).map (fun b =>
      let lo := (List.range ways).map (fun w => Wire.mk s!"hd_lo_{w}_{b}")
      (List.range ways).map (fun w => Gate.mkAND way_hit[w]! (way_word[w]!)[b]! lo[w]!)
      ++ mkOrTree lo hit_data[b]!))
    ++
    List.flatten ((List.range 32).map (fun b =>
      let hi := (List.range ways).map (fun w => Wire.mk s!"hd_hi_{w}_{b}")
      (List.range ways).map (fun w => Gate.mkAND way_hit[w]! (way_dword_hi[w]!)[b]! hi[w]!)
      ++ mkOrTree hi hit_data[32+b]!))

  -- Refill word mux: extract the requested lower word from 256-bit refill data using pend_q[4:2]
  let pend_word_sel := (List.range wordBits).map fun i => pend_q[2 + i]!
  let refill_word := (List.range 64).map fun b => Wire.mk s!"refill_word_{b}"

  let refill_word_mux_inst := CircuitInstance.mk s!"Mux{lineWords}x32" "u_refill_word_mux"
    ((List.range lineWords).foldl (fun acc wordIdx =>
      acc ++ (List.range 32).map (fun b =>
        (s!"in{wordIdx}_{b}", refill_data[wordIdx * 32 + b]!))
    ) [] ++
    (List.range wordBits).map (fun i => (s!"sel_{i}", pend_word_sel[i]!)) ++
    (List.range 32).map (fun b => (s!"out_{b}", refill_word[b]!)))

  -- Refill doubleword-high mux: extract upper 32 bits from 256-bit refill data using pend_q[4:3]
  let pend_dword_sel := (List.range (wordBits - 1)).map fun i => pend_q[3 + i]!
  let refill_dwhi_mux_inst := CircuitInstance.mk s!"Mux{lineWords / 2}x32" "u_refill_dwhi_mux"
    ((List.range (lineWords / 2)).foldl (fun acc dwIdx =>
      let wordIdx := dwIdx * 2 + 1
      acc ++ (List.range 32).map (fun b =>
        (s!"in{dwIdx}_{b}", refill_data[wordIdx * 32 + b]!))
    ) [] ++
    (List.range (wordBits - 1)).map (fun i => (s!"sel_{i}", pend_dword_sel[i]!)) ++
    (List.range 32).map (fun b => (s!"out_{b}", refill_word[32+b]!)))

  -- Final resp_data_comb (64 bits): MUX(hit_data, refill_word, refill_done)
  -- On refill_done, return the dword from refill data; otherwise return hit data
  let resp_data_mux_gates := (List.range 64).map fun b =>
    Gate.mkMUX hit_data[b]! refill_word[b]! (Wire.mk "refill_done") resp_data_comb[b]!

  -- FSM decode
  let not_fsm := (List.range 3).map fun i => Wire.mk s!"not_fsm_{i}"
  let is_idle := Wire.mk "is_idle"
  let is_writeback := Wire.mk "is_writeback"
  -- fence.i flush states (fsm_q[2] was unused): FENCE_CHECK = 100, FENCE_WB = 101
  let wb_active := Wire.mk "wb_active"
  let is_flush_check := Wire.mk "is_flush_check"
  let is_flush_wb := Wire.mk "is_flush_wb"
  let is_flush := Wire.mk "is_flush"
  let fsm_decode_gates :=
    (List.range 3).map (fun i => Gate.mkNOT fsm_q[i]! not_fsm[i]!) ++
    [-- IDLE = 000
     Gate.mkAND not_fsm[0]! not_fsm[1]! (Wire.mk "idle_01"),
     Gate.mkAND (Wire.mk "idle_01") not_fsm[2]! is_idle,
     -- WRITEBACK = 010
     Gate.mkAND not_fsm[0]! fsm_q[1]! (Wire.mk "wb_01"),
     Gate.mkAND (Wire.mk "wb_01") not_fsm[2]! is_writeback,
     -- FENCE.I flush (fsm_q[2] was unused): FENCE_CHECK = 100, FENCE_WB = 101
     Gate.mkAND fsm_q[2]! not_fsm[0]! is_flush_check,
     Gate.mkAND fsm_q[2]! fsm_q[0]! is_flush_wb,
     Gate.mkOR is_flush_check is_flush_wb is_flush,
     -- the writeback datapath (data RAM read, tag read, wb_addr/wb_data) serves both
     -- the eviction writeback and the fence.i flush writeback
     Gate.mkOR is_writeback is_flush_wb wb_active]

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
    (List.range 64).map fun b =>
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

  -- miss_valid = (miss_detect AND NOT victim_needs_wb) OR is_refill_wait
  -- When victim needs writeback, defer miss request until after WRITEBACK → REFILL_WAIT
  let miss_detect_clean := Wire.mk "miss_detect_clean"
  let miss_valid_gates := [
    Gate.mkAND miss_detect (Wire.mk "not_victim_wb") miss_detect_clean,
    Gate.mkOR miss_detect_clean (Wire.mk "is_refill_wait") miss_valid
  ]

  -- miss_addr: line-aligned address, use pend_q when in REFILL_WAIT, else req_addr
  -- MUX(req_addr, pend_q, is_refill_wait) per bit, with the offset forced to 0
  let miss_addr_gates := (List.range 32).map fun i =>
    if i < offsetBits then
      Gate.mkBUF (Wire.mk "const_zero_l1d") miss_addr[i]!
    else
      Gate.mkMUX req_addr[i]! pend_q[i]! (Wire.mk "is_refill_wait") miss_addr[i]!

  -- stall: unconditional when not idle or on miss_detect (no req_valid gating)
  let not_idle := Wire.mk "not_idle"
  let stall_gates := [
    Gate.mkNOT is_idle not_idle,
    Gate.mkOR not_idle miss_detect stall
  ]

  -- wb_valid = wb_active (eviction WRITEBACK or fence.i flush writeback)
  let wb_valid_gate := Gate.mkBUF wb_active wb_valid

  -- wb_addr: {victim_tag, index, offset 0}
  -- victim_tag = MUX(sel_tag_w0, sel_tag_w1, pend_victim_q)
  let wb_victim_tag := (List.range tagBits).map fun b => Wire.mk s!"wb_vtag_{b}"
  let wb_vtag_mux : List Gate :=
    List.flatten ((List.range tagBits).map (fun b =>
      let t := (List.range ways).map (fun w => Wire.mk s!"wb_vt_{w}_{b}")
      (List.range ways).map (fun w =>
        Gate.mkAND pend_victim_oh[w]! (Wire.mk s!"sel_tag_w{w}_{b}") t[w]!)
      ++ mkOrTree t wb_victim_tag[b]!))
  let wb_addr_gates := (List.range 32).map fun i =>
    if i < offsetBits then Gate.mkBUF (Wire.mk "const_zero_l1d") wb_addr[i]!
    else if i < offsetBits + idxBits then
      Gate.mkBUF data_ram_rd_addr[i - offsetBits]! wb_addr[i]!
    else Gate.mkBUF wb_victim_tag[i - offsetBits - idxBits]! wb_addr[i]!

  -- wb_data: MUX(data_ram_rd[0], data_ram_rd[1], pend_victim_q) per bit
  let wb_data_gates : List Gate :=
    List.flatten ((List.range lineBits).map (fun b =>
      let t := (List.range ways).map (fun w => Wire.mk s!"wb_dt_{w}_{b}")
      (List.range ways).map (fun w => Gate.mkAND pend_victim_oh[w]! (data_ram_rd[w]!)[b]! t[w]!)
      ++ mkOrTree t wb_data[b]!))

  -- === FENCE.I FLUSH ===
  -- fence.i must make stored code visible to instruction fetch.  The L1D is
  -- write-back, so every dirty line has to reach the L2 (which the L1I refills
  -- from) before the core fetches again.  All 8 lines are swept in order, one
  -- line per visit: write the dirty ones back and drop their dirty bit.  The
  -- sweep is deliberately dumb - 2 ways x 4 sets is small, and a fence is rare.
  --
  -- A fence.i that arrives while the D-side is busy (miss/eviction in flight) is
  -- latched and served on the next IDLE, so the pulse can be one cycle wide.
  let fence_pending_d := Wire.mk "fence_pending_d"
  let fence_pending_q := Wire.mk "fence_pending_q"
  let flush_start := Wire.mk "flush_start"
  let flush_idx_d := (List.range flushIdxBits).map fun i => Wire.mk s!"flush_idx_d_{i}"
  let flush_idx_q := (List.range flushIdxBits).map fun i => Wire.mk s!"flush_idx_q_{i}"
  let flush_dec := (List.range lines).map fun i => Wire.mk s!"flush_dec_{i}"
  let flush_way_oh := (List.range ways).map fun w => Wire.mk s!"flush_way_oh_{w}"
  let fl_write := Wire.mk "fl_write"
  let fl_wb_ack := Wire.mk "fl_wb_ack"
  let fl_skip := Wire.mk "fl_skip"
  let fl_advance := Wire.mk "fl_advance"
  let flush_finish := Wire.mk "flush_finish"
  let flush_gates :=
    [-- request latch / flush start
     Gate.mkOR fence_i fence_pending_q (Wire.mk "fence_req"),
     Gate.mkNOT miss_detect (Wire.mk "not_fl_miss"),
     Gate.mkAND is_idle (Wire.mk "not_fl_miss") (Wire.mk "flush_can_start"),
     Gate.mkAND (Wire.mk "fence_req") (Wire.mk "flush_can_start") flush_start,
     Gate.mkNOT flush_start (Wire.mk "not_flush_start"),
     Gate.mkAND (Wire.mk "fence_req") (Wire.mk "not_flush_start") fence_pending_d,
     Gate.mkDFF fence_pending_d clock reset fence_pending_q] ++
    -- sweep index decoder (one-hot over the lines), same progressive shape
    (List.range flushIdxBits).map (fun j => Gate.mkNOT flush_idx_q[j]! (Wire.mk s!"flush_nq_{j}")) ++
    List.flatten ((List.range lines).map (fun i =>
      let terms := (List.range flushIdxBits).map (fun b =>
        if (i / 2 ^ b) % 2 == 1 then flush_idx_q[b]! else Wire.mk s!"flush_nq_{b}")
      let gates := terms.foldl (fun (acc : List Gate) (t : Wire) =>
        let prev := if acc.isEmpty then t else (Wire.mk s!"flush_dt_{i}_{acc.length}")
        acc ++ [Gate.mkAND prev t (Wire.mk s!"flush_dt_{i}_{acc.length + 1}")]) []
      match gates with
      | [] => [Gate.mkBUF (Wire.mk "const_zero_l1d") flush_dec[i]!]
      | _ => gates ++ [Gate.mkBUF (Wire.mk s!"flush_dt_{i}_{gates.length}") flush_dec[i]!])) ++
    -- the sweep's way select (the high bits of the sweep index)
    List.flatten ((List.range ways).map (fun w =>
      let terms := (List.range waySelBits).map (fun b =>
        if (w / 2 ^ b) % 2 == 1 then flush_idx_q[idxBits + b]!
        else Wire.mk s!"flush_nq_{idxBits + b}")
      let gates := terms.foldl (fun (acc : List Gate) (t : Wire) =>
        let prev := if acc.isEmpty then t else (Wire.mk s!"flush_wt_{w}_{acc.length}")
        acc ++ [Gate.mkAND prev t (Wire.mk s!"flush_wt_{w}_{acc.length + 1}")]) []
      match gates with
      | [] => [Gate.mkBUF (Wire.mk "const_one_l1d") flush_way_oh[w]!]
      | _ => gates ++ [Gate.mkBUF (Wire.mk s!"flush_wt_{w}_{gates.length}") flush_way_oh[w]!])) ++
    -- per-line scan: valid AND dirty means this line needs a writeback
    (List.range lines).map (fun i => Gate.mkAND flush_dec[i]! valid_q[i]! (Wire.mk s!"fl_v_{i}")) ++
    (List.range lines).map (fun i => Gate.mkAND flush_dec[i]! dirty_q[i]! (Wire.mk s!"fl_d_{i}")) ++
    mkOrTree ((List.range lines).map (fun i => Wire.mk s!"fl_v_{i}")) (Wire.mk "fl_valid") ++
    mkOrTree ((List.range lines).map (fun i => Wire.mk s!"fl_d_{i}")) (Wire.mk "fl_dirty") ++
    [Gate.mkAND (Wire.mk "fl_valid") (Wire.mk "fl_dirty") fl_write] ++
    -- advance: FENCE_CHECK skips clean lines, FENCE_WB advances on the ack
    [Gate.mkAND is_flush_wb wb_ack fl_wb_ack,
     Gate.mkNOT fl_write (Wire.mk "not_fl_write"),
     Gate.mkAND is_flush_check (Wire.mk "not_fl_write") fl_skip,
     Gate.mkOR fl_wb_ack fl_skip fl_advance,
     Gate.mkAND fl_advance flush_dec[lines - 1]! flush_finish] ++
    -- sweep index: hold, +1 on advance, wrap to 0 on the last line
    [Gate.mkNOT flush_finish (Wire.mk "not_flush_finish")] ++
    (List.range flushIdxBits).map (fun i =>
      Gate.mkXOR flush_idx_q[i]!
        (if i == 0 then Wire.mk "const_one_l1d" else Wire.mk s!"fl_carry_{i}")
        (Wire.mk s!"fl_inc_{i}")) ++
    (List.range (flushIdxBits - 1)).map (fun i =>
      Gate.mkAND flush_idx_q[i]!
        (if i == 0 then Wire.mk "const_one_l1d" else Wire.mk s!"fl_carry_{i}")
        (Wire.mk s!"fl_carry_{i + 1}")) ++
    (List.range flushIdxBits).map (fun i =>
      Gate.mkAND (Wire.mk "not_flush_finish") (Wire.mk s!"fl_inc_{i}") (Wire.mk s!"fl_nxt_t_{i}")) ++
    (List.range flushIdxBits).map (fun i =>
      Gate.mkMUX flush_idx_q[i]! (Wire.mk s!"fl_nxt_t_{i}") fl_advance flush_idx_d[i]!) ++
    (List.range flushIdxBits).map (fun i =>
      Gate.mkDFF flush_idx_d[i]! clock reset flush_idx_q[i]!) ++
    -- dirty clear for the line just written back
    (List.range lines).map (fun i =>
      Gate.mkAND fl_wb_ack flush_dec[i]! (Wire.mk s!"flush_clr_{i}")) ++
    -- busy: the core must not redirect until the flush has finished
    [Gate.mkOR fence_i fence_pending_q (Wire.mk "fl_busy_pre"),
     Gate.mkOR (Wire.mk "fl_busy_pre") is_flush fence_i_busy]

  -- Const zero
  let const_zero_gates := [
    Gate.mkNOT reset (Wire.mk "not_reset_l1d"),
    Gate.mkAND reset (Wire.mk "not_reset_l1d") (Wire.mk "const_zero_l1d"),
    Gate.mkNOT (Wire.mk "const_zero_l1d") (Wire.mk "const_one_l1d")
  ]

  -- === Set decoder for current req_addr (for hit detection + write-hit) ===
  let set_dec := (List.range sets).map fun i => Wire.mk s!"valid_dec_w0_{i}"

  -- === Pending set decoder (for refill install) ===
  let pend_idx := (List.range idxBits).map fun i => pend_q[offsetBits + i]!
  let not_pidx := (List.range idxBits).map fun i => Wire.mk s!"not_pidx_{i}"
  let pend_dec := (List.range sets).map fun i => Wire.mk s!"pend_dec_{i}"
  let pend_dec_gates : List Gate :=
    (List.range idxBits).map (fun i => Gate.mkNOT pend_idx[i]! not_pidx[i]!) ++
    List.flatten ((List.range sets).map (fun i =>
      let terms := (List.range idxBits).map (fun b =>
        if (i / 2 ^ b) % 2 == 1 then pend_idx[b]! else not_pidx[b]!)
      match terms with
      | [] => [Gate.mkBUF (Wire.mk "const_zero_l1d") pend_dec[i]!]
      | t :: rest =>
        -- progressive AND: same shape as the hand-written 2-bit decoder
        let gates := rest.foldl (fun (acc : List Gate) (t' : Wire) =>
          let prev := if acc.isEmpty then t
                      else (Wire.mk s!"pend_dt_{i}_{acc.length}")
          acc ++ [Gate.mkAND prev t' (Wire.mk s!"pend_dt_{i}_{acc.length + 1}")]) []
        match gates with
        | [] => [Gate.mkBUF t pend_dec[i]!]
        | _ => gates ++ [Gate.mkBUF (Wire.mk s!"pend_dt_{i}_{gates.length}") pend_dec[i]!]))

  -- === Pending tag bits (from the pending address) ===
  let pend_tag := (List.range tagBits).map fun i => pend_q[offsetBits + idxBits + i]!

  -- === Victim way for the current set (one-hot), from that set's PLRU ===
  let victim_sel_gates : List Gate :=
    List.flatten ((List.range ways).map (fun w =>
      let t := (List.range sets).map (fun st => Wire.mk s!"victim_and_{st}_{w}")
      List.flatten ((List.range sets).map (fun st =>
        [Gate.mkAND (Wire.mk s!"valid_dec_w0_{st}") plru_victim[st]![w]! t[st]!]))
      ++ mkOrTree t victim_oh[w]!))

  -- === Pending victim way: one-hot registers (refill install + writeback) ===
  let pend_victim_dffs := (List.range ways).map fun w =>
    Gate.mkDFF pend_victim_d[w]! clock reset pend_victim_oh[w]!

  -- === Write-hit detection ===
  let write_hit := Wire.mk "write_hit"
  let write_hit_gates := [
    Gate.mkAND req_valid req_we (Wire.mk "wh_t1"),
    Gate.mkAND (Wire.mk "wh_t1") hit (Wire.mk "wh_t2"),
    Gate.mkAND (Wire.mk "wh_t2") is_idle write_hit
  ]

  -- === Word decoder (wordBits-to-lineWords) for write-hit ===
  let not_ws := (List.range wordBits).map fun i => Wire.mk s!"nws_{i}"
  let not_ws_gates := (List.range wordBits).map fun i => Gate.mkNOT word_sel[i]! not_ws[i]!
  let word_dec := (List.range lineWords).map fun i => Wire.mk s!"wdc_{i}"
  let word_dec_gates : List Gate := (List.range lineWords).foldl (fun acc i =>
    let terms := (List.range wordBits).map (fun b =>
      if (i / 2 ^ b) % 2 == 0 then not_ws[b]! else word_sel[b]!)
    match terms with
    | [] => acc ++ [Gate.mkBUF (Wire.mk "const_zero_l1d") word_dec[i]!]
    | t :: rest =>
      let gates := rest.foldl (fun (acc2 : List Gate) (t' : Wire) =>
        let prev := if acc2.isEmpty then t else (Wire.mk s!"wdct_{i}_{acc2.length}")
        acc2 ++ [Gate.mkAND prev t' (Wire.mk s!"wdct_{i}_{acc2.length + 1}")]) []
      match gates with
      | [] => acc ++ [Gate.mkBUF t word_dec[i]!]
      | _ => acc ++ gates ++ [Gate.mkBUF (Wire.mk s!"wdct_{i}_{gates.length}") word_dec[i]!]
  ) []

  -- === Refill + write-hit enables per way/set ===
  -- Refill uses pend_dec (pending address) and pend_victim (latched victim way)
  -- Write-hit uses set_dec (current address) and way_hit
  let refill_wh_gates := (List.range ways).foldl (fun acc way =>
    let vmatch := pend_victim_oh[way]!
    let hmatch := way_hit[way]!
    acc ++ (List.range sets).foldl (fun acc2 set =>
      acc2 ++ [
        Gate.mkAND (Wire.mk "refill_done") pend_dec[set]! (Wire.mk s!"rfs_{way}_{set}"),
        Gate.mkAND (Wire.mk s!"rfs_{way}_{set}") vmatch (Wire.mk s!"rfe_{way}_{set}"),
        Gate.mkAND write_hit set_dec[set]! (Wire.mk s!"whs_{way}_{set}"),
        Gate.mkAND (Wire.mk s!"whs_{way}_{set}") hmatch (Wire.mk s!"whe_{way}_{set}")
      ]
    ) []
  ) []

  -- === Byte-enable decode from req_size[1:0] + req_addr[1:0] ===
  -- req_size: 00=byte, 01=halfword, 10=word, 11=doubleword
  -- be_0..be_3: per-byte enables
  let not_sz := (List.range 2).map fun i => Wire.mk s!"not_sz_{i}"
  let not_ba := (List.range 2).map fun i => Wire.mk s!"not_ba_{i}"
  let be := (List.range 4).map fun i => Wire.mk s!"be_{i}"
  let is_word := Wire.mk "is_word"
  let is_dword := Wire.mk "is_dword"
  let byte_en_gates :=
    [Gate.mkNOT req_size[0]! not_sz[0]!, Gate.mkNOT req_size[1]! not_sz[1]!,
     Gate.mkNOT req_addr[0]! not_ba[0]!, Gate.mkNOT req_addr[1]! not_ba[1]!] ++
    -- is_byte = NOT sz1 AND NOT sz0;  is_half = NOT sz1 AND sz0;  is_word = sz1 AND NOT sz0; is_dword = sz1 AND sz0
    [Gate.mkAND not_sz[1]! not_sz[0]! (Wire.mk "is_byte"),
     Gate.mkAND not_sz[1]! req_size[0]! (Wire.mk "is_half"),
     Gate.mkAND req_size[1]! not_sz[0]! is_word,
     Gate.mkAND req_size[1]! req_size[0]! is_dword,
     -- be_0: byte AND ba==00, OR half AND ba1==0, OR word
     Gate.mkAND (Wire.mk "is_byte") not_ba[1]! (Wire.mk "be0_bt"),
     Gate.mkAND (Wire.mk "be0_bt") not_ba[0]! (Wire.mk "be0_b"),
     Gate.mkAND (Wire.mk "is_half") not_ba[1]! (Wire.mk "be0_h"),
     Gate.mkOR (Wire.mk "be0_b") (Wire.mk "be0_h") (Wire.mk "be0_bh"),
     Gate.mkOR (Wire.mk "be0_bh") is_word be[0]!,
     -- be_1: byte AND ba==01, OR half AND ba1==0, OR word
     Gate.mkAND (Wire.mk "is_byte") not_ba[1]! (Wire.mk "be1_bt"),
     Gate.mkAND (Wire.mk "be1_bt") req_addr[0]! (Wire.mk "be1_b"),
     Gate.mkOR (Wire.mk "be1_b") (Wire.mk "be0_h") (Wire.mk "be1_bh"),
     Gate.mkOR (Wire.mk "be1_bh") is_word be[1]!,
     -- be_2: byte AND ba==10, OR half AND ba1==1, OR word
     Gate.mkAND (Wire.mk "is_byte") req_addr[1]! (Wire.mk "be2_bt"),
     Gate.mkAND (Wire.mk "be2_bt") not_ba[0]! (Wire.mk "be2_b"),
     Gate.mkAND (Wire.mk "is_half") req_addr[1]! (Wire.mk "be2_h"),
     Gate.mkOR (Wire.mk "be2_b") (Wire.mk "be2_h") (Wire.mk "be2_bh"),
     Gate.mkOR (Wire.mk "be2_bh") is_word be[2]!,
     -- be_3: byte AND ba==11, OR half AND ba1==1, OR word
     Gate.mkAND (Wire.mk "be2_bt") req_addr[0]! (Wire.mk "be3_b"),
     Gate.mkOR (Wire.mk "be3_b") (Wire.mk "be2_h") (Wire.mk "be3_bh"),
     Gate.mkOR (Wire.mk "be3_bh") is_word be[3]!]

  -- === Shifted write data: replicate store data to correct byte lanes ===
  let wdata_shifted := (List.range 32).map fun i => Wire.mk s!"wds_{i}"
  let wdata_shift_gates :=
    -- Byte 0: passthrough
    (List.range 8).map (fun i =>
      Gate.mkBUF req_wdata[i]! wdata_shifted[i]!) ++
    -- Byte 1: MUX(req_wdata[15:8], req_wdata[7:0], is_byte)
    (List.range 8).map (fun i =>
      Gate.mkMUX req_wdata[8+i]! req_wdata[i]! (Wire.mk "is_byte") wdata_shifted[8+i]!) ++
    -- Byte 2: MUX(req_wdata[7:0], req_wdata[23:16], is_word)
    (List.range 8).map (fun i =>
      Gate.mkMUX req_wdata[i]! req_wdata[16+i]! is_word wdata_shifted[16+i]!) ++
    -- Byte 3: first MUX byte vs half source, then word override
    (List.range 8).map (fun i =>
      Gate.mkMUX req_wdata[8+i]! req_wdata[i]! (Wire.mk "is_byte") (Wire.mk s!"wds3t_{i}")) ++
    (List.range 8).map (fun i =>
      Gate.mkMUX (Wire.mk s!"wds3t_{i}") req_wdata[24+i]! is_word wdata_shifted[24+i]!)

  -- doubleword decoder for 64-bit store write enables
  let dword_dec := (List.range (lineWords / 2)).map fun i => Wire.mk s!"dwdc_{i}"
  let dword_dec_gates := (List.range (lineWords / 2)).map fun i =>
    Gate.mkOR word_dec[2 * i]! word_dec[2 * i + 1]! dword_dec[i]!

  -- === FSM next-state ===
  -- IDLE(000) → WRITEBACK(010) on miss_detect AND victim_needs_wb
  -- IDLE(000) → REFILL_WAIT(001) on miss_detect AND NOT victim_needs_wb
  -- WRITEBACK(010) → REFILL_WAIT(001) on wb_ack
  -- WRITEBACK(010) → WRITEBACK(010) if NOT wb_ack (L2 busy)
  -- REFILL_WAIT(001) → IDLE(000) on refill_valid, else stay
  let is_refill_wait := Wire.mk "is_refill_wait"
  let refill_done := Wire.mk "refill_done"
  let not_refill_valid := Wire.mk "not_refill_valid"
  let not_victim_wb := Wire.mk "not_victim_wb"
  let not_wb_ack := Wire.mk "not_wb_ack"
  let fsm_next_gates := [
    Gate.mkAND fsm_q[0]! (Wire.mk "not_fsm_1") (Wire.mk "rw_01"),
    Gate.mkAND (Wire.mk "rw_01") (Wire.mk "not_fsm_2") is_refill_wait,
    Gate.mkAND is_refill_wait refill_valid refill_done,
    Gate.mkNOT refill_valid not_refill_valid,
    Gate.mkAND is_refill_wait not_refill_valid (Wire.mk "stay_rw"),
    -- miss_detect branches
    Gate.mkNOT (Wire.mk "victim_needs_wb") not_victim_wb,
    Gate.mkAND miss_detect not_victim_wb (Wire.mk "go_rw_direct"),
    Gate.mkAND miss_detect (Wire.mk "victim_needs_wb") (Wire.mk "go_wb"),
    -- WRITEBACK transitions
    Gate.mkNOT wb_ack not_wb_ack,
    Gate.mkAND is_writeback wb_ack (Wire.mk "wb_to_rw"),
    Gate.mkAND is_writeback not_wb_ack (Wire.mk "stay_wb"),
    -- fsm_d[0] = go_rw_direct OR stay_rw OR wb_to_rw
    Gate.mkOR (Wire.mk "go_rw_direct") (Wire.mk "stay_rw") (Wire.mk "fsm0_t1"),
    Gate.mkOR (Wire.mk "fsm0_t1") (Wire.mk "wb_to_rw") (Wire.mk "fsm0_base"),
    -- fence.i flush: FENCE_CHECK → FENCE_WB when the line needs a writeback,
    -- FENCE_WB stays until wb_ack
    Gate.mkAND is_flush_check fl_write (Wire.mk "fl_to_wb"),
    Gate.mkNOT fl_advance (Wire.mk "not_fl_advance"),
    Gate.mkAND is_flush_wb (Wire.mk "not_fl_advance") (Wire.mk "fl_stay_wb"),
    Gate.mkOR (Wire.mk "fsm0_base") (Wire.mk "fl_to_wb") (Wire.mk "fsm0_t2"),
    Gate.mkOR (Wire.mk "fsm0_t2") (Wire.mk "fl_stay_wb") fsm_d[0]!,
    -- fsm_d[1] = go_wb OR stay_wb
    Gate.mkOR (Wire.mk "go_wb") (Wire.mk "stay_wb") fsm_d[1]!,
    -- fsm_d[2] = fence.i flush in progress (enter FENCE_CHECK, leave on the last line)
    Gate.mkOR flush_start is_flush (Wire.mk "fsm2_t1"),
    Gate.mkNOT flush_finish (Wire.mk "not_flush_finish2"),
    Gate.mkAND (Wire.mk "fsm2_t1") (Wire.mk "not_flush_finish2") fsm_d[2]!
  ]
  -- Note: NOT gates for fsm_q[1], fsm_q[2] already exist in fsm_decode_gates

  -- === Pending address capture: MUX(hold, req_addr, miss_detect) ===
  -- During the flush sweep, pend_q[6:5] carries the line index being flushed
  -- (the tag read and the data RAM read are addressed from it, exactly as the
  -- eviction writeback uses the miss index).
  let pend_capture_gates : List Gate := List.flatten ((List.range 32).map (fun i =>
    if i ≥ offsetBits && i < offsetBits + idxBits then
      let j := i - offsetBits
      [Gate.mkMUX pend_q[i]! req_addr[i]! miss_detect (Wire.mk s!"pend_dx_{i}"),
       Gate.mkMUX (Wire.mk s!"pend_dx_{i}") flush_idx_q[j]! is_flush pend_d[i]!]
    else
      [Gate.mkMUX pend_q[i]! req_addr[i]! miss_detect pend_d[i]!]))

  -- === Pending victim capture (one-hot): the miss's PLRU victim, or the way
  -- the fence.i sweep is currently on ===
  let pend_victim_gates : List Gate :=
    List.flatten ((List.range ways).map (fun w =>
      [Gate.mkMUX pend_victim_oh[w]! victim_oh[w]! miss_detect (Wire.mk s!"pend_victim_dx_{w}"),
       Gate.mkMUX (Wire.mk s!"pend_victim_dx_{w}") (Wire.mk s!"flush_way_oh_{w}") is_flush
         pend_victim_d[w]!]))

  -- === Tag next: MUX(hold, pend_tag, refill_en) ===
  -- Use pend_tag (from pending address) for refill tag installation
  let tag_next_gates := (List.range ways).foldl (fun acc way =>
    acc ++ (List.range sets).foldl (fun acc2 set =>
      acc2 ++ (List.range tagBits).map (fun b =>
        Gate.mkMUX (Wire.mk s!"tag_q_w{way}_s{set}_{b}") pend_tag[b]!
          (Wire.mk s!"rfe_{way}_{set}") (Wire.mk s!"tag_d_w{way}_s{set}_{b}"))
    ) []
  ) []

  -- === Data RAM write logic ===
  -- Per-way: write_en, write_addr, write_data
  -- refill_for_way = refill_valid AND (way matches pend_victim)
  -- write_hit_for_way = write_hit AND way_hit[way]
  let data_ram_ctl_gates : List Gate :=
    List.flatten ((List.range ways).map (fun way =>
      [Gate.mkAND (Wire.mk "refill_done") pend_victim_oh[way]! (Wire.mk s!"ram_refill_w{way}"),
       Gate.mkAND (Wire.mk "write_hit") way_hit[way]! (Wire.mk s!"ram_wh_w{way}"),
       Gate.mkOR (Wire.mk s!"ram_refill_w{way}") (Wire.mk s!"ram_wh_w{way}") data_ram_wr_en[way]!]))
  -- Write address: refill uses pend_idx, write-hit uses idx_bits
  -- Since refill and write-hit are mutually exclusive, MUX on refill_done
  let data_ram_addr_gates := (List.range ways).foldl (fun acc way =>
    acc ++ (List.range idxBits).map (fun i =>
      Gate.mkMUX idx_bits[i]! pend_idx[i]! (Wire.mk "refill_done") (data_ram_wr_addr[way]!)[i]!)
  ) []
  -- Write data: refill uses refill_data, write-hit uses merge(ram_rd, wdata_shifted)
  -- Merge logic: for each bit, MUX(ram_rd[b], wdata_shifted[b%32], write_hit_byte_en)
  -- write_hit_byte_en for bit b = word_dec[b/32] AND be[(b%32)/8]
  -- Note: word_dec and be are already computed (shared across ways)
  let data_ram_merge_gates := (List.range ways).foldl (fun acc way =>
    acc ++ (List.range lineBits).foldl (fun acc2 b =>
      let wd := b / 32
      let dw := b / 64
      let bb32 := b % 32
      let bb64 := b % 64
      let byte := bb32 / 8
      acc2 ++ [
        Gate.mkAND word_dec[wd]! be[byte]! (Wire.mk s!"ram_be_base_w{way}_{b}"),
        Gate.mkMUX (Wire.mk s!"ram_be_base_w{way}_{b}") dword_dec[dw]! is_dword (Wire.mk s!"ram_be_w{way}_{b}"),
        Gate.mkMUX wdata_shifted[bb32]! req_wdata[bb64]! is_dword (Wire.mk s!"wr_data_w{way}_{b}"),
        Gate.mkMUX (data_ram_rd[way]!)[b]! (Wire.mk s!"wr_data_w{way}_{b}")
          (Wire.mk s!"ram_be_w{way}_{b}") (Wire.mk s!"ram_merged_w{way}_{b}"),
        -- Final write data: MUX(merged, refill_data, refill_done)
        Gate.mkMUX (Wire.mk s!"ram_merged_w{way}_{b}") refill_data[b]!
          (Wire.mk "refill_done") (data_ram_wr_data[way]!)[b]!
      ]
    ) []
  ) []

  -- === Valid next: set on refill (rfe uses pend_dec already) ===
  let valid_next_gates := (List.range ways).foldl (fun acc way =>
    acc ++ (List.range sets).map (fun set =>
      Gate.mkOR valid_q[way * sets + set]! (Wire.mk s!"rfe_{way}_{set}") valid_d[way * sets + set]!)
  ) []

  -- === Dirty next: set on write-hit, clear on refill, hold otherwise ===
  let dirty_next_gates := (List.range ways).foldl (fun acc way =>
    acc ++ (List.range sets).foldl (fun acc2 set =>
      let idx := way * sets + set
      acc2 ++ [
        Gate.mkNOT (Wire.mk s!"rfe_{way}_{set}") (Wire.mk s!"nrfe_{way}_{set}"),
        Gate.mkAND dirty_q[idx]! (Wire.mk s!"nrfe_{way}_{set}") (Wire.mk s!"dh_{way}_{set}"),
        Gate.mkOR (Wire.mk s!"dh_{way}_{set}") (Wire.mk s!"whe_{way}_{set}") (Wire.mk s!"dirty_pre_{idx}"),
        -- a fence.i writeback clears the line's dirty bit
        Gate.mkNOT (Wire.mk s!"flush_clr_{idx}") (Wire.mk s!"nflush_clr_{idx}"),
        Gate.mkAND (Wire.mk s!"dirty_pre_{idx}") (Wire.mk s!"nflush_clr_{idx}") dirty_d[idx]!
      ]
    ) []
  ) []

  let allGates :=
    fsm_gates ++ pend_dffs ++ pend_victim_dffs ++ plru_gates ++ valid_dffs ++ dirty_dffs ++
    data_ram_rd_addr_mux ++
    valid_mux_gates ++ dirty_mux_gates ++ victim_wb_gates ++
    hit_gates ++ [hit_gate] ++
    hit_data_mux_gates ++ resp_data_mux_gates ++ fsm_decode_gates ++ resp_valid_gates ++ resp_reg_gates ++
    miss_gates ++ miss_valid_gates ++ miss_addr_gates ++ stall_gates ++
    [wb_valid_gate] ++ wb_vtag_mux ++ wb_addr_gates ++ wb_data_gates ++ flush_gates ++
    const_zero_gates ++
    pend_dec_gates ++
    write_hit_gates ++ not_ws_gates ++ word_dec_gates ++ dword_dec_gates ++
    refill_wh_gates ++ byte_en_gates ++ wdata_shift_gates ++
    fsm_next_gates ++ pend_capture_gates ++ pend_victim_gates ++
    tag_next_gates ++ data_ram_ctl_gates ++ data_ram_addr_gates ++ data_ram_merge_gates ++
    valid_next_gates ++ dirty_next_gates ++ victim_sel_gates

  let allInstances :=
    tag_instances ++
    tag_mux_instances ++ tag_cmp_instances ++
    data_word_mux_instances ++ data_dwhi_mux_instances ++
    [refill_word_mux_inst, refill_dwhi_mux_inst] ++
    plru_insts ++ valid_dec_insts

  { name := s!"L1DCache{g.nameSuffix}"
    inputs := [clock, reset, req_valid, req_we] ++ req_addr ++ req_wdata ++ req_size ++
              [refill_valid] ++ refill_data ++ [wb_ack, fence_i]
    outputs := [resp_valid] ++ resp_data ++ [miss_valid] ++ miss_addr ++
               [wb_valid] ++ wb_addr ++ wb_data ++ [stall, fence_i_busy]
    gates := allGates
    instances := allInstances
    rams := data_rams
    signalGroups := [
      { name := "req_addr", width := 32, wires := req_addr },
      { name := "req_wdata", width := 64, wires := req_wdata },
      { name := "req_size", width := 2, wires := req_size },
      { name := "refill_data", width := lineBits, wires := refill_data },
      { name := "resp_data", width := 64, wires := resp_data },
      { name := "miss_addr", width := 32, wires := miss_addr },
      { name := "wb_addr", width := 32, wires := wb_addr },
      { name := "wb_data", width := lineBits, wires := wb_data }
    ]
  }

end Shoumei.RISCV.Memory.Cache

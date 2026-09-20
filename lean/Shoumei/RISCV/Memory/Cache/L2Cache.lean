/-
RISCV/Memory/Cache/L2Cache.lean - Shared L2 Cache

2-way set-associative, 8-set, 32B line, shared between L1I and L1D.
Behavioral model + structural circuit.

D-side requests have priority over I-side.
On L2 miss: sends request to main memory.
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

/-- Build the L2 cache structural circuit for a geometry.

    FSM states:
    - IDLE (000): Arbitrate requests, check hit
    - HIT_LATCH (001): Hit detected, latching data read (1-cycle delay)
    - HIT_RESP (010): Respond with stored data
    - MEM_REQ (011): Send read request to main memory
    - MEM_WAIT (100): Wait for memory response, then respond + install
    - WRITEBACK (101): Write dirty victim back to memory
    - WB_COMMIT (110): Complete an L1D writeback

    Ports:
    - Inputs: clock, reset,
              l1i_req_valid, l1i_req_addr[31:0],
              l1d_req_valid, l1d_req_addr[31:0], l1d_req_we, l1d_req_data[lineBits-1:0],
              mem_resp_valid, mem_resp_data[lineBits-1:0]
    - Outputs: l1i_resp_valid, l1i_resp_data[lineBits-1:0],
               l1d_resp_valid, l1d_resp_data[lineBits-1:0],
               mem_req_valid, mem_req_addr[31:0], mem_req_we, mem_req_data[lineBits-1:0],
               stall_i, stall_d

    Everything geometry-dependent (tag width, set and way counts, line width, set
    decoders, tag muxes/comparators, the replacement policy) follows `CacheGeom`;
    the default geometry keeps the historical shape and module name.
-/
def mkL2Cache (g : CacheGeom := CacheGeom.default) : Circuit :=
  -- === Geometry ===
  let sets := g.l2Sets
  let ways := g.l2Ways
  let lineBits := g.lineBytes * 8
  let offsetBits := log2Ceil g.lineBytes
  let idxBits := log2Ceil sets
  let tagBits := 32 - idxBits - offsetBits
  let lines := ways * sets

  -- === Port Wires ===
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let l1i_req_valid := Wire.mk "l1i_req_valid"
  let l1i_req_addr := (List.range 32).map fun i => Wire.mk s!"l1i_req_addr_{i}"
  let l1i_resp_valid := Wire.mk "l1i_resp_valid"
  let l1i_resp_data := (List.range lineBits).map fun i => Wire.mk s!"l1i_resp_data_{i}"
  let l1d_req_valid := Wire.mk "l1d_req_valid"
  let l1d_req_addr := (List.range 32).map fun i => Wire.mk s!"l1d_req_addr_{i}"
  let l1d_req_we := Wire.mk "l1d_req_we"
  let l1d_req_data := (List.range lineBits).map fun i => Wire.mk s!"l1d_req_data_{i}"
  let l1d_resp_valid := Wire.mk "l1d_resp_valid"
  let l1d_resp_data := (List.range lineBits).map fun i => Wire.mk s!"l1d_resp_data_{i}"
  let mem_resp_valid := Wire.mk "mem_resp_valid"
  let mem_resp_data := (List.range lineBits).map fun i => Wire.mk s!"mem_resp_data_{i}"
  let mem_req_valid := Wire.mk "mem_req_valid"
  let mem_req_addr := (List.range 32).map fun i => Wire.mk s!"mem_req_addr_{i}"
  let mem_req_we := Wire.mk "mem_req_we"
  let mem_req_data := (List.range lineBits).map fun i => Wire.mk s!"mem_req_data_{i}"
  let stall_i := Wire.mk "stall_i"
  let stall_d := Wire.mk "stall_d"

  -- === State Registers ===
  -- FSM: 3-bit (IDLE=000, HIT_LATCH=001, HIT_RESP=010, MEM_REQ=011, MEM_WAIT=100,
  -- WRITEBACK=101, WB_COMMIT=110)
  let fsm_d := (List.range 3).map fun i => Wire.mk s!"l2_fsm_d_{i}"
  let fsm_q := (List.range 3).map fun i => Wire.mk s!"l2_fsm_q_{i}"
  let fsm_dffs := (List.range 3).map fun i => Gate.mkDFF fsm_d[i]! clock reset fsm_q[i]!

  -- Source: 1-bit (0=ICache, 1=DCache)
  let src_d := Wire.mk "src_d"
  let src_q := Wire.mk "src_q"
  let src_dff := Gate.mkDFF src_d clock reset src_q

  -- Pending address: 32-bit
  let pend_d := (List.range 32).map fun i => Wire.mk s!"pend_d_{i}"
  let pend_q := (List.range 32).map fun i => Wire.mk s!"pend_q_{i}"
  let pend_dffs := (List.range 32).map fun i => Gate.mkDFF pend_d[i]! clock reset pend_q[i]!

  -- Latched index (for hit data readback in HIT_LATCH/HIT_RESP)
  let lat_idx_d := (List.range idxBits).map fun i => Wire.mk s!"lat_idx_d_{i}"
  let lat_idx_q := (List.range idxBits).map fun i => Wire.mk s!"lat_idx_q_{i}"
  let lat_idx_dffs := (List.range idxBits).map fun i => Gate.mkDFF lat_idx_d[i]! clock reset lat_idx_q[i]!

  -- Latched hit way: one-hot (which way hit, for readback)
  let lat_way_d := (List.range ways).map fun w => Wire.mk s!"lat_way_d_{w}"
  let lat_way_q := (List.range ways).map fun w => Wire.mk s!"lat_way_q_{w}"
  let lat_way_dffs := (List.range ways).map fun w => Gate.mkDFF lat_way_d[w]! clock reset lat_way_q[w]!

  -- Pending-is-wb flag: tracks if WRITEBACK was triggered by L1D wb (vs read miss)
  let pend_is_wb_d := Wire.mk "l2_piwb_d"
  let pend_is_wb_q := Wire.mk "l2_piwb_q"
  let pend_is_wb_dff := Gate.mkDFF pend_is_wb_d clock reset pend_is_wb_q

  -- Tag storage: ways × sets × tagBits
  let tag_instances := (List.range ways).foldl (fun acc way =>
    acc ++ (List.range sets).map (fun set =>
      CircuitInstance.mk s!"Register{tagBits}" s!"u_l2_tag_w{way}_s{set}"
        ((List.range tagBits).map (fun b => (s!"d_{b}", Wire.mk s!"l2_tag_d_w{way}_s{set}_{b}")) ++
         [("clock", clock), ("reset", reset)] ++
         (List.range tagBits).map (fun b => (s!"q_{b}", Wire.mk s!"l2_tag_q_w{way}_s{set}_{b}"))))
  ) []

  -- Valid bits: one per line (ways × sets)
  let valid_d := (List.range lines).map fun i => Wire.mk s!"l2_valid_d_{i}"
  let valid_q := (List.range lines).map fun i => Wire.mk s!"l2_valid_q_{i}"
  let valid_dffs := (List.range lines).map fun i => Gate.mkDFF valid_d[i]! clock reset valid_q[i]!

  -- Dirty bits: one per line
  let dirty_d := (List.range lines).map fun i => Wire.mk s!"l2_dirty_d_{i}"
  let dirty_q := (List.range lines).map fun i => Wire.mk s!"l2_dirty_q_{i}"
  let dirty_dffs := (List.range lines).map fun i => Gate.mkDFF dirty_d[i]! clock reset dirty_q[i]!

  -- Replacement: one tree-PLRU per set (the old single LRU bit per set is exactly
  -- its two-way case), plus the one-hot victim of the set being evicted
  let pend_victim_d := (List.range ways).map fun w => Wire.mk s!"l2_pvict_d_{w}"
  let pend_victim_q := (List.range ways).map fun w => Wire.mk s!"l2_pvict_q_{w}"
  let pend_victim_dffs := (List.range ways).map fun w =>
    Gate.mkDFF pend_victim_d[w]! clock reset pend_victim_q[w]!

  -- Pending victim tag: captures the victim's tag on evict_trigger
  let pend_vtag_d := (List.range tagBits).map fun b => Wire.mk s!"l2_pvtag_d_{b}"
  let pend_vtag_q := (List.range tagBits).map fun b => Wire.mk s!"l2_pvtag_q_{b}"
  let pend_vtag_dffs := (List.range tagBits).map fun b =>
    Gate.mkDFF pend_vtag_d[b]! clock reset pend_vtag_q[b]!

  -- Data RAM wire declarations (RAMs defined later after read_idx is available)
  let l2_data_ram_rd := (List.range ways).map fun way =>
    (List.range lineBits).map fun b => Wire.mk s!"drd{way}_{b}"
  let l2_data_ram_wr_en := (List.range ways).map fun way => Wire.mk s!"l2_dwr_en_w{way}"
  let l2_data_ram_wr_addr := (List.range ways).map fun way =>
    (List.range idxBits).map fun i => Wire.mk s!"l2_dwr_addr_w{way}_{i}"
  let l2_data_ram_wr_data := (List.range ways).map fun way =>
    (List.range lineBits).map fun b => Wire.mk s!"l2_dwr_data_w{way}_{b}"

  -- === Constants ===
  let const_zero_gates := [
    Gate.mkNOT reset (Wire.mk "l2_not_reset"),
    Gate.mkAND reset (Wire.mk "l2_not_reset") (Wire.mk "l2_const_zero"),
    Gate.mkNOT (Wire.mk "l2_const_zero") (Wire.mk "l2_const_one")
  ]

  -- === Request Arbitration ===
  -- D-side has priority: arb_sel_d = l1d_req_valid OR l1d_req_we
  let arb_sel_d := Wire.mk "arb_sel_d"
  let arb_valid := Wire.mk "arb_valid"
  let arb_is_write := Wire.mk "arb_is_write"
  let arb_gates := [
    Gate.mkOR l1d_req_valid l1d_req_we arb_sel_d,
    Gate.mkOR l1d_req_valid l1i_req_valid (Wire.mk "arb_v_tmp"),
    Gate.mkOR (Wire.mk "arb_v_tmp") l1d_req_we arb_valid,
    Gate.mkBUF l1d_req_we arb_is_write
  ]

  -- Arbitrated address: arb_sel_d ? l1d : l1i
  let arb_addr := (List.range 32).map fun i => Wire.mk s!"arb_addr_{i}"
  let arb_addr_mux := (List.range 32).map fun i =>
    Gate.mkMUX l1i_req_addr[i]! l1d_req_addr[i]! arb_sel_d arb_addr[i]!

  -- === Address Decomposition ===
  -- Current request: idx = arb_addr[offsetBits+idxBits-1:offsetBits], tag above it
  let cur_idx := (List.range idxBits).map fun i => arb_addr[offsetBits + i]!
  let cur_tag := (List.range tagBits).map fun i => arb_addr[offsetBits + idxBits + i]!
  -- Refill/pending: the same slices of the pending address
  let ref_idx := (List.range idxBits).map fun i => pend_q[offsetBits + i]!
  let ref_tag := (List.range tagBits).map fun i => pend_q[offsetBits + idxBits + i]!

  -- === Index Decoders ===
  let cur_dec := (List.range sets).map fun i => Wire.mk s!"cd_{i}"
  let cur_dec_inst := CircuitInstance.mk s!"Decoder{idxBits}" "u_l2_cur_dec"
    ((List.range idxBits).map (fun i => (s!"in_{i}", cur_idx[i]!)) ++
     (List.range sets).map (fun i => (s!"out_{i}", cur_dec[i]!)))
  let ref_dec := (List.range sets).map fun i => Wire.mk s!"rd_{i}"
  let ref_dec_inst := CircuitInstance.mk s!"Decoder{idxBits}" "u_l2_ref_dec"
    ((List.range idxBits).map (fun i => (s!"in_{i}", ref_idx[i]!)) ++
     (List.range sets).map (fun i => (s!"out_{i}", ref_dec[i]!)))

  -- === Read Index Mux ===
  -- During IDLE: use cur_idx. During WRITEBACK: use ref_idx (for victim data read).
  -- Otherwise (HIT_LATCH/HIT_RESP): use lat_idx_q.
  let not_idle := Wire.mk "l2_not_idle"  -- computed in FSM decode below, declared here
  let is_writeback_fwd := Wire.mk "l2_is_wb"  -- forward ref, driven by FSM decode
  let read_idx := (List.range idxBits).map fun i => Wire.mk s!"ridx_{i}"
  let read_idx_inner := (List.range idxBits).map fun i => Wire.mk s!"ridx_i_{i}"
  let read_idx_mux :=
    (List.range idxBits).map (fun i =>
      Gate.mkMUX lat_idx_q[i]! ref_idx[i]! is_writeback_fwd read_idx_inner[i]!) ++
    (List.range idxBits).map (fun i =>
      Gate.mkMUX cur_idx[i]! read_idx_inner[i]! not_idle read_idx[i]!)

  -- === Tag Lookup ===
  -- Per way: Mux{sets}x{tagBits} to select the tag of the indexed set, then compare
  let way_sel_tag := (List.range ways).map fun w =>
    (List.range tagBits).map fun b => Wire.mk s!"wst{w}_{b}"
  let tag_mux_instances := (List.range ways).map fun way =>
    CircuitInstance.mk s!"Mux{sets}x{tagBits}" s!"u_l2_tag_mux_w{way}"
      ((List.range sets).foldl (fun acc set =>
        acc ++ (List.range tagBits).map (fun b =>
          (s!"in{set}_{b}", Wire.mk s!"l2_tag_q_w{way}_s{set}_{b}"))
      ) [] ++
      (List.range idxBits).map (fun i => (s!"sel_{i}", cur_idx[i]!)) ++
      (List.range tagBits).map (fun b => (s!"out_{b}", (way_sel_tag[way]!)[b]!)))
  let way_tag_match := (List.range ways).map fun w => Wire.mk s!"wtm{w}"
  let tag_cmp_instances := (List.range ways).map fun way =>
    CircuitInstance.mk s!"EqualityComparator{tagBits}" s!"u_l2_cmp_w{way}"
      ((List.range tagBits).map (fun b => (s!"a_{b}", (way_sel_tag[way]!)[b]!)) ++
       (List.range tagBits).map (fun b => (s!"b_{b}", cur_tag[b]!)) ++
       [("eq", way_tag_match[way]!)])

  -- === Valid Bit Lookup ===
  -- Per way: OR over sets of (set select AND that line's valid). Layout: valid_q[way*sets+set]
  let way_valid_sel := (List.range ways).map fun w => Wire.mk s!"wvs{w}"
  let valid_mux_gates : List Gate := List.flatten ((List.range ways).map fun way =>
    let t := (List.range sets).map (fun st => Wire.mk s!"va{way}_{st}")
    List.flatten ((List.range sets).map fun st =>
      [Gate.mkAND cur_dec[st]! valid_q[way * sets + st]! t[st]!])
    ++ mkOrTree t way_valid_sel[way]!)

  -- === Hit Detection ===
  let way_hit := (List.range ways).map fun w => Wire.mk s!"wh{w}"
  let hit := Wire.mk "l2_hit"
  let hit_gates : List Gate :=
    (List.range ways).map (fun w => Gate.mkAND way_valid_sel[w]! way_tag_match[w]! way_hit[w]!) ++
    mkOrTree way_hit hit

  -- === Replacement Victim Lookup ===
  -- One tree-PLRU per set; the victim of the requested set and of the refill set
  -- are one-hot selects muxed out of the per-set PLRUs.
  let plru_victim := (List.range sets).map fun st =>
    (List.range ways).map fun w => Wire.mk s!"l2_plru_victim_{st}_{w}"
  let plru_upd_en := (List.range sets).map fun st => Wire.mk s!"l2_plru_en_{st}"
  let plru_upd_way := (List.range sets).map fun st =>
    (List.range ways).map fun w => Wire.mk s!"l2_plru_w_{st}_{w}"
  let cur_victim := (List.range ways).map fun w => Wire.mk s!"cv{w}"
  let ref_victim := (List.range ways).map fun w => Wire.mk s!"rv{w}"
  let pickVictim (dec : List Wire) (out : List Wire) : List Gate :=
    if ways == 1 then
      [Gate.mkBUF (Wire.mk "l2_const_one") out[0]!]
    else List.flatten ((List.range ways).map fun w =>
      let t := (List.range sets).map (fun st => Wire.mk s!"{out[w]!.name}_and_{st}")
      List.flatten ((List.range sets).map fun st =>
        [Gate.mkAND dec[st]! plru_victim[st]![w]! t[st]!])
      ++ mkOrTree t out[w]!)
  -- Update source: the set is touched by a read hit or a writeback (current set)
  -- and by a refill (refill set); the two never touch the same set at once.
  let plru_gates : List Gate :=
    (List.range sets).map (fun st => Gate.mkAND (Wire.mk "l2_access_evt") cur_dec[st]!
      (Wire.mk s!"l2_plru_acc_{st}")) ++
    (List.range sets).map (fun st => Gate.mkAND (Wire.mk "l2_rd") ref_dec[st]!
      (Wire.mk s!"l2_plru_rf_{st}")) ++
    (List.range sets).map (fun st =>
      Gate.mkOR (Wire.mk s!"l2_plru_acc_{st}") (Wire.mk s!"l2_plru_rf_{st}") plru_upd_en[st]!) ++
    List.flatten ((List.range sets).map (fun st =>
      List.flatten ((List.range ways).map fun w =>
        [Gate.mkAND (Wire.mk s!"l2_plru_acc_{st}") (Wire.mk s!"wbw{w}")
           (Wire.mk s!"l2_plru_aw_{st}_{w}"),
         Gate.mkAND (Wire.mk s!"l2_plru_rf_{st}") (Wire.mk s!"rv{w}")
           (Wire.mk s!"l2_plru_rw_{st}_{w}"),
         Gate.mkOR (Wire.mk s!"l2_plru_aw_{st}_{w}") (Wire.mk s!"l2_plru_rw_{st}_{w}")
           plru_upd_way[st]![w]!])))
  let plru_insts : List CircuitInstance :=
    if ways < 2 then []
    else (List.range sets).map (fun st =>
      CircuitInstance.mk s!"PLRU{ways}" s!"u_l2_plru_s{st}"
        ([("clock", clock), ("reset", reset), ("zero", Wire.mk "l2_const_zero"),
          ("one", Wire.mk "l2_const_one"), ("upd_en", plru_upd_en[st]!)] ++
         (List.range ways).map (fun w => (s!"upd_way_oh_{w}", plru_upd_way[st]![w]!)) ++
         (List.range ways).map (fun w => (s!"victim_oh_{w}", plru_victim[st]![w]!))))

  -- === Data Read Path ===
  -- RAM read ports provide drd{way}_{b} directly.  Way select: the request's
  -- victim way while idle, the latched hit way afterwards.
  let read_way := (List.range ways).map fun w => Wire.mk s!"rway{w}"
  let read_way_mux := (List.range ways).map fun w =>
    Gate.mkMUX cur_victim[w]! lat_way_q[w]! not_idle read_way[w]!
  let way_data_mux : List Gate := List.flatten ((List.range lineBits).map fun b =>
    let t := (List.range ways).map (fun w => Wire.mk s!"wsd_a{w}_{b}")
    List.flatten ((List.range ways).map fun w =>
      [Gate.mkAND read_way[w]! (l2_data_ram_rd[w]!)[b]! t[w]!])
    ++ mkOrTree t (Wire.mk s!"wsd_{b}"))

  -- === FSM Decode ===
  let not_fsm := (List.range 3).map fun i => Wire.mk s!"l2nf{i}"
  let is_idle := Wire.mk "l2_is_idle"
  let is_hit_latch := Wire.mk "l2_is_hl"
  let is_hit_resp := Wire.mk "l2_is_hr"
  let is_mem_req := Wire.mk "l2_is_mr"
  let is_mem_wait := Wire.mk "l2_is_mw"
  let is_writeback := Wire.mk "l2_is_wb"
  let is_wb_commit := Wire.mk "l2_is_wc"
  let fsm_decode_gates :=
    (List.range 3).map (fun i => Gate.mkNOT fsm_q[i]! not_fsm[i]!) ++
    [Gate.mkAND not_fsm[0]! not_fsm[1]! (Wire.mk "l2f01n"),
     Gate.mkAND (Wire.mk "l2f01n") not_fsm[2]! is_idle,            -- 000
     Gate.mkAND fsm_q[0]! not_fsm[1]! (Wire.mk "l2f01h"),
     Gate.mkAND (Wire.mk "l2f01h") not_fsm[2]! is_hit_latch,      -- 001
     Gate.mkAND not_fsm[0]! fsm_q[1]! (Wire.mk "l2f01r"),
     Gate.mkAND (Wire.mk "l2f01r") not_fsm[2]! is_hit_resp,       -- 010
     Gate.mkAND fsm_q[0]! fsm_q[1]! (Wire.mk "l2f01m"),
     Gate.mkAND (Wire.mk "l2f01m") not_fsm[2]! is_mem_req,        -- 011
     Gate.mkAND not_fsm[0]! not_fsm[1]! (Wire.mk "l2f01w"),
     Gate.mkAND (Wire.mk "l2f01w") fsm_q[2]! is_mem_wait,         -- 100
     Gate.mkAND (Wire.mk "l2f01h") fsm_q[2]! is_writeback,       -- 101
     Gate.mkAND (Wire.mk "l2f01r") fsm_q[2]! is_wb_commit,      -- 110
     Gate.mkNOT is_idle not_idle]

  -- === Detection Logic ===
  let not_hit := Wire.mk "l2_nh"
  let not_write := Wire.mk "l2_nw"
  let read_req := Wire.mk "l2_rr"
  let hit_detect := Wire.mk "l2_hd"
  let miss_detect := Wire.mk "l2_md"
  let wb_detect := Wire.mk "l2_wd"
  let refill_done := Wire.mk "l2_rd"
  let detect_gates := [
    Gate.mkNOT hit not_hit,
    Gate.mkNOT arb_is_write not_write,
    Gate.mkAND arb_valid not_write read_req,
    Gate.mkAND is_idle read_req (Wire.mk "l2_ir"),
    Gate.mkAND (Wire.mk "l2_ir") hit hit_detect,
    Gate.mkAND (Wire.mk "l2_ir") not_hit miss_detect,
    Gate.mkAND is_idle l1d_req_we wb_detect,
    Gate.mkAND is_mem_wait mem_resp_valid refill_done
  ]

  -- === Response Logic ===
  -- resp_valid = (is_hit_resp OR refill_done) AND source_match
  let resp_any := Wire.mk "l2_ra"
  let not_src_q := Wire.mk "l2_ns"
  let resp_valid_gates := [
    Gate.mkOR is_hit_resp refill_done resp_any,
    Gate.mkNOT src_q not_src_q,
    Gate.mkAND resp_any not_src_q l1i_resp_valid,
    Gate.mkAND resp_any src_q l1d_resp_valid
  ]
  -- Response data: is_hit_resp ? way_sel_data : mem_resp_data
  -- Both outputs get the same data (only valid signal differs)
  let resp_mux_i := (List.range lineBits).map fun b =>
    Gate.mkMUX (Wire.mk s!"wsd_{b}") mem_resp_data[b]! (Wire.mk "l2_rd") l1i_resp_data[b]!
  let resp_mux_d := (List.range lineBits).map fun b =>
    Gate.mkMUX (Wire.mk s!"wsd_{b}") mem_resp_data[b]! (Wire.mk "l2_rd") l1d_resp_data[b]!

  -- === Memory Request ===
  -- mem_req_valid = is_mem_req OR is_writeback
  -- During WRITEBACK: we=1, addr={pend_vtag, ref_idx, offset 0}, data=victim_data
  -- During MEM_REQ: we=0, addr=pend_q (line-aligned), data=0
  let wb_victim_data := (List.range lineBits).map fun b => Wire.mk s!"l2_wbvd_{b}"
  let wb_victim_data_mux : List Gate := List.flatten ((List.range lineBits).map fun b =>
    let t := (List.range ways).map (fun w => Wire.mk s!"l2_wbv_a{w}_{b}")
    List.flatten ((List.range ways).map fun w =>
      [Gate.mkAND pend_victim_q[w]! (l2_data_ram_rd[w]!)[b]! t[w]!])
    ++ mkOrTree t wb_victim_data[b]!)
  let mem_req_gates :=
    [Gate.mkOR is_mem_req is_writeback mem_req_valid,
     Gate.mkBUF is_writeback mem_req_we] ++
    -- addr: WRITEBACK ? {pend_vtag, ref_idx, offset 0} : {pend_q line-aligned}
    (List.range 32).map (fun i =>
      if i < offsetBits then Gate.mkBUF (Wire.mk "l2_const_zero") mem_req_addr[i]!
      else if i < offsetBits + idxBits then
        Gate.mkMUX pend_q[i]! ref_idx[i - offsetBits]! is_writeback mem_req_addr[i]!
      else
        Gate.mkMUX pend_q[i]! pend_vtag_q[i - offsetBits - idxBits]! is_writeback mem_req_addr[i]!) ++
    -- data: WRITEBACK ? victim_data : 0
    (List.range lineBits).map (fun i =>
      Gate.mkMUX (Wire.mk "l2_const_zero") wb_victim_data[i]! is_writeback mem_req_data[i]!)

  -- === FSM Next State ===
  -- IDLE→HIT_LATCH(001) on hit_detect
  -- IDLE→MEM_REQ(011) on miss_detect AND NOT victim_needs_wb
  -- IDLE→WRITEBACK(101) on miss_detect AND victim_needs_wb
  -- WRITEBACK(101)→MEM_REQ(011) unconditionally
  -- MEM_REQ(011)→MEM_WAIT(100) unconditionally
  -- MEM_WAIT(100)→IDLE(000) on mem_resp_valid
  let not_mem_resp := Wire.mk "l2_nmr"
  let stay_wait := Wire.mk "l2_sw"
  let not_vnwb := Wire.mk "l2_nvnwb"
  let miss_clean := Wire.mk "l2_mc"  -- miss with no dirty victim
  let miss_dirty := Wire.mk "l2_md2"  -- miss with dirty victim
  -- === L1D Writeback Miss+Dirty Detection ===
  -- wb_miss_dirty: L1D writeback misses in L2 AND would evict a dirty line
  let wb_miss_dirty := Wire.mk "l2_wmd"
  let wb_direct := Wire.mk "l2_wbd"
  let effective_wb_write := Wire.mk "l2_eww"
  let not_wb_miss_dirty := Wire.mk "l2_nwmd"
  let wb_miss_dirty_gates := [
    Gate.mkAND wb_detect not_hit (Wire.mk "l2_wbm"),
    Gate.mkAND (Wire.mk "l2_wbm") (Wire.mk "l2_vnwb") wb_miss_dirty,
    Gate.mkNOT wb_miss_dirty not_wb_miss_dirty,
    Gate.mkAND wb_detect not_wb_miss_dirty wb_direct,
    Gate.mkOR wb_direct is_wb_commit effective_wb_write
  ]

  -- evict_trigger captures the victim (miss_detect OR wb_miss_dirty)
  let evict_trigger := Wire.mk "l2_evtrig"
  let evict_trigger_gate := Gate.mkOR miss_detect wb_miss_dirty evict_trigger

  -- WRITEBACK→MEM_REQ (read miss) vs WRITEBACK→WB_COMMIT (L1D wb miss)
  let wb_to_memreq := Wire.mk "l2_wb2mr"
  let wb_to_commit := Wire.mk "l2_wb2wc"
  let not_pend_is_wb := Wire.mk "l2_npiwb"
  let fsm_next_gates := [
    Gate.mkNOT (Wire.mk "l2_vnwb") not_vnwb,
    Gate.mkAND miss_detect not_vnwb miss_clean,
    Gate.mkAND miss_detect (Wire.mk "l2_vnwb") miss_dirty,
    Gate.mkNOT mem_resp_valid not_mem_resp,
    Gate.mkAND is_mem_wait not_mem_resp stay_wait,
    Gate.mkNOT pend_is_wb_q not_pend_is_wb,
    Gate.mkAND is_writeback not_pend_is_wb wb_to_memreq,
    Gate.mkAND is_writeback pend_is_wb_q wb_to_commit,
    -- fsm_d[0] = hit_detect OR miss_clean OR miss_dirty OR wb_miss_dirty OR wb_to_memreq
    Gate.mkOR hit_detect miss_clean (Wire.mk "l2_f0t1"),
    Gate.mkOR miss_dirty wb_miss_dirty (Wire.mk "l2_f0t2a"),
    Gate.mkOR (Wire.mk "l2_f0t2a") wb_to_memreq (Wire.mk "l2_f0t2"),
    Gate.mkOR (Wire.mk "l2_f0t1") (Wire.mk "l2_f0t2") fsm_d[0]!,
    -- fsm_d[1] = is_hit_latch OR miss_clean OR is_writeback (unchanged)
    Gate.mkOR is_hit_latch miss_clean (Wire.mk "l2_f1t1"),
    Gate.mkOR (Wire.mk "l2_f1t1") is_writeback fsm_d[1]!,
    -- fsm_d[2] = is_mem_req OR stay_wait OR miss_dirty OR wb_miss_dirty OR wb_to_commit
    Gate.mkOR is_mem_req stay_wait (Wire.mk "l2_f2t1"),
    Gate.mkOR miss_dirty wb_miss_dirty (Wire.mk "l2_f2t2a"),
    Gate.mkOR (Wire.mk "l2_f2t2a") wb_to_commit (Wire.mk "l2_f2t2"),
    Gate.mkOR (Wire.mk "l2_f2t1") (Wire.mk "l2_f2t2") fsm_d[2]!
  ]

  -- === Register Capture ===
  -- Pending address + source: capture on evict_trigger (miss_detect OR wb_miss_dirty)
  let pend_next := (List.range 32).map fun i =>
    Gate.mkMUX pend_q[i]! arb_addr[i]! evict_trigger pend_d[i]!
  -- Source: capture on hit_detect OR miss_detect
  let capture_src := Wire.mk "l2_cs"
  let src_next := [
    Gate.mkOR hit_detect miss_detect capture_src,
    Gate.mkMUX src_q arb_sel_d capture_src src_d
  ]
  -- Latched index: capture on hit_detect
  let lat_idx_next := (List.range idxBits).map fun i =>
    Gate.mkMUX lat_idx_q[i]! cur_idx[i]! hit_detect lat_idx_d[i]!
  -- Latched way: capture the hitting way on hit_detect
  let lat_way_next := (List.range ways).map fun w =>
    Gate.mkMUX lat_way_q[w]! way_hit[w]! hit_detect lat_way_d[w]!

  -- === Victim Detection (for L2 writeback on eviction) ===
  -- Victim dirty/valid/tag: the requested set's victim way
  let victim_dirty := Wire.mk "l2_vdirty"
  let victim_valid := Wire.mk "l2_vvalid"
  let victim_needs_wb := Wire.mk "l2_vnwb"
  let victim_detect_gates : List Gate :=
    List.flatten ((List.range ways).map fun way =>
      let t := (List.range sets).map (fun st => Wire.mk s!"vda{way}_{st}")
      List.flatten ((List.range sets).map fun st =>
        [Gate.mkAND cur_dec[st]! dirty_q[way * sets + st]! t[st]!])
      ++ mkOrTree t (Wire.mk s!"vds{way}")) ++
    List.flatten ((List.range ways).map fun way =>
      let t := (List.range sets).map (fun st => Wire.mk s!"vva{way}_{st}")
      List.flatten ((List.range sets).map fun st =>
        [Gate.mkAND cur_dec[st]! valid_q[way * sets + st]! t[st]!])
      ++ mkOrTree t (Wire.mk s!"vvs{way}")) ++
    (List.range ways).map (fun way =>
      Gate.mkAND cur_victim[way]! (Wire.mk s!"vds{way}") (Wire.mk s!"vdm{way}")) ++
    (List.range ways).map (fun way =>
      Gate.mkAND cur_victim[way]! (Wire.mk s!"vvs{way}") (Wire.mk s!"vvm{way}")) ++
    mkOrTree ((List.range ways).map fun way => Wire.mk s!"vdm{way}") victim_dirty ++
    mkOrTree ((List.range ways).map fun way => Wire.mk s!"vvm{way}") victim_valid ++
    [Gate.mkAND victim_valid victim_dirty victim_needs_wb]

  -- Victim tag: the victim way's selected tag
  let victim_tag_raw := (List.range tagBits).map fun b => Wire.mk s!"vtraw_{b}"
  let victim_tag_mux : List Gate := List.flatten ((List.range tagBits).map fun b =>
    let t := (List.range ways).map (fun w => Wire.mk s!"vt_a{w}_{b}")
    List.flatten ((List.range ways).map fun w =>
      [Gate.mkAND cur_victim[w]! (way_sel_tag[w]!)[b]! t[w]!])
    ++ mkOrTree t victim_tag_raw[b]!)

  -- Capture the victim way + tag on evict_trigger
  let pend_victim_capture := (List.range ways).map fun w =>
    Gate.mkMUX pend_victim_q[w]! cur_victim[w]! evict_trigger pend_victim_d[w]!
  let pend_vtag_capture := (List.range tagBits).map fun b =>
    Gate.mkMUX pend_vtag_q[b]! victim_tag_raw[b]! evict_trigger pend_vtag_d[b]!
  -- pend_is_wb: 1 if triggered by wb_miss_dirty, 0 if by miss_detect
  let pend_is_wb_capture := Gate.mkMUX pend_is_wb_q wb_miss_dirty evict_trigger pend_is_wb_d

  -- === Write Way Selection ===
  -- For writeback: the hitting way, or the victim when the writeback missed
  let wb_use_way := (List.range ways).map fun w => Wire.mk s!"wbw{w}"
  let way_sel_gates : List Gate := List.flatten ((List.range ways).map fun w =>
    [Gate.mkAND (Wire.mk "l2_hit") way_hit[w]! (Wire.mk s!"l2_wbhw{w}"),
     Gate.mkAND (Wire.mk "l2_nh") cur_victim[w]! (Wire.mk s!"l2_wbml{w}"),
     Gate.mkOR (Wire.mk s!"l2_wbhw{w}") (Wire.mk s!"l2_wbml{w}") wb_use_way[w]!])

  -- === Write Enables ===
  -- Per way/set: wb_we OR refill_we
  let write_en_gates : List Gate := List.flatten ((List.range ways).map fun way =>
    List.flatten ((List.range sets).map fun set =>
      [Gate.mkAND (Wire.mk "l2_eww") cur_dec[set]! (Wire.mk s!"wbs_{way}_{set}"),
       Gate.mkAND (Wire.mk s!"wbs_{way}_{set}") wb_use_way[way]! (Wire.mk s!"wbw_{way}_{set}"),
       Gate.mkAND (Wire.mk "l2_rd") ref_dec[set]! (Wire.mk s!"rfs_{way}_{set}"),
       Gate.mkAND (Wire.mk s!"rfs_{way}_{set}") ref_victim[way]! (Wire.mk s!"rfw_{way}_{set}"),
       Gate.mkOR (Wire.mk s!"wbw_{way}_{set}") (Wire.mk s!"rfw_{way}_{set}") (Wire.mk s!"wen_{way}_{set}")]))

  -- === Write Data Selection ===
  -- write_tag: refill_done ? ref_tag : cur_tag
  let write_tag := (List.range tagBits).map fun b => Wire.mk s!"wt_{b}"
  let write_tag_mux := (List.range tagBits).map fun b =>
    Gate.mkMUX cur_tag[b]! ref_tag[b]! (Wire.mk "l2_rd") write_tag[b]!
  -- write_data: refill_done ? mem_resp_data : l1d_req_data
  let write_data := (List.range lineBits).map fun b => Wire.mk s!"wdd_{b}"
  let write_data_mux := (List.range lineBits).map fun b =>
    Gate.mkMUX l1d_req_data[b]! mem_resp_data[b]! (Wire.mk "l2_rd") write_data[b]!
  -- write_dirty: wb → dirty, refill → clean
  let not_refill := Wire.mk "l2_nrf"
  let write_dirty := Wire.mk "wdty"
  let write_dirty_gates := [Gate.mkNOT (Wire.mk "l2_rd") not_refill, Gate.mkBUF not_refill write_dirty]

  -- === Storage Next State ===
  -- Tag: MUX(hold, write_tag, write_en)
  let tag_next := (List.range ways).foldl (fun acc way =>
    acc ++ (List.range sets).foldl (fun acc2 set =>
      acc2 ++ (List.range tagBits).map (fun b =>
        Gate.mkMUX (Wire.mk s!"l2_tag_q_w{way}_s{set}_{b}") write_tag[b]!
          (Wire.mk s!"wen_{way}_{set}") (Wire.mk s!"l2_tag_d_w{way}_s{set}_{b}"))
    ) []
  ) []
  -- Data RAM write control: wen per way, addr, data
  -- write_en = OR of wen_{way}_{set} over the sets
  let data_ram_wen_gates : List Gate := List.flatten ((List.range ways).map fun way =>
    mkOrTree ((List.range sets).map fun set => Wire.mk s!"wen_{way}_{set}") l2_data_ram_wr_en[way]!)
  -- Write addr: refill uses ref_idx, wb uses cur_idx; MUX on refill_done
  let data_ram_waddr_gates := (List.range ways).foldl (fun acc way =>
    acc ++ (List.range idxBits).map (fun i =>
      Gate.mkMUX cur_idx[i]! ref_idx[i]! (Wire.mk "l2_rd") (l2_data_ram_wr_addr[way]!)[i]!)
  ) []
  -- Write data: already computed as write_data[b]
  let data_ram_wdata_gates := (List.range ways).foldl (fun acc way =>
    acc ++ (List.range lineBits).map (fun b =>
      Gate.mkBUF write_data[b]! (l2_data_ram_wr_data[way]!)[b]!)
  ) []
  -- Define the actual RAM primitives (read_idx is now available)
  let data_rams := (List.range ways).map fun way =>
    RAMPrimitive.mk s!"l2_data_ram_w{way}" sets lineBits
      [{ en := l2_data_ram_wr_en[way]!
         addr := l2_data_ram_wr_addr[way]!
         data := l2_data_ram_wr_data[way]! }]
      [{ addr := read_idx
         data := l2_data_ram_rd[way]! }]
      false clock
      -- 1R1W contract: separate read/write addresses, asynchronous read
      (portKind := .r1w1)
  -- Valid: OR(hold, write_en)
  let valid_next := (List.range ways).foldl (fun acc way =>
    acc ++ (List.range sets).map (fun set =>
      Gate.mkOR valid_q[way * sets + set]! (Wire.mk s!"wen_{way}_{set}") valid_d[way * sets + set]!)
  ) []
  -- Dirty: MUX(hold, write_dirty, write_en)
  let dirty_next := (List.range ways).foldl (fun acc way =>
    acc ++ (List.range sets).map (fun set =>
      let idx := way * sets + set
      Gate.mkMUX dirty_q[idx]! write_dirty (Wire.mk s!"wen_{way}_{set}") dirty_d[idx]!)
  ) []

  -- === Stall Signals ===
  -- === L1D Writeback Acknowledge ===
  let l1d_wb_ack := Wire.mk "l1d_wb_ack"
  let wb_ack_gate := Gate.mkBUF effective_wb_write l1d_wb_ack

  let stall_gates := [
    -- stall_i = NOT idle OR (idle AND D-side priority AND I-side requesting)
    Gate.mkAND is_idle arb_sel_d (Wire.mk "l2_dp"),
    Gate.mkAND (Wire.mk "l2_dp") l1i_req_valid (Wire.mk "l2_ib"),
    Gate.mkOR not_idle (Wire.mk "l2_ib") stall_i,
    Gate.mkBUF not_idle stall_d
  ]

  -- The set-touch event for the replacement policy (a read hit or a writeback)
  let access_evt_gate := Gate.mkOR hit_detect effective_wb_write (Wire.mk "l2_access_evt")

  -- === Assemble ===
  { name := "L2Cache"
    inputs := [clock, reset, l1i_req_valid] ++ l1i_req_addr ++
              [l1d_req_valid] ++ l1d_req_addr ++ [l1d_req_we] ++ l1d_req_data ++
              [mem_resp_valid] ++ mem_resp_data
    outputs := [l1i_resp_valid] ++ l1i_resp_data ++
               [l1d_resp_valid] ++ l1d_resp_data ++
               [mem_req_valid] ++ mem_req_addr ++ [mem_req_we] ++ mem_req_data ++
               [l1d_wb_ack, stall_i, stall_d]
    gates := fsm_dffs ++ [src_dff] ++ pend_dffs ++ lat_idx_dffs ++ lat_way_dffs ++
             pend_victim_dffs ++ pend_vtag_dffs ++ [pend_is_wb_dff] ++
             valid_dffs ++ dirty_dffs ++
             const_zero_gates ++ arb_gates ++ arb_addr_mux ++
             read_idx_mux ++ valid_mux_gates ++ hit_gates ++
             pickVictim cur_dec cur_victim ++ pickVictim ref_dec ref_victim ++
             plru_gates ++ read_way_mux ++ way_data_mux ++
             fsm_decode_gates ++
             detect_gates ++
             victim_detect_gates ++ victim_tag_mux ++
             wb_miss_dirty_gates ++ [evict_trigger_gate] ++
             pend_victim_capture ++ pend_vtag_capture ++ [pend_is_wb_capture] ++
             resp_valid_gates ++ resp_mux_i ++ resp_mux_d ++
             wb_victim_data_mux ++ mem_req_gates ++
             fsm_next_gates ++ pend_next ++ src_next ++ lat_idx_next ++ lat_way_next ++
             way_sel_gates ++ write_en_gates ++
             write_tag_mux ++ write_data_mux ++ write_dirty_gates ++
             tag_next ++ data_ram_wen_gates ++ data_ram_waddr_gates ++ data_ram_wdata_gates ++
             valid_next ++ dirty_next ++ [wb_ack_gate, access_evt_gate] ++ stall_gates
    instances := tag_instances ++
                 [cur_dec_inst, ref_dec_inst] ++
                 tag_mux_instances ++ tag_cmp_instances ++ plru_insts
    rams := data_rams
    signalGroups := [
      { name := "l1i_req_addr", width := 32, wires := l1i_req_addr },
      { name := "l1d_req_addr", width := 32, wires := l1d_req_addr },
      { name := "l1d_req_data", width := lineBits, wires := l1d_req_data },
      { name := "l1i_resp_data", width := lineBits, wires := l1i_resp_data },
      { name := "l1d_resp_data", width := lineBits, wires := l1d_resp_data },
      { name := "mem_resp_data", width := lineBits, wires := mem_resp_data },
      { name := "mem_req_addr", width := 32, wires := mem_req_addr },
      { name := "mem_req_data", width := lineBits, wires := mem_req_data }
    ]
  }

end Shoumei.RISCV.Memory.Cache

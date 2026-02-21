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

    FSM states (3-bit):
    - IDLE (000): Accept requests, tag lookup
    - HIT_LATCH (001): Hit detected, latching data read (1-cycle delay)
    - HIT_RESP (010): Respond with stored data
    - MEM_REQ (011): Send read request to main memory
    - MEM_WAIT (100): Wait for memory response, then respond + install

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
  -- === Port Wires ===
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let l1i_req_valid := Wire.mk "l1i_req_valid"
  let l1i_req_addr := (List.range 32).map fun i => Wire.mk s!"l1i_req_addr_{i}"
  let l1i_resp_valid := Wire.mk "l1i_resp_valid"
  let l1i_resp_data := (List.range 256).map fun i => Wire.mk s!"l1i_resp_data_{i}"
  let l1d_req_valid := Wire.mk "l1d_req_valid"
  let l1d_req_addr := (List.range 32).map fun i => Wire.mk s!"l1d_req_addr_{i}"
  let l1d_req_we := Wire.mk "l1d_req_we"
  let l1d_req_data := (List.range 256).map fun i => Wire.mk s!"l1d_req_data_{i}"
  let l1d_resp_valid := Wire.mk "l1d_resp_valid"
  let l1d_resp_data := (List.range 256).map fun i => Wire.mk s!"l1d_resp_data_{i}"
  let mem_resp_valid := Wire.mk "mem_resp_valid"
  let mem_resp_data := (List.range 256).map fun i => Wire.mk s!"mem_resp_data_{i}"
  let mem_req_valid := Wire.mk "mem_req_valid"
  let mem_req_addr := (List.range 32).map fun i => Wire.mk s!"mem_req_addr_{i}"
  let mem_req_we := Wire.mk "mem_req_we"
  let mem_req_data := (List.range 256).map fun i => Wire.mk s!"mem_req_data_{i}"
  let stall_i := Wire.mk "stall_i"
  let stall_d := Wire.mk "stall_d"

  -- === State Registers ===
  -- FSM: 3-bit (IDLE=000, HIT_LATCH=001, HIT_RESP=010, MEM_REQ=011, MEM_WAIT=100)
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

  -- Latched index: 3-bit (for hit data readback in HIT_LATCH/HIT_RESP)
  let lat_idx_d := (List.range 3).map fun i => Wire.mk s!"lat_idx_d_{i}"
  let lat_idx_q := (List.range 3).map fun i => Wire.mk s!"lat_idx_q_{i}"
  let lat_idx_dffs := (List.range 3).map fun i => Gate.mkDFF lat_idx_d[i]! clock reset lat_idx_q[i]!

  -- Latched way: 1-bit (which way hit, for readback)
  let lat_way_d := Wire.mk "lat_way_d"
  let lat_way_q := Wire.mk "lat_way_q"
  let lat_way_dff := Gate.mkDFF lat_way_d clock reset lat_way_q

  -- Tag storage: 2 ways × 8 sets × 24 bits (Register24 instances)
  let tag_instances := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 8).map (fun set =>
      CircuitInstance.mk "Register24" s!"u_l2_tag_w{way}_s{set}"
        ((List.range 24).map (fun b => (s!"d_{b}", Wire.mk s!"l2_tag_d_w{way}_s{set}_{b}")) ++
         [("clock", clock), ("reset", reset)] ++
         (List.range 24).map (fun b => (s!"q_{b}", Wire.mk s!"l2_tag_q_w{way}_s{set}_{b}"))))
  ) []

  -- Valid bits: 2 ways × 8 sets = 16 DFFs
  let valid_d := (List.range 16).map fun i => Wire.mk s!"l2_valid_d_{i}"
  let valid_q := (List.range 16).map fun i => Wire.mk s!"l2_valid_q_{i}"
  let valid_dffs := (List.range 16).map fun i => Gate.mkDFF valid_d[i]! clock reset valid_q[i]!

  -- Dirty bits: 2 ways × 8 sets = 16 DFFs
  let dirty_d := (List.range 16).map fun i => Wire.mk s!"l2_dirty_d_{i}"
  let dirty_q := (List.range 16).map fun i => Wire.mk s!"l2_dirty_q_{i}"
  let dirty_dffs := (List.range 16).map fun i => Gate.mkDFF dirty_d[i]! clock reset dirty_q[i]!

  -- LRU bits: 8 DFFs (one per set)
  let lru_d := (List.range 8).map fun i => Wire.mk s!"l2_lru_d_{i}"
  let lru_q := (List.range 8).map fun i => Wire.mk s!"l2_lru_q_{i}"
  let lru_dffs := (List.range 8).map fun i => Gate.mkDFF lru_d[i]! clock reset lru_q[i]!

  -- Writeback buffer: victim data (256-bit) + tag (24-bit) + dirty flag (1-bit)
  let wb_buf_d := (List.range 256).map fun i => Wire.mk s!"l2_wb_buf_d_{i}"
  let wb_buf_q := (List.range 256).map fun i => Wire.mk s!"l2_wb_buf_q_{i}"
  let wb_buf_dffs := (List.range 256).map fun i => Gate.mkDFF wb_buf_d[i]! clock reset wb_buf_q[i]!
  let wb_tag_d := (List.range 24).map fun i => Wire.mk s!"l2_wb_tag_d_{i}"
  let wb_tag_q := (List.range 24).map fun i => Wire.mk s!"l2_wb_tag_q_{i}"
  let wb_tag_dffs := (List.range 24).map fun i => Gate.mkDFF wb_tag_d[i]! clock reset wb_tag_q[i]!
  let wb_dirty_d := Wire.mk "l2_wb_dirty_d"
  let wb_dirty_q := Wire.mk "l2_wb_dirty_q"
  let wb_dirty_dff := Gate.mkDFF wb_dirty_d clock reset wb_dirty_q

  -- wb_is_write: 1 if WB_REQ was triggered by L1D writeback (not read miss)
  let wb_is_write_d := Wire.mk "l2_wb_iswr_d"
  let wb_is_write_q := Wire.mk "l2_wb_iswr_q"
  let wb_is_write_dff := Gate.mkDFF wb_is_write_d clock reset wb_is_write_q

  -- wb_way: which way the victim was (captured on miss_detect or wb_miss_dirty)
  let wb_way_d := Wire.mk "l2_wb_way_d"
  let wb_way_q := Wire.mk "l2_wb_way_q"
  let wb_way_dff := Gate.mkDFF wb_way_d clock reset wb_way_q

  -- Data RAM wire declarations (RAMs defined later after read_idx is available)
  let l2_data_ram_rd := (List.range 2).map fun way =>
    (List.range 256).map fun b => Wire.mk s!"drd{way}_{b}"
  let l2_data_ram_wr_en := (List.range 2).map fun way => Wire.mk s!"l2_dwr_en_w{way}"
  let l2_data_ram_wr_addr := (List.range 2).map fun way =>
    (List.range 3).map fun i => Wire.mk s!"l2_dwr_addr_w{way}_{i}"
  let l2_data_ram_wr_data := (List.range 2).map fun way =>
    (List.range 256).map fun b => Wire.mk s!"l2_dwr_data_w{way}_{b}"

  -- === Constants ===
  let const_zero_gates := [
    Gate.mkNOT reset (Wire.mk "l2_not_reset"),
    Gate.mkAND reset (Wire.mk "l2_not_reset") (Wire.mk "l2_const_zero")
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
  -- Current request: idx = arb_addr[7:5], tag = arb_addr[31:8]
  let cur_idx := [arb_addr[5]!, arb_addr[6]!, arb_addr[7]!]
  let cur_tag := (List.range 24).map fun i => arb_addr[i + 8]!
  -- Refill/pending: idx = pend_q[7:5], tag = pend_q[31:8]
  let ref_idx := [pend_q[5]!, pend_q[6]!, pend_q[7]!]
  let ref_tag := (List.range 24).map fun i => pend_q[i + 8]!

  -- === Index Decoders (3-to-8) ===
  -- Current request decoder
  let not_cur_idx := (List.range 3).map fun i => Wire.mk s!"not_ci_{i}"
  let not_cur_idx_gates := (List.range 3).map fun i => Gate.mkNOT cur_idx[i]! not_cur_idx[i]!
  let cur_dec := (List.range 8).map fun i => Wire.mk s!"cd_{i}"
  let cur_dec_gates := (List.range 8).foldl (fun acc i =>
    let b0 := if i % 2 == 0 then not_cur_idx[0]! else cur_idx[0]!
    let b1 := if (i / 2) % 2 == 0 then not_cur_idx[1]! else cur_idx[1]!
    let b2 := if (i / 4) % 2 == 0 then not_cur_idx[2]! else cur_idx[2]!
    acc ++ [Gate.mkAND b0 b1 (Wire.mk s!"cdt_{i}"), Gate.mkAND (Wire.mk s!"cdt_{i}") b2 cur_dec[i]!]
  ) []
  -- Refill decoder
  let not_ref_idx := (List.range 3).map fun i => Wire.mk s!"not_ri_{i}"
  let not_ref_idx_gates := (List.range 3).map fun i => Gate.mkNOT ref_idx[i]! not_ref_idx[i]!
  let ref_dec := (List.range 8).map fun i => Wire.mk s!"rd_{i}"
  let ref_dec_gates := (List.range 8).foldl (fun acc i =>
    let b0 := if i % 2 == 0 then not_ref_idx[0]! else ref_idx[0]!
    let b1 := if (i / 2) % 2 == 0 then not_ref_idx[1]! else ref_idx[1]!
    let b2 := if (i / 4) % 2 == 0 then not_ref_idx[2]! else ref_idx[2]!
    acc ++ [Gate.mkAND b0 b1 (Wire.mk s!"rdt_{i}"), Gate.mkAND (Wire.mk s!"rdt_{i}") b2 ref_dec[i]!]
  ) []

  -- === Read Index Mux ===
  -- During IDLE: use cur_idx. During HIT_LATCH/HIT_RESP: use lat_idx_q.
  let not_idle := Wire.mk "l2_not_idle"  -- computed in FSM decode below, declared here
  let read_idx := (List.range 3).map fun i => Wire.mk s!"ridx_{i}"
  let read_idx_mux := (List.range 3).map fun i =>
    Gate.mkMUX cur_idx[i]! lat_idx_q[i]! not_idle read_idx[i]!
  let read_way1 := Wire.mk "rway1"

  -- === Tag Lookup ===
  -- Per way: Mux8x24 to select tag from indexed set, then EqualityComparator24
  let way_sel_tag := (List.range 2).map fun w => (List.range 24).map fun b => Wire.mk s!"wst{w}_{b}"
  let tag_mux_instances := (List.range 2).map fun way =>
    CircuitInstance.mk "Mux8x24" s!"u_l2_tag_mux_w{way}"
      ((List.range 8).foldl (fun acc set =>
        acc ++ (List.range 24).map (fun b =>
          (s!"in{set}_{b}", Wire.mk s!"l2_tag_q_w{way}_s{set}_{b}"))
      ) [] ++
      (List.range 3).map (fun i => (s!"sel_{i}", cur_idx[i]!)) ++
      (List.range 24).map (fun b => (s!"out_{b}", (way_sel_tag[way]!)[b]!)))
  let way_tag_match := (List.range 2).map fun w => Wire.mk s!"wtm{w}"
  let tag_cmp_instances := (List.range 2).map fun way =>
    CircuitInstance.mk "EqualityComparator24" s!"u_l2_cmp_w{way}"
      ((List.range 24).map (fun b => (s!"a_{b}", (way_sel_tag[way]!)[b]!)) ++
       (List.range 24).map (fun b => (s!"b_{b}", cur_tag[b]!)) ++
       [("eq", way_tag_match[way]!)])

  -- === Valid Bit Lookup ===
  -- Per way: gate-based 8:1 mux of valid bits. Layout: valid_q[way*8+set]
  let way_valid_sel := (List.range 2).map fun w => Wire.mk s!"wvs{w}"
  let valid_mux_gates := (List.range 2).foldl (fun acc way =>
    let base := way * 8
    let va := (List.range 8).map fun i => Wire.mk s!"va{way}_{i}"
    let vo := (List.range 6).map fun i => Wire.mk s!"vo{way}_{i}"
    acc ++
    (List.range 8).map (fun i => Gate.mkAND cur_dec[i]! valid_q[base + i]! va[i]!) ++
    [Gate.mkOR va[0]! va[1]! vo[0]!, Gate.mkOR va[2]! va[3]! vo[1]!,
     Gate.mkOR va[4]! va[5]! vo[2]!, Gate.mkOR va[6]! va[7]! vo[3]!,
     Gate.mkOR vo[0]! vo[1]! vo[4]!, Gate.mkOR vo[2]! vo[3]! vo[5]!,
     Gate.mkOR vo[4]! vo[5]! way_valid_sel[way]!]
  ) []

  -- === Hit Detection ===
  let way_hit := (List.range 2).map fun w => Wire.mk s!"wh{w}"
  let hit := Wire.mk "l2_hit"
  let hit_gates :=
    (List.range 2).map (fun w => Gate.mkAND way_valid_sel[w]! way_tag_match[w]! way_hit[w]!) ++
    [Gate.mkOR way_hit[0]! way_hit[1]! hit]

  -- === Data Read Path ===
  -- RAM read ports provide drd{way}_{b} directly (replacing Mux8x32 instances)
  -- Way select MUX: 256 gates, controlled by read_way1
  let way_data_mux := (List.range 256).map fun b =>
    Gate.mkMUX (Wire.mk s!"drd0_{b}") (Wire.mk s!"drd1_{b}") read_way1 (Wire.mk s!"wsd_{b}")

  -- === FSM Decode ===
  let not_fsm := (List.range 3).map fun i => Wire.mk s!"l2nf{i}"
  let is_idle := Wire.mk "l2_is_idle"
  let is_hit_latch := Wire.mk "l2_is_hl"
  let is_hit_resp := Wire.mk "l2_is_hr"
  let is_mem_req := Wire.mk "l2_is_mr"
  let is_mem_wait := Wire.mk "l2_is_mw"
  let is_wb_req := Wire.mk "l2_is_wb"
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
     Gate.mkAND fsm_q[0]! not_fsm[1]! (Wire.mk "l2f01wb"),
     Gate.mkAND (Wire.mk "l2f01wb") fsm_q[2]! is_wb_req,          -- 101
     Gate.mkNOT is_idle not_idle]

  -- Read way mux: idle ? way_hit[1] : lat_way_q
  let read_way1_mux := Gate.mkMUX way_hit[1]! lat_way_q not_idle read_way1

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

  -- === LRU Lookup (moved before victim detection) ===
  -- Current set LRU: gate-based 8:1 mux of lru_q by cur_dec
  let cur_lru := Wire.mk "clru"
  let cur_lru_gates :=
    let la := (List.range 8).map fun i => Wire.mk s!"cla_{i}"
    (List.range 8).map (fun i => Gate.mkAND cur_dec[i]! lru_q[i]! la[i]!) ++
    [Gate.mkOR la[0]! la[1]! (Wire.mk "clo01"), Gate.mkOR la[2]! la[3]! (Wire.mk "clo23"),
     Gate.mkOR la[4]! la[5]! (Wire.mk "clo45"), Gate.mkOR la[6]! la[7]! (Wire.mk "clo67"),
     Gate.mkOR (Wire.mk "clo01") (Wire.mk "clo23") (Wire.mk "clo03"),
     Gate.mkOR (Wire.mk "clo45") (Wire.mk "clo67") (Wire.mk "clo47"),
     Gate.mkOR (Wire.mk "clo03") (Wire.mk "clo47") cur_lru]

  -- === Victim Dirty Detection ===
  -- Victim way dirty: select dirty bit for victim way (cur_lru) at current set
  -- dirty_q layout: [way0_set0..way0_set7, way1_set0..way1_set7]
  -- victim_dirty_w0 = OR of (cur_dec[set] AND dirty_q[set]) for way0
  -- victim_dirty_w1 = OR of (cur_dec[set] AND dirty_q[8+set]) for way1
  -- victim_dirty = cur_lru ? victim_dirty_w1 : victim_dirty_w0
  let victim_dirty := Wire.mk "l2_vdirty"
  let miss_dirty := Wire.mk "l2_miss_dirty"
  let miss_clean := Wire.mk "l2_miss_clean"
  let victim_dirty_gates :=
    let vda0 := (List.range 8).map fun i => Wire.mk s!"vda0_{i}"
    let vda1 := (List.range 8).map fun i => Wire.mk s!"vda1_{i}"
    (List.range 8).map (fun i => Gate.mkAND cur_dec[i]! dirty_q[i]! vda0[i]!) ++
    (List.range 8).map (fun i => Gate.mkAND cur_dec[i]! dirty_q[8 + i]! vda1[i]!) ++
    [Gate.mkOR vda0[0]! vda0[1]! (Wire.mk "vdo0_01"), Gate.mkOR vda0[2]! vda0[3]! (Wire.mk "vdo0_23"),
     Gate.mkOR vda0[4]! vda0[5]! (Wire.mk "vdo0_45"), Gate.mkOR vda0[6]! vda0[7]! (Wire.mk "vdo0_67"),
     Gate.mkOR (Wire.mk "vdo0_01") (Wire.mk "vdo0_23") (Wire.mk "vdo0_03"),
     Gate.mkOR (Wire.mk "vdo0_45") (Wire.mk "vdo0_67") (Wire.mk "vdo0_47"),
     Gate.mkOR (Wire.mk "vdo0_03") (Wire.mk "vdo0_47") (Wire.mk "l2_vdirty_w0"),
     Gate.mkOR vda1[0]! vda1[1]! (Wire.mk "vdo1_01"), Gate.mkOR vda1[2]! vda1[3]! (Wire.mk "vdo1_23"),
     Gate.mkOR vda1[4]! vda1[5]! (Wire.mk "vdo1_45"), Gate.mkOR vda1[6]! vda1[7]! (Wire.mk "vdo1_67"),
     Gate.mkOR (Wire.mk "vdo1_01") (Wire.mk "vdo1_23") (Wire.mk "vdo1_03"),
     Gate.mkOR (Wire.mk "vdo1_45") (Wire.mk "vdo1_67") (Wire.mk "vdo1_47"),
     Gate.mkOR (Wire.mk "vdo1_03") (Wire.mk "vdo1_47") (Wire.mk "l2_vdirty_w1"),
     Gate.mkMUX (Wire.mk "l2_vdirty_w0") (Wire.mk "l2_vdirty_w1") cur_lru victim_dirty]
  -- Also need victim valid: check if the victim way has a valid line
  let victim_valid := Wire.mk "l2_vvalid"
  let victim_valid_gates :=
    let vva0 := (List.range 8).map fun i => Wire.mk s!"vva0_{i}"
    let vva1 := (List.range 8).map fun i => Wire.mk s!"vva1_{i}"
    (List.range 8).map (fun i => Gate.mkAND cur_dec[i]! valid_q[i]! vva0[i]!) ++
    (List.range 8).map (fun i => Gate.mkAND cur_dec[i]! valid_q[8 + i]! vva1[i]!) ++
    [Gate.mkOR vva0[0]! vva0[1]! (Wire.mk "vvo0_01"), Gate.mkOR vva0[2]! vva0[3]! (Wire.mk "vvo0_23"),
     Gate.mkOR vva0[4]! vva0[5]! (Wire.mk "vvo0_45"), Gate.mkOR vva0[6]! vva0[7]! (Wire.mk "vvo0_67"),
     Gate.mkOR (Wire.mk "vvo0_01") (Wire.mk "vvo0_23") (Wire.mk "vvo0_03"),
     Gate.mkOR (Wire.mk "vvo0_45") (Wire.mk "vvo0_67") (Wire.mk "vvo0_47"),
     Gate.mkOR (Wire.mk "vvo0_03") (Wire.mk "vvo0_47") (Wire.mk "l2_vvalid_w0"),
     Gate.mkOR vva1[0]! vva1[1]! (Wire.mk "vvo1_01"), Gate.mkOR vva1[2]! vva1[3]! (Wire.mk "vvo1_23"),
     Gate.mkOR vva1[4]! vva1[5]! (Wire.mk "vvo1_45"), Gate.mkOR vva1[6]! vva1[7]! (Wire.mk "vvo1_67"),
     Gate.mkOR (Wire.mk "vvo1_01") (Wire.mk "vvo1_23") (Wire.mk "vvo1_03"),
     Gate.mkOR (Wire.mk "vvo1_45") (Wire.mk "vvo1_67") (Wire.mk "vvo1_47"),
     Gate.mkOR (Wire.mk "vvo1_03") (Wire.mk "vvo1_47") (Wire.mk "l2_vvalid_w1"),
     Gate.mkMUX (Wire.mk "l2_vvalid_w0") (Wire.mk "l2_vvalid_w1") cur_lru victim_valid]
  -- miss_dirty = miss_detect AND victim_dirty AND victim_valid
  -- miss_clean = miss_detect AND NOT(victim_dirty AND victim_valid)
  let not_vdv := Wire.mk "l2_nvdv"
  let vdv := Wire.mk "l2_vdv"
  let miss_detect_gates := [
    Gate.mkAND victim_dirty victim_valid vdv,
    Gate.mkNOT vdv not_vdv,
    Gate.mkAND miss_detect vdv miss_dirty,
    Gate.mkAND miss_detect not_vdv miss_clean
  ]

  -- wb_miss_dirty: L1D writeback that misses in L2 and victim is dirty+valid
  let wb_miss_dirty := Wire.mk "l2_wb_md"
  let wb_miss_dirty_gates := [
    Gate.mkAND wb_detect not_hit (Wire.mk "l2_wb_miss"),
    Gate.mkAND (Wire.mk "l2_wb_miss") vdv wb_miss_dirty
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
  let resp_mux_i := (List.range 256).map fun b =>
    Gate.mkMUX (Wire.mk s!"wsd_{b}") mem_resp_data[b]! refill_done l1i_resp_data[b]!
  let resp_mux_d := (List.range 256).map fun b =>
    Gate.mkMUX (Wire.mk s!"wsd_{b}") mem_resp_data[b]! refill_done l1d_resp_data[b]!

  -- === Writeback Buffer Capture ===
  -- On miss_detect, capture victim data (cur_lru selects way) and victim tag
  let victim_data_mux := (List.range 256).map fun b => Wire.mk s!"l2_vdata_{b}"
  let victim_data_gates := (List.range 256).map fun b =>
    Gate.mkMUX (Wire.mk s!"drd0_{b}") (Wire.mk s!"drd1_{b}") cur_lru victim_data_mux[b]!
  let victim_tag_mux := (List.range 24).map fun b => Wire.mk s!"l2_vtag_{b}"
  let victim_tag_gates := (List.range 24).map fun b =>
    Gate.mkMUX (way_sel_tag[0]!)[b]! (way_sel_tag[1]!)[b]! cur_lru victim_tag_mux[b]!
  -- wb_buf_d: capture on miss_detect OR wb_miss_dirty, hold otherwise
  let capture_victim := Wire.mk "l2_cap_v"
  let capture_victim_gate := Gate.mkOR miss_detect wb_miss_dirty capture_victim
  let wb_buf_next := (List.range 256).map fun b =>
    Gate.mkMUX wb_buf_q[b]! victim_data_mux[b]! capture_victim wb_buf_d[b]!
  let wb_tag_next := (List.range 24).map fun b =>
    Gate.mkMUX wb_tag_q[b]! victim_tag_mux[b]! capture_victim wb_tag_d[b]!
  let wb_dirty_next := Gate.mkMUX wb_dirty_q vdv capture_victim wb_dirty_d
  -- wb_is_write: set 1 on wb_miss_dirty, 0 on read miss_dirty, hold otherwise
  let wb_is_write_next := [
    Gate.mkMUX wb_is_write_q wb_miss_dirty capture_victim wb_is_write_d
  ]
  -- wb_way: capture cur_lru on capture_victim
  let wb_way_next := Gate.mkMUX wb_way_q cur_lru capture_victim wb_way_d

  -- === Memory Request ===
  -- mem_req_valid = is_mem_req OR is_wb_req
  -- mem_req_we = is_wb_req
  -- mem_req_addr: wb_req ? {wb_tag, pend_idx, 5'b0} : {pend_tag, pend_idx, 5'b0}
  -- mem_req_data: wb_buf_q
  let mem_req_valid_or := Wire.mk "l2_mrv_or"
  let mem_req_gates :=
    [Gate.mkOR is_mem_req is_wb_req mem_req_valid_or,
     Gate.mkBUF mem_req_valid_or mem_req_valid,
     Gate.mkBUF is_wb_req mem_req_we] ++
    (List.range 32).map (fun i =>
      if i < 5 then Gate.mkBUF (Wire.mk "l2_const_zero") mem_req_addr[i]!
      else if i < 8 then
        -- Bits 5-7: always from pend_q (same set index for both wb and refill)
        Gate.mkBUF pend_q[i]! mem_req_addr[i]!
      else
        -- Bits 8-31: tag. wb_req ? wb_tag : pend_tag (=ref_tag)
        Gate.mkMUX pend_q[i]! wb_tag_q[i - 8]! is_wb_req mem_req_addr[i]!) ++
    (List.range 256).map (fun i => Gate.mkBUF wb_buf_q[i]! mem_req_data[i]!)

  -- === FSM Next State ===
  -- IDLE(000) → hit: HIT_LATCH(001), miss_clean: MEM_REQ(011), miss_dirty: WB_REQ(101),
  --              wb_miss_dirty: WB_REQ(101)
  -- HIT_LATCH(001) → HIT_RESP(010)
  -- HIT_RESP(010) → IDLE(000)
  -- MEM_REQ(011) → MEM_WAIT(100)
  -- MEM_WAIT(100) → done: IDLE(000), !done: MEM_WAIT(100)
  -- WB_REQ(101) → wb_is_write ? IDLE(000) : MEM_REQ(011)
  let not_mem_resp := Wire.mk "l2_nmr"
  let stay_wait := Wire.mk "l2_sw"
  let not_wb_iswr := Wire.mk "l2_nwbiw"
  let wb_req_to_mr := Wire.mk "l2_wbmr"
  let fsm_next_gates := [
    Gate.mkNOT wb_is_write_q not_wb_iswr,
    Gate.mkAND is_wb_req not_wb_iswr wb_req_to_mr,
    -- fsm_d[0]: HIT_LATCH from hit_detect, MEM_REQ from miss_clean/miss_detect/wb_req_to_mr,
    --           WB_REQ from miss_dirty/wb_miss_dirty
    Gate.mkOR hit_detect miss_detect (Wire.mk "l2_fd0_hm"),
    Gate.mkOR (Wire.mk "l2_fd0_hm") wb_req_to_mr (Wire.mk "l2_fd0_hmw"),
    Gate.mkOR (Wire.mk "l2_fd0_hmw") wb_miss_dirty fsm_d[0]!,
    -- fsm_d[1]: HIT_RESP from hit_latch, MEM_REQ from miss_clean/wb_req_to_mr
    Gate.mkOR is_hit_latch miss_clean (Wire.mk "l2_fd1_hc"),
    Gate.mkOR (Wire.mk "l2_fd1_hc") wb_req_to_mr fsm_d[1]!,
    -- fsm_d[2]: WB_REQ from miss_dirty/wb_miss_dirty, MEM_WAIT from mem_req/stay_wait
    Gate.mkNOT mem_resp_valid not_mem_resp,
    Gate.mkAND is_mem_wait not_mem_resp stay_wait,
    Gate.mkOR miss_dirty wb_miss_dirty (Wire.mk "l2_fd2_dirty"),
    Gate.mkOR (Wire.mk "l2_fd2_dirty") is_mem_req (Wire.mk "l2_fd2_dm"),
    Gate.mkOR (Wire.mk "l2_fd2_dm") stay_wait fsm_d[2]!
  ]

  -- === Register Capture ===
  -- Pending address + source: capture on miss_detect OR wb_miss_dirty
  let capture_pend := Wire.mk "l2_cap_p"
  let capture_pend_gate := Gate.mkOR miss_detect wb_miss_dirty capture_pend
  let pend_next := (List.range 32).map fun i =>
    Gate.mkMUX pend_q[i]! arb_addr[i]! capture_pend pend_d[i]!
  -- Source: capture on hit_detect OR miss_detect
  let capture_src := Wire.mk "l2_cs"
  let src_next := [
    Gate.mkOR hit_detect miss_detect capture_src,
    Gate.mkMUX src_q arb_sel_d capture_src src_d
  ]
  -- Latched index: capture on hit_detect
  let lat_idx_next := (List.range 3).map fun i =>
    Gate.mkMUX lat_idx_q[i]! cur_idx[i]! hit_detect lat_idx_d[i]!
  -- Latched way: capture on hit_detect
  let lat_way_next := Gate.mkMUX lat_way_q way_hit[1]! hit_detect lat_way_d

  -- Refill set LRU
  let ref_lru := Wire.mk "rlru"
  let ref_lru_gates :=
    let la := (List.range 8).map fun i => Wire.mk s!"rla_{i}"
    (List.range 8).map (fun i => Gate.mkAND ref_dec[i]! lru_q[i]! la[i]!) ++
    [Gate.mkOR la[0]! la[1]! (Wire.mk "rlo01"), Gate.mkOR la[2]! la[3]! (Wire.mk "rlo23"),
     Gate.mkOR la[4]! la[5]! (Wire.mk "rlo45"), Gate.mkOR la[6]! la[7]! (Wire.mk "rlo67"),
     Gate.mkOR (Wire.mk "rlo01") (Wire.mk "rlo23") (Wire.mk "rlo03"),
     Gate.mkOR (Wire.mk "rlo45") (Wire.mk "rlo67") (Wire.mk "rlo47"),
     Gate.mkOR (Wire.mk "rlo03") (Wire.mk "rlo47") ref_lru]

  -- === Write Way Selection ===
  -- For writeback: hit ? hit_way : victim (cur_lru)
  let wb_use_way1 := Wire.mk "wbw1"
  let not_wb_w1 := Wire.mk "nwbw1"
  let not_ref_lru := Wire.mk "nrlru"
  let way_sel_gates := [
    Gate.mkAND hit way_hit[1]! (Wire.mk "wbhw1"),
    Gate.mkAND not_hit cur_lru (Wire.mk "wbml"),
    Gate.mkOR (Wire.mk "wbhw1") (Wire.mk "wbml") wb_use_way1,
    Gate.mkNOT wb_use_way1 not_wb_w1,
    Gate.mkNOT ref_lru not_ref_lru
  ]

  -- === Write Enables ===
  -- Per way/set: wb_we OR refill_we
  -- wb_safe = wb_detect AND NOT wb_miss_dirty (don't write if victim needs saving)
  let not_wb_miss_dirty := Wire.mk "l2_nwbmd"
  let wb_safe := Wire.mk "l2_wb_safe"
  let wb_safe_gates := [
    Gate.mkNOT wb_miss_dirty not_wb_miss_dirty,
    Gate.mkAND wb_detect not_wb_miss_dirty wb_safe
  ]
  let write_en_gates := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 8).foldl (fun acc2 set =>
      let wm := if way == 0 then not_wb_w1 else wb_use_way1
      let rm := if way == 0 then not_ref_lru else ref_lru
      acc2 ++ [
        Gate.mkAND wb_safe cur_dec[set]! (Wire.mk s!"wbs_{way}_{set}"),
        Gate.mkAND (Wire.mk s!"wbs_{way}_{set}") wm (Wire.mk s!"wbw_{way}_{set}"),
        Gate.mkAND refill_done ref_dec[set]! (Wire.mk s!"rfs_{way}_{set}"),
        Gate.mkAND (Wire.mk s!"rfs_{way}_{set}") rm (Wire.mk s!"rfw_{way}_{set}"),
        Gate.mkOR (Wire.mk s!"wbw_{way}_{set}") (Wire.mk s!"rfw_{way}_{set}") (Wire.mk s!"wen_{way}_{set}")
      ]
    ) []
  ) []

  -- === Write Data Selection ===
  -- write_tag: refill_done ? ref_tag : cur_tag
  let write_tag := (List.range 24).map fun b => Wire.mk s!"wt_{b}"
  let write_tag_mux := (List.range 24).map fun b =>
    Gate.mkMUX cur_tag[b]! ref_tag[b]! refill_done write_tag[b]!
  -- write_data: refill_done ? mem_resp_data : l1d_req_data
  let write_data := (List.range 256).map fun b => Wire.mk s!"wdd_{b}"
  let write_data_mux := (List.range 256).map fun b =>
    Gate.mkMUX l1d_req_data[b]! mem_resp_data[b]! refill_done write_data[b]!
  -- write_dirty: wb → dirty, refill → clean
  let not_refill := Wire.mk "l2_nrf"
  let write_dirty := Wire.mk "wdty"
  let write_dirty_gates := [Gate.mkNOT refill_done not_refill, Gate.mkBUF not_refill write_dirty]

  -- === Storage Next State ===
  -- Tag: MUX(hold, write_tag, write_en)
  let tag_next := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 8).foldl (fun acc2 set =>
      acc2 ++ (List.range 24).map (fun b =>
        Gate.mkMUX (Wire.mk s!"l2_tag_q_w{way}_s{set}_{b}") write_tag[b]!
          (Wire.mk s!"wen_{way}_{set}") (Wire.mk s!"l2_tag_d_w{way}_s{set}_{b}"))
    ) []
  ) []
  -- Data RAM write control: wen per way, addr, data
  -- write_en = OR of wen_{way}_{set} for any set (same as any write_en_gates match for this way)
  let data_ram_wen_gates := (List.range 2).foldl (fun acc way =>
    -- OR-tree of wen_{way}_{set} for all 8 sets
    let wen_wires := (List.range 8).map fun set => Wire.mk s!"wen_{way}_{set}"
    acc ++ [
      Gate.mkOR wen_wires[0]! wen_wires[1]! (Wire.mk s!"l2_dwen_01_w{way}"),
      Gate.mkOR wen_wires[2]! wen_wires[3]! (Wire.mk s!"l2_dwen_23_w{way}"),
      Gate.mkOR wen_wires[4]! wen_wires[5]! (Wire.mk s!"l2_dwen_45_w{way}"),
      Gate.mkOR wen_wires[6]! wen_wires[7]! (Wire.mk s!"l2_dwen_67_w{way}"),
      Gate.mkOR (Wire.mk s!"l2_dwen_01_w{way}") (Wire.mk s!"l2_dwen_23_w{way}") (Wire.mk s!"l2_dwen_03_w{way}"),
      Gate.mkOR (Wire.mk s!"l2_dwen_45_w{way}") (Wire.mk s!"l2_dwen_67_w{way}") (Wire.mk s!"l2_dwen_47_w{way}"),
      Gate.mkOR (Wire.mk s!"l2_dwen_03_w{way}") (Wire.mk s!"l2_dwen_47_w{way}") l2_data_ram_wr_en[way]!
    ]
  ) []
  -- Write addr: refill uses ref_idx, wb uses cur_idx; MUX on refill_done
  let data_ram_waddr_gates := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 3).map (fun i =>
      Gate.mkMUX cur_idx[i]! ref_idx[i]! refill_done (l2_data_ram_wr_addr[way]!)[i]!)
  ) []
  -- Write data: already computed as write_data[b]
  let data_ram_wdata_gates := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 256).map (fun b =>
      Gate.mkBUF write_data[b]! (l2_data_ram_wr_data[way]!)[b]!)
  ) []
  -- Define the actual RAM primitives (read_idx is now available)
  let data_rams := (List.range 2).map fun way =>
    RAMPrimitive.mk s!"l2_data_ram_w{way}" 8 256
      [{ en := l2_data_ram_wr_en[way]!
         addr := l2_data_ram_wr_addr[way]!
         data := l2_data_ram_wr_data[way]! }]
      [{ addr := read_idx
         data := l2_data_ram_rd[way]! }]
      false clock
  -- Valid: OR(hold, write_en)
  let valid_next := (List.range 2).foldl (fun acc way =>
    acc ++ (List.range 8).map (fun set =>
      Gate.mkOR valid_q[way * 8 + set]! (Wire.mk s!"wen_{way}_{set}") valid_d[way * 8 + set]!)
  ) []
  -- Dirty: MUX(hold, write_dirty, write_en), with clearing for wb_miss_dirty victim
  -- When is_wb_req AND wb_is_write_q, clear the dirty bit for wb_way_q at ref_dec set
  let wb_clear_dirty := Wire.mk "l2_wbcd"
  let wb_clear_dirty_gate := Gate.mkAND is_wb_req wb_is_write_q wb_clear_dirty
  let dirty_next := (List.range 2).foldl (fun acc way =>
    acc ++ ((List.range 8).map (fun set =>
      let idx := way * 8 + set
      let way_match := if way == 0 then Wire.mk "l2_nwbwq" else wb_way_q
      [Gate.mkAND way_match ref_dec[set]! (Wire.mk s!"wbcs_{way}_{set}"),
       Gate.mkAND (Wire.mk s!"wbcs_{way}_{set}") wb_clear_dirty (Wire.mk s!"wbcl_{way}_{set}"),
       Gate.mkMUX dirty_q[idx]! (Wire.mk "l2_const_zero") (Wire.mk s!"wbcl_{way}_{set}") (Wire.mk s!"dh_{idx}"),
       Gate.mkMUX (Wire.mk s!"dh_{idx}") write_dirty (Wire.mk s!"wen_{way}_{set}") dirty_d[idx]!]
    )).flatten
  ) []
  let not_wb_way_q := Wire.mk "l2_nwbwq"
  let not_wb_way_q_gate := Gate.mkNOT wb_way_q not_wb_way_q
  -- LRU: update on hit, wb, or refill
  let lru_next := (List.range 8).foldl (fun acc set =>
    acc ++ [
      Gate.mkOR hit_detect wb_safe (Wire.mk s!"lca_{set}"),
      Gate.mkAND (Wire.mk s!"lca_{set}") cur_dec[set]! (Wire.mk s!"lcu_{set}"),
      Gate.mkAND refill_done ref_dec[set]! (Wire.mk s!"lru_{set}"),
      Gate.mkOR (Wire.mk s!"lcu_{set}") (Wire.mk s!"lru_{set}") (Wire.mk s!"lua_{set}"),
      -- new_lru: refill_done ? NOT ref_lru : NOT wb_use_way1
      Gate.mkMUX not_wb_w1 not_ref_lru refill_done (Wire.mk s!"lnv_{set}"),
      Gate.mkMUX lru_q[set]! (Wire.mk s!"lnv_{set}") (Wire.mk s!"lua_{set}") lru_d[set]!
    ]
  ) []

  -- === Stall Signals ===
  let stall_gates := [
    -- stall_i = NOT idle OR (idle AND D-side priority AND I-side requesting)
    Gate.mkAND is_idle arb_sel_d (Wire.mk "l2_dp"),
    Gate.mkAND (Wire.mk "l2_dp") l1i_req_valid (Wire.mk "l2_ib"),
    Gate.mkOR not_idle (Wire.mk "l2_ib") stall_i,
    Gate.mkOR not_idle wb_miss_dirty stall_d
  ]

  -- === Assemble ===
  { name := "L2Cache"
    inputs := [clock, reset, l1i_req_valid] ++ l1i_req_addr ++
              [l1d_req_valid] ++ l1d_req_addr ++ [l1d_req_we] ++ l1d_req_data ++
              [mem_resp_valid] ++ mem_resp_data
    outputs := [l1i_resp_valid] ++ l1i_resp_data ++
               [l1d_resp_valid] ++ l1d_resp_data ++
               [mem_req_valid] ++ mem_req_addr ++ [mem_req_we] ++ mem_req_data ++
               [stall_i, stall_d]
    gates := fsm_dffs ++ [src_dff] ++ pend_dffs ++ lat_idx_dffs ++ [lat_way_dff] ++
             valid_dffs ++ dirty_dffs ++ lru_dffs ++
             wb_buf_dffs ++ wb_tag_dffs ++ [wb_dirty_dff, wb_is_write_dff, wb_way_dff] ++
             const_zero_gates ++ arb_gates ++ arb_addr_mux ++
             not_cur_idx_gates ++ cur_dec_gates ++ not_ref_idx_gates ++ ref_dec_gates ++
             read_idx_mux ++ valid_mux_gates ++ hit_gates ++ way_data_mux ++
             fsm_decode_gates ++ [read_way1_mux] ++
             detect_gates ++
             cur_lru_gates ++
             victim_dirty_gates ++ victim_valid_gates ++ miss_detect_gates ++
             wb_miss_dirty_gates ++ [capture_victim_gate] ++
             resp_valid_gates ++ resp_mux_i ++ resp_mux_d ++
             victim_data_gates ++ victim_tag_gates ++
             wb_buf_next ++ wb_tag_next ++ [wb_dirty_next] ++
             wb_is_write_next ++ [wb_way_next] ++
             mem_req_gates ++ fsm_next_gates ++
             [capture_pend_gate] ++ pend_next ++ src_next ++ lat_idx_next ++ [lat_way_next] ++
             ref_lru_gates ++ way_sel_gates ++ wb_safe_gates ++ write_en_gates ++
             write_tag_mux ++ write_data_mux ++ write_dirty_gates ++
             tag_next ++ data_ram_wen_gates ++ data_ram_waddr_gates ++ data_ram_wdata_gates ++
             valid_next ++ [wb_clear_dirty_gate, not_wb_way_q_gate] ++ dirty_next ++
             lru_next ++ stall_gates
    instances := tag_instances ++
                 tag_mux_instances ++ tag_cmp_instances
    rams := data_rams
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

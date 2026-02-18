/-
RISCV/Memory/Cache/L1ICache.lean - L1 Instruction Cache

Direct-mapped, 8-set, 32B line, read-only instruction cache.
Behavioral model + structural circuit.

On hit: returns word in 1 cycle.
On miss: sends refill request to L2, waits for 8-word line, installs, then retries.
FENCE.I: invalidates all lines.
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

/-- L1 Instruction Cache State: 8 direct-mapped lines. -/
structure L1ICacheState where
  /-- 8 direct-mapped cache lines (24-bit tags) -/
  lines : Fin 8 → CacheLine 24
  /-- FSM state -/
  fsm : L1ICacheFSM
  /-- Address of in-flight refill -/
  refillAddr : UInt32
  /-- Word counter for multi-word refill -/
  refillCount : Fin 8

instance : Inhabited L1ICacheState where
  default := {
    lines := fun _ => CacheLine.empty
    fsm := .IDLE
    refillAddr := 0
    refillCount := 0
  }

/-- Create an empty L1I cache. -/
def L1ICacheState.empty : L1ICacheState := default

/-- Lookup an address in the L1I cache. Returns `some word` on hit, `none` on miss. -/
def L1ICacheState.lookup (s : L1ICacheState) (addr : UInt32) : Option UInt32 :=
  let idx := extractL1IIndex addr
  let tag := extractL1ITag addr
  let wordOff := extractWordOffset addr
  let line := s.lines idx
  if line.valid && line.tag == tag then
    some (line.data wordOff)
  else
    none

/-- Install a complete cache line after refill. -/
def L1ICacheState.refill (s : L1ICacheState) (addr : UInt32)
    (lineData : Fin 8 → UInt32) : L1ICacheState :=
  let idx := extractL1IIndex addr
  let tag := extractL1ITag addr
  { s with
    lines := fun i =>
      if i == idx then
        { valid := true, dirty := false, tag := tag, data := lineData }
      else
        s.lines i
  }

/-- Invalidate all lines (FENCE.I). -/
def L1ICacheState.invalidateAll (s : L1ICacheState) : L1ICacheState :=
  { s with lines := fun _ => CacheLine.empty }

/-- Step the FSM. Returns (newState, missReqValid, missReqAddr, stall). -/
def L1ICacheState.step (s : L1ICacheState) (reqValid : Bool) (reqAddr : UInt32)
    (refillValid : Bool) (refillData : Fin 8 → UInt32)
    (fenceI : Bool) : L1ICacheState × Bool × UInt32 × Bool :=
  if fenceI then
    -- FENCE.I: invalidate everything, return to IDLE
    let s' := s.invalidateAll
    ({ s' with fsm := .IDLE }, false, 0, true)
  else match s.fsm with
  | .IDLE =>
    if reqValid then
      match s.lookup reqAddr with
      | some _ => (s, false, 0, false)  -- hit, no stall
      | none =>
        -- miss: transition to REFILL_REQ
        ({ s with fsm := .REFILL_REQ, refillAddr := reqAddr, refillCount := 0 },
         true, reqAddr, true)
    else
      (s, false, 0, false)
  | .REFILL_REQ =>
    -- Request sent, wait for response
    ({ s with fsm := .REFILL_WAIT }, false, 0, true)
  | .REFILL_WAIT =>
    if refillValid then
      -- Refill complete: install line and return to IDLE
      let s' := s.refill s.refillAddr refillData
      ({ s' with fsm := .IDLE }, false, 0, false)
    else
      -- Still waiting
      (s, false, 0, true)

/-! ## Structural Circuit -/

/-- Build the L1I Cache structural circuit.

    Ports:
    - Inputs: clock, reset, req_valid, req_addr[31:0], refill_valid, refill_data[255:0], fence_i
    - Outputs: resp_valid, resp_data[31:0], miss_valid, miss_addr[31:0], stall

    Internal structure:
    - 8× tag storage (24 bits each) via Register instances
    - 8× valid bits via DFF
    - 8× data storage (256 bits each) via Register instances
    - EqualityComparator24 for tag match
    - Mux8x32 for word select
    - FSM: 2-bit state register
-/
def mkL1ICache : Circuit :=
  -- Port wires
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let req_valid := Wire.mk "req_valid"
  let req_addr := (List.range 32).map fun i => Wire.mk s!"req_addr_{i}"
  let refill_valid := Wire.mk "refill_valid"
  -- refill_data: 8 words × 32 bits = 256 bits
  let refill_data := (List.range 256).map fun i => Wire.mk s!"refill_data_{i}"
  let fence_i := Wire.mk "fence_i"

  -- Outputs
  let resp_valid := Wire.mk "resp_valid"
  let resp_data := (List.range 32).map fun i => Wire.mk s!"resp_data_{i}"
  let miss_valid := Wire.mk "miss_valid"
  let miss_addr := (List.range 32).map fun i => Wire.mk s!"miss_addr_{i}"
  let stall := Wire.mk "stall"

  -- Extract index bits (addr[7:5]) for set selection
  let idx_bits := [req_addr[5]!, req_addr[6]!, req_addr[7]!]
  -- Extract tag bits (addr[31:8])
  let tag_bits := (List.range 24).map fun i => req_addr[i + 8]!
  -- Extract word offset bits (addr[4:2])
  let word_sel := [req_addr[2]!, req_addr[3]!, req_addr[4]!]

  -- FSM state register (2 bits: IDLE=00, REFILL_REQ=01, REFILL_WAIT=10)
  let fsm_d := (List.range 2).map fun i => Wire.mk s!"fsm_d_{i}"
  let fsm_q := (List.range 2).map fun i => Wire.mk s!"fsm_q_{i}"
  let fsm_gates := (List.range 2).map fun i =>
    Gate.mkDFF fsm_d[i]! clock reset fsm_q[i]!

  -- Miss Address Register (MAR): captures req_addr on miss_detect.
  -- Needed because CPU's fetch_pc may change during REFILL_WAIT (e.g., branch).
  let mar_d := (List.range 32).map fun i => Wire.mk s!"mar_d_{i}"
  let mar_q := (List.range 32).map fun i => Wire.mk s!"mar_q_{i}"
  let mar_gates := (List.range 32).map fun i =>
    Gate.mkDFF mar_d[i]! clock reset mar_q[i]!

  -- Refill address decomposition (from MAR, used for refill writes)
  let refill_idx_bits := [mar_q[5]!, mar_q[6]!, mar_q[7]!]
  let refill_tag_bits := (List.range 24).map fun i => mar_q[i + 8]!

  -- Tag storage: 8 sets × 24-bit tags (using Register24 instances)
  let tag_instances := (List.range 8).map fun set =>
    let d_wires := (List.range 24).map fun b => Wire.mk s!"tag_d_{set}_{b}"
    let q_wires := (List.range 24).map fun b => Wire.mk s!"tag_q_{set}_{b}"
    (CircuitInstance.mk "Register24" s!"u_tag_{set}"
      ((List.range 24).map (fun b => (s!"d_{b}", d_wires[b]!)) ++
       [("clock", clock), ("reset", reset)] ++
       (List.range 24).map (fun b => (s!"q_{b}", q_wires[b]!))),
     d_wires, q_wires)

  -- Valid bits: 8 DFFs
  let valid_d := (List.range 8).map fun i => Wire.mk s!"valid_d_{i}"
  let valid_q := (List.range 8).map fun i => Wire.mk s!"valid_q_{i}"
  let valid_gates := (List.range 8).map fun i =>
    Gate.mkDFF valid_d[i]! clock reset valid_q[i]!

  -- Data storage: single RAM (8 entries × 256 bits)
  -- Replaces 8× Register256 + 8× Mux8x32 (line set muxes)
  let data_ram_rd := (List.range 256).map fun b => Wire.mk s!"sel_line_{b}"
  let data_ram := RAMPrimitive.mk "data_ram" 8 256
    [{ en := Wire.mk "refill_done"  -- write on refill completion
       addr := refill_idx_bits
       data := refill_data }]
    [{ addr := idx_bits
       data := data_ram_rd }]
    false clock

  -- Refill decoder: 3-to-8 from MAR index bits (for refill writes)
  let not_refill_idx := (List.range 3).map fun i => Wire.mk s!"not_ridx_{i}"
  let not_refill_idx_gates := (List.range 3).map fun i =>
    Gate.mkNOT refill_idx_bits[i]! not_refill_idx[i]!

  let refill_dec_out := (List.range 8).map fun i => Wire.mk s!"rdec_idx_{i}"
  let refill_dec_and_wires := (List.range 8).map fun i =>
    let b0 := if i % 2 == 0 then not_refill_idx[0]! else refill_idx_bits[0]!
    let b1 := if (i / 2) % 2 == 0 then not_refill_idx[1]! else refill_idx_bits[1]!
    let b2 := if (i / 4) % 2 == 0 then not_refill_idx[2]! else refill_idx_bits[2]!
    (b0, b1, b2, Wire.mk s!"rdec_tmp01_{i}")

  let refill_dec_gates := (List.range 8).foldl (fun acc i =>
    let (b0, b1, b2, tmp) := refill_dec_and_wires[i]!
    acc ++ [
      Gate.mkAND b0 b1 tmp,
      Gate.mkAND tmp b2 refill_dec_out[i]!
    ]
  ) []

  -- Tag comparator for the selected set
  -- First: mux the tag from the selected set (8:1 mux of 24-bit values)
  let sel_tag := (List.range 24).map fun b => Wire.mk s!"sel_tag_{b}"
  let tag_mux_inst := CircuitInstance.mk "Mux8x24" "u_tag_mux"
    (-- 8 inputs × 24 bits (MuxTree port naming: in{i}_{j})
     (List.range 8).foldl (fun acc set =>
       acc ++ (List.range 24).map (fun b =>
         (s!"in{set}_{b}", Wire.mk s!"tag_q_{set}_{b}"))
     ) [] ++
     -- 3-bit select
     (List.range 3).map (fun i => (s!"sel_{i}", idx_bits[i]!)) ++
     -- 24-bit output
     (List.range 24).map (fun b => (s!"out_{b}", sel_tag[b]!)))

  -- Selected valid bit (8:1 mux of 1-bit values)
  let sel_valid := Wire.mk "sel_valid"
  -- Use a simple gate-based 8:1 mux for valid bit
  let _sel_valid_decoded := (List.range 8).map fun i => Wire.mk s!"sel_valid_and_{i}"
  -- Decode index and AND with valid
  let not_idx := (List.range 3).map fun i => Wire.mk s!"not_idx_{i}"
  let not_idx_gates := (List.range 3).map fun i =>
    Gate.mkNOT idx_bits[i]! not_idx[i]!

  -- 3-to-8 decoder for set selection (inline, for muxing valid bit)
  let dec_out := (List.range 8).map fun i => Wire.mk s!"dec_idx_{i}"
  let dec_and_wires := (List.range 8).map fun i =>
    let b0 := if i % 2 == 0 then not_idx[0]! else idx_bits[0]!
    let b1 := if (i / 2) % 2 == 0 then not_idx[1]! else idx_bits[1]!
    let b2 := if (i / 4) % 2 == 0 then not_idx[2]! else idx_bits[2]!
    (b0, b1, b2, Wire.mk s!"dec_tmp01_{i}")

  let dec_gates := (List.range 8).foldl (fun acc i =>
    let (b0, b1, b2, tmp) := dec_and_wires[i]!
    acc ++ [
      Gate.mkAND b0 b1 tmp,
      Gate.mkAND tmp b2 dec_out[i]!
    ]
  ) []

  -- AND decoded select with valid bits
  let valid_and_sel := (List.range 8).map fun i => Wire.mk s!"valid_and_sel_{i}"
  let valid_sel_gates := (List.range 8).map fun i =>
    Gate.mkAND dec_out[i]! valid_q[i]! valid_and_sel[i]!

  -- OR-tree to get sel_valid
  let valid_or_tmp := (List.range 6).map fun i => Wire.mk s!"valid_or_tmp_{i}"
  let valid_or_gates := [
    Gate.mkOR valid_and_sel[0]! valid_and_sel[1]! valid_or_tmp[0]!,
    Gate.mkOR valid_and_sel[2]! valid_and_sel[3]! valid_or_tmp[1]!,
    Gate.mkOR valid_and_sel[4]! valid_and_sel[5]! valid_or_tmp[2]!,
    Gate.mkOR valid_and_sel[6]! valid_and_sel[7]! valid_or_tmp[3]!,
    Gate.mkOR valid_or_tmp[0]! valid_or_tmp[1]! valid_or_tmp[4]!,
    Gate.mkOR valid_or_tmp[2]! valid_or_tmp[3]! valid_or_tmp[5]!,
    Gate.mkOR valid_or_tmp[4]! valid_or_tmp[5]! sel_valid
  ]

  -- Tag comparator
  let tag_match := Wire.mk "tag_match"
  let tag_cmp_inst := CircuitInstance.mk "EqualityComparator24" "u_tag_cmp"
    ((List.range 24).map (fun b => (s!"a_{b}", sel_tag[b]!)) ++
     (List.range 24).map (fun b => (s!"b_{b}", tag_bits[b]!)) ++
     [("eq", tag_match)])

  -- Hit = valid AND tag_match
  let hit := Wire.mk "hit"
  let hit_gate := Gate.mkAND sel_valid tag_match hit

  -- Word select: mux 1 of 8 words from the selected line (data_ram read → sel_line)
  -- sel_line[255:0] is driven by the data_ram read port
  let word_mux_inst := CircuitInstance.mk "Mux8x32" "u_word_mux"
    ((List.range 8).foldl (fun acc wordIdx =>
      acc ++ (List.range 32).map (fun b =>
        (s!"in{wordIdx}_{b}", Wire.mk s!"sel_line_{wordIdx * 32 + b}"))
    ) [] ++
    (List.range 3).map (fun i => (s!"sel_{i}", word_sel[i]!)) ++
    (List.range 32).map (fun b => (s!"out_{b}", resp_data[b]!)))

  -- FSM logic
  let is_idle := Wire.mk "is_idle"
  let not_fsm0 := Wire.mk "not_fsm0"
  let not_fsm1 := Wire.mk "not_fsm1"
  let fsm_logic_gates := [
    Gate.mkNOT fsm_q[0]! not_fsm0,
    Gate.mkNOT fsm_q[1]! not_fsm1,
    Gate.mkAND not_fsm0 not_fsm1 is_idle  -- IDLE = 00
  ]

  -- miss detection: IDLE AND req_valid AND NOT hit
  let not_hit := Wire.mk "not_hit"
  let miss_detect := Wire.mk "miss_detect"
  let miss_tmp := Wire.mk "miss_tmp"
  let miss_gates := [
    Gate.mkNOT hit not_hit,
    Gate.mkAND is_idle req_valid miss_tmp,
    Gate.mkAND miss_tmp not_hit miss_detect
  ]

  -- resp_valid = req_valid AND hit AND is_idle
  let resp_tmp := Wire.mk "resp_tmp"
  let resp_gates := [
    Gate.mkAND req_valid hit resp_tmp,
    Gate.mkAND resp_tmp is_idle resp_valid
  ]

  -- miss_valid = miss_detect OR is_refill_req OR is_refill_wait
  -- Must persist while waiting, so L2 can accept when it becomes idle
  let miss_valid_gate := Gate.mkOR miss_detect (Wire.mk "not_idle_for_miss") miss_valid
  let not_idle_miss_gates := [
    Gate.mkOR (Wire.mk "is_refill_req") (Wire.mk "is_refill_wait") (Wire.mk "not_idle_for_miss")
  ]

  -- miss_addr = line-aligned address. Use MAR (mar_q) when not idle, req_addr in IDLE.
  -- MAR captures req_addr on miss_detect and holds it through REFILL_REQ/REFILL_WAIT.
  let miss_addr_gates := (List.range 32).map fun i =>
    if i < 5 then
      -- Clear low 5 bits for line alignment
      Gate.mkBUF (Wire.mk "const_zero") (miss_addr[i]!)
    else
      Gate.mkMUX req_addr[i]! mar_q[i]! (Wire.mk "not_idle_for_miss") miss_addr[i]!

  -- stall = NOT is_idle OR miss_detect
  let not_idle := Wire.mk "not_idle"
  let stall_gates := [
    Gate.mkNOT is_idle not_idle,
    Gate.mkOR not_idle miss_detect stall
  ]

  -- FSM next-state logic
  -- In IDLE: if miss → go to REFILL_REQ (01)
  -- In REFILL_REQ: go to REFILL_WAIT (10)
  -- In REFILL_WAIT: if refill_valid → go to REFILL_DONE (11), else stay
  -- In REFILL_DONE: stay until req_valid (CPU re-requests), then go to IDLE (00)
  --   This prevents the stall→ifetch_valid feedback loop from causing
  --   a 1-cycle gap where stall=0 but req_valid=0, which would let the CPU
  --   advance its PC without actually fetching the instruction.
  let is_refill_req := Wire.mk "is_refill_req"
  let is_refill_wait := Wire.mk "is_refill_wait"
  let is_refill_done := Wire.mk "is_refill_done"
  let refill_done := Wire.mk "refill_done"
  let not_req_valid := Wire.mk "not_req_valid"
  let stay_done := Wire.mk "stay_done"
  let fsm_next_gates := [
    Gate.mkAND fsm_q[0]! not_fsm1 is_refill_req,   -- 01
    Gate.mkAND fsm_q[1]! not_fsm0 is_refill_wait,   -- 10
    Gate.mkAND fsm_q[0]! fsm_q[1]! is_refill_done,  -- 11
    Gate.mkAND is_refill_wait refill_valid refill_done,
    Gate.mkNOT req_valid not_req_valid,
    Gate.mkAND is_refill_done not_req_valid stay_done,  -- stay in REFILL_DONE
    -- fsm_d[0] = miss_detect (IDLE→REFILL_REQ)
    --            OR refill_done (REFILL_WAIT→REFILL_DONE)
    --            OR stay_done (REFILL_DONE stays until req_valid)
    Gate.mkOR miss_detect refill_done (Wire.mk "fsm_d0_tmp"),
    Gate.mkOR (Wire.mk "fsm_d0_tmp") stay_done fsm_d[0]!,
    -- fsm_d[1] = is_refill_req (REFILL_REQ→REFILL_WAIT)
    --            OR (is_refill_wait AND NOT refill_valid) (stay in REFILL_WAIT)
    --            OR refill_done (REFILL_WAIT→REFILL_DONE)
    --            OR stay_done (REFILL_DONE stays until req_valid)
    Gate.mkNOT refill_valid (Wire.mk "not_refill_valid"),
    Gate.mkAND is_refill_wait (Wire.mk "not_refill_valid") (Wire.mk "stay_wait"),
    Gate.mkOR is_refill_req (Wire.mk "stay_wait") (Wire.mk "fsm_d1_tmp"),
    Gate.mkOR (Wire.mk "fsm_d1_tmp") refill_done (Wire.mk "fsm_d1_tmp2"),
    Gate.mkOR (Wire.mk "fsm_d1_tmp2") stay_done fsm_d[1]!
  ]

  -- MAR capture: save req_addr on miss_detect, hold otherwise
  let mar_capture_gates := (List.range 32).map fun i =>
    Gate.mkMUX mar_q[i]! req_addr[i]! miss_detect mar_d[i]!

  -- FENCE.I: clear all valid bits on fence_i
  -- valid_d[i] = (current write_en AND set_match) OR (existing valid AND NOT fence_i)
  -- For simplicity in this structural model: on refill_done, write to refill set;
  -- on fence_i, clear all. Otherwise, hold current value.
  let not_fence_i := Wire.mk "not_fence_i"
  let valid_next_gates := [Gate.mkNOT fence_i not_fence_i] ++
    (List.range 8).foldl (fun acc i =>
      let hold := Wire.mk s!"valid_hold_{i}"
      let refill_set_match := Wire.mk s!"refill_set_match_{i}"
      let _refill_write := Wire.mk s!"refill_write_{i}"
      acc ++ [
        -- hold = valid_q AND NOT fence_i
        Gate.mkAND valid_q[i]! not_fence_i hold,
        -- refill_set_match = refill_done AND rdec_idx[i] (use MAR decoder)
        Gate.mkAND refill_done refill_dec_out[i]! refill_set_match,
        -- valid_d = refill_write OR hold
        Gate.mkOR refill_set_match hold valid_d[i]!
      ]
    ) []

  -- Tag write logic: on refill, write tag from MAR (not current req_addr)
  let tag_write_gates := (List.range 8).foldl (fun acc set =>
    let tag_d_wires := (List.range 24).map fun b => Wire.mk s!"tag_d_{set}_{b}"
    let tag_q_wires := (List.range 24).map fun b => Wire.mk s!"tag_q_{set}_{b}"
    let refill_match := Wire.mk s!"refill_set_match_{set}"
    acc ++ (List.range 24).foldl (fun acc2 b =>
      -- tag_d = MUX(refill_match, refill_tag_bits[b], tag_q[b])
      acc2 ++ [Gate.mkMUX tag_q_wires[b]! refill_tag_bits[b]! refill_match tag_d_wires[b]!]
    ) []
  ) []

  -- Data write logic: handled by data_ram write port (refill_done + refill_idx)

  -- Constant zero wire (for miss_addr low bits)
  let _const_zero_gate := Gate.mkBUF reset (Wire.mk "const_zero_pre")
  -- Actually we need a proper const 0. Use NOT of DFF_SET or simpler approach:
  -- Just AND any wire with its NOT to get 0
  let const_zero_gates := [
    Gate.mkNOT reset (Wire.mk "not_reset_for_zero"),
    Gate.mkAND reset (Wire.mk "not_reset_for_zero") (Wire.mk "const_zero")
  ]

  -- Collect all gates
  let allGates :=
    fsm_gates ++ mar_gates ++ valid_gates ++
    not_idx_gates ++ dec_gates ++
    not_refill_idx_gates ++ refill_dec_gates ++
    valid_sel_gates ++ valid_or_gates ++
    [hit_gate] ++ fsm_logic_gates ++ miss_gates ++ resp_gates ++
    [miss_valid_gate] ++ not_idle_miss_gates ++ miss_addr_gates ++ stall_gates ++
    fsm_next_gates ++ mar_capture_gates ++
    valid_next_gates ++ tag_write_gates ++
    const_zero_gates

  -- Collect all instances
  let allInstances :=
    (tag_instances.map (·.1)) ++
    [tag_mux_inst, tag_cmp_inst] ++
    [word_mux_inst]

  { name := "L1ICache"
    inputs := [clock, reset, req_valid] ++ req_addr ++ [refill_valid] ++ refill_data ++ [fence_i]
    outputs := [resp_valid] ++ resp_data ++ [miss_valid] ++ miss_addr ++ [stall]
    gates := allGates
    instances := allInstances
    rams := [data_ram]
    signalGroups := [
      { name := "req_addr", width := 32, wires := req_addr },
      { name := "refill_data", width := 256, wires := refill_data },
      { name := "resp_data", width := 32, wires := resp_data },
      { name := "miss_addr", width := 32, wires := miss_addr }
    ]
  }

end Shoumei.RISCV.Memory.Cache

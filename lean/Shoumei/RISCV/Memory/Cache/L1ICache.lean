/-
RISCV/Memory/Cache/L1ICache.lean - L1 Instruction Cache

Direct-mapped, 8-set, 32B line, read-only instruction cache.
Behavioral model + structural circuit.

On hit: returns word in 1 cycle.
On miss: sends refill request to L2, waits for 8-word line, installs, then retries.
FENCE.I: invalidates all lines.
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

/-- Build the L1I Cache structural circuit for a geometry.

    Ports:
    - Inputs: clock, reset, req_valid, req_addr[31:0], refill_valid,
      refill_data[lineBits-1:0], fence_i
    - Outputs: resp_valid, resp_data[31:0], resp_data_1[31:0], miss_valid,
      miss_addr[31:0], stall, last_word

    Structure follows the geometry (`CacheGeom`, default = the historical
    8-set direct-mapped 32-byte-line cache):

    - ways × sets tag words (`Register{tagBits}`), valid bits, and one data RAM
      per way (`sets` deep, one line wide);
    - one `Mux{sets}x{tagBits}` and one `EqualityComparator{tagBits}` per way;
    - one tree-PLRU per set picks the refill way (degenerate at one way);
    - word selects are `wordBits` wide and the extract muxes `Mux{words}x32`;
    - FSM: 2-bit state register.
-/
def mkL1ICache (g : CacheGeom := CacheGeom.default) : Circuit :=
  let sets := g.l1iSets
  let ways := g.l1iWays
  let lineBits := g.lineBytes * 8
  let words := g.lineBytes / 4
  let wordBits := log2Ceil words
  let offsetBits := log2Ceil g.lineBytes
  let idxBits := log2Ceil sets
  let tagBits := 32 - idxBits - offsetBits
  let lines := ways * sets

  -- Port wires
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let req_valid := Wire.mk "req_valid"
  let req_addr := (List.range 32).map fun i => Wire.mk s!"req_addr_{i}"
  let refill_valid := Wire.mk "refill_valid"
  -- refill_data carries one whole cache line
  let refill_data := (List.range lineBits).map fun i => Wire.mk s!"refill_data_{i}"
  let fence_i := Wire.mk "fence_i"

  -- Outputs
  let resp_valid := Wire.mk "resp_valid"
  let resp_data := (List.range 32).map fun i => Wire.mk s!"resp_data_{i}"
  let resp_data_1 := (List.range 32).map fun i => Wire.mk s!"resp_data_1_{i}"
  let miss_valid := Wire.mk "miss_valid"
  let miss_addr := (List.range 32).map fun i => Wire.mk s!"miss_addr_{i}"
  let stall := Wire.mk "stall"
  -- last_word: high when the word select is all ones (the last word of the
  -- line), so slot 1 of a dual fetch wraps instead of reading past the line
  let last_word := Wire.mk "last_word"

  -- Constant wires: zero from reset AND NOT reset, one as its complement. The
  -- one marks the single way's victim when there is nothing to choose.
  let const_zero := Wire.mk "const_zero"
  let const_one := Wire.mk "const_one"
  let const_gates := [
    Gate.mkNOT reset (Wire.mk "not_reset_for_zero"),
    Gate.mkAND reset (Wire.mk "not_reset_for_zero") const_zero,
    Gate.mkNOT const_zero const_one
  ]

  -- Extract index bits (addr[offsetBits+idxBits-1:offsetBits]) for set selection
  let idx_bits := (List.range idxBits).map fun i => req_addr[offsetBits + i]!
  -- Extract tag bits (above the index)
  let tag_bits := (List.range tagBits).map fun i => req_addr[offsetBits + idxBits + i]!
  -- Extract the word select: the offset field above the two byte bits
  -- (addr[offsetBits-1:2])
  let word_sel := (List.range wordBits).map fun i => req_addr[2 + i]!

  -- FSM state register (2 bits: IDLE=00, REFILL_REQ=01, REFILL_WAIT=10,
  -- REFILL_DONE=11)
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
  let refill_idx_bits := (List.range idxBits).map fun i => mar_q[offsetBits + i]!
  let refill_tag_bits := (List.range tagBits).map fun i => mar_q[offsetBits + idxBits + i]!

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
  let valid_gates := (List.range lines).map fun i =>
    Gate.mkDFF valid_d[i]! clock reset valid_q[i]!

  -- Data storage: one RAM per way (sets deep, a whole line wide)
  let sel_line_w := (List.range ways).map fun way =>
    (List.range lineBits).map fun b => Wire.mk s!"sel_line_w{way}_{b}"
  let ram_wr_en := (List.range ways).map fun way => Wire.mk s!"ram_wr_en_w{way}"
  let data_rams := (List.range ways).map fun way =>
    RAMPrimitive.mk s!"data_ram_w{way}" sets lineBits
      [{ en := ram_wr_en[way]!, addr := refill_idx_bits, data := refill_data }]
      [{ addr := idx_bits, data := sel_line_w[way]! }]
      false clock
      (portKind := .r1w1)

  -- Set decoders: one for the request index, one for the refill index
  let req_dec := (List.range sets).map fun st => Wire.mk s!"req_dec_{st}"
  let refill_dec := (List.range sets).map fun st => Wire.mk s!"refill_dec_{st}"
  let req_dec_inst := CircuitInstance.mk s!"Decoder{idxBits}" "u_req_dec"
    ((List.range idxBits).map (fun i => (s!"in_{i}", idx_bits[i]!)) ++
     (List.range sets).map (fun st => (s!"out_{st}", req_dec[st]!)))
  let refill_dec_inst := CircuitInstance.mk s!"Decoder{idxBits}" "u_refill_dec"
    ((List.range idxBits).map (fun i => (s!"in_{i}", refill_idx_bits[i]!)) ++
     (List.range sets).map (fun st => (s!"out_{st}", refill_dec[st]!)))

  -- Per-way request tag: mux the selected set's tag out of that way's storage
  let sel_tag := (List.range ways).map fun way =>
    (List.range tagBits).map fun b => Wire.mk s!"sel_tag_w{way}_{b}"
  let tag_mux_insts := (List.range ways).map fun way =>
    CircuitInstance.mk s!"Mux{sets}x{tagBits}" s!"u_tag_mux_w{way}"
      ((List.range sets).foldl (fun acc set =>
        acc ++ (List.range tagBits).map (fun b =>
          (s!"in{set}_{b}", Wire.mk s!"tag_q_w{way}_s{set}_{b}"))) [] ++
       (List.range idxBits).map (fun i => (s!"sel_{i}", idx_bits[i]!)) ++
       (List.range tagBits).map (fun b => (s!"out_{b}", sel_tag[way]![b]!)))

  -- Per-way tag comparison
  let tag_match := (List.range ways).map fun way => Wire.mk s!"tag_match_w{way}"
  let tag_cmp_insts := (List.range ways).map fun way =>
    CircuitInstance.mk s!"EqualityComparator{tagBits}" s!"u_tag_cmp_w{way}"
      ((List.range tagBits).map (fun b => (s!"a_{b}", sel_tag[way]![b]!)) ++
       (List.range tagBits).map (fun b => (s!"b_{b}", tag_bits[b]!)) ++
       [("eq", tag_match[way]!)])

  -- Per-way valid select = OR over sets of (set select AND that line's valid)
  let way_valid_sel := (List.range ways).map fun w => Wire.mk s!"way_valid_sel_{w}"
  let way_hit := (List.range ways).map fun w => Wire.mk s!"way{w}_hit"
  let way_sel_gates : List Gate := List.flatten ((List.range ways).map fun w =>
    let t := (List.range sets).map fun st => Wire.mk s!"way_valid_and_w{w}_{st}"
    List.flatten ((List.range sets).map fun st =>
      [Gate.mkAND req_dec[st]! valid_q[w * sets + st]! t[st]!])
    ++ mkOrTree t way_valid_sel[w]!
    ++ [Gate.mkAND way_valid_sel[w]! tag_match[w]! way_hit[w]!])

  -- Hit = any way's valid select AND tag match.  At one way the OR-tree
  -- reduces to a buffer.
  let hit := Wire.mk "hit"
  let hit_gate := mkOrTree way_hit hit

  -- Replacement: one tree-PLRU per set.  At one way there is nothing to
  -- choose, so the victim is a constant.
  let refill_victim := (List.range ways).map fun w => Wire.mk s!"refill_victim_oh_{w}"
  let plru_victim := (List.range sets).map fun st =>
    (List.range ways).map fun w => Wire.mk s!"plru_victim_{st}_{w}"
  let plru_upd_en := (List.range sets).map fun st => Wire.mk s!"plru_upd_en_{st}"
  let plru_upd_way := (List.range sets).map fun st =>
    (List.range ways).map fun w => Wire.mk s!"plru_upd_way_{st}_{w}"
  -- One-hot victim of the requested set (used for the stale line below)
  let req_victim := (List.range ways).map fun w => Wire.mk s!"req_victim_oh_{w}"
  -- Pick the victim way of a set out of the per-set PLRUs.  At one way there is
  -- nothing to choose, so the victim is a constant.
  let pickVictim (dec : List Wire) (out : List Wire) : List Gate :=
    if ways == 1 then
      [Gate.mkBUF const_one out[0]!]
    else List.flatten ((List.range ways).map fun w =>
      let t := (List.range sets).map fun st => Wire.mk s!"{out[w]!.name}_and_{st}"
      List.flatten ((List.range sets).map fun st =>
        [Gate.mkAND dec[st]! plru_victim[st]![w]! t[st]!])
      ++ mkOrTree t out[w]!)
  let victim_gates : List Gate := pickVictim refill_dec refill_victim
  let req_victim_gates : List Gate := pickVictim req_dec req_victim
  -- Update source: a refill fills the victim way, an accepted fetch touches the
  -- hitting way.  One set never sees both: while a refill completes, that set's
  -- line is still invalid, so it cannot hit.
  let plru_gates : List Gate :=
    (List.range sets).map (fun st => Gate.mkAND (Wire.mk "refill_done") refill_dec[st]!
      (Wire.mk s!"plru_rf_evt_{st}")) ++
    (List.range sets).map (fun st => Gate.mkAND resp_valid req_dec[st]!
      (Wire.mk s!"plru_hit_evt_{st}")) ++
    (List.range sets).map (fun st =>
      Gate.mkOR (Wire.mk s!"plru_rf_evt_{st}") (Wire.mk s!"plru_hit_evt_{st}") plru_upd_en[st]!) ++
    List.flatten ((List.range sets).map (fun st =>
      List.flatten ((List.range ways).map fun w =>
        [Gate.mkAND (Wire.mk s!"plru_rf_evt_{st}") refill_victim[w]!
           (Wire.mk s!"plru_rf_w_{st}_{w}"),
         Gate.mkAND (Wire.mk s!"plru_hit_evt_{st}") way_hit[w]!
           (Wire.mk s!"plru_hit_w_{st}_{w}"),
         Gate.mkOR (Wire.mk s!"plru_rf_w_{st}_{w}") (Wire.mk s!"plru_hit_w_{st}_{w}")
           plru_upd_way[st]![w]!])))
  let plru_insts : List CircuitInstance :=
    if ways < 2 then []
    else (List.range sets).map (fun st =>
      CircuitInstance.mk s!"PLRU{ways}" s!"u_plru_s{st}"
        ([("clock", clock), ("reset", reset), ("zero", const_zero), ("one", const_one),
          ("upd_en", plru_upd_en[st]!)] ++
         (List.range ways).map (fun w => (s!"upd_way_oh_{w}", plru_upd_way[st]![w]!)) ++
         (List.range ways).map (fun w => (s!"victim_oh_{w}", plru_victim[st]![w]!))))

  -- RAM write enables: a refill writes exactly the victim way
  let ram_wr_gates := (List.range ways).map fun way =>
    Gate.mkAND (Wire.mk "refill_done") refill_victim[way]! ram_wr_en[way]!

  -- Line write = RAM write (victim way) AND the refill set
  let refill_write := (List.range ways).map fun way =>
    (List.range sets).map fun st => Wire.mk s!"refill_write_w{way}_s{st}"
  let refill_write_gates : List Gate := List.flatten ((List.range ways).map fun way =>
    (List.range sets).map fun st =>
      Gate.mkAND ram_wr_en[way]! refill_dec[st]! refill_write[way]![st]!)

  -- FENCE.I: clear all valid bits; a refill installs its line
  let not_fence_i := Wire.mk "not_fence_i"
  let valid_next_gates : List Gate := [Gate.mkNOT fence_i not_fence_i] ++
    List.flatten (List.flatten ((List.range ways).map fun way =>
      (List.range sets).map fun st =>
        let i := way * sets + st
        [Gate.mkAND valid_q[i]! not_fence_i (Wire.mk s!"valid_hold_{i}"),
         Gate.mkOR (Wire.mk s!"valid_hold_{i}") refill_write[way]![st]! valid_d[i]!]))

  -- Tag write logic: on refill, write the victim way's tag from the MAR
  let tag_write_gates : List Gate := (List.range ways).foldl (fun acc way =>
    acc ++ (List.range sets).foldl (fun acc2 st =>
      acc2 ++ (List.range tagBits).map (fun b =>
        Gate.mkMUX (Wire.mk s!"tag_q_w{way}_s{st}_{b}") refill_tag_bits[b]! refill_write[way]![st]!
          (Wire.mk s!"tag_d_w{way}_s{st}_{b}"))) []) []

  -- Selected line: the hitting way, or - on a miss - the set's victim.  The
  -- CPU keeps decoding combinationally during a refill stall, so the cache must
  -- present the indexed set's contents rather than nothing; at one way this
  -- select is always on and the line is the plain RAM read.
  let sel_way := (List.range ways).map fun w => Wire.mk s!"sel_way_oh_{w}"
  let sel_way_gates : List Gate := List.flatten ((List.range ways).map fun w =>
    [Gate.mkAND (Wire.mk "not_hit") req_victim[w]! (Wire.mk s!"sel_way_nv_{w}"),
     Gate.mkOR way_hit[w]! (Wire.mk s!"sel_way_nv_{w}") sel_way[w]!])
  let sel_line := (List.range lineBits).map fun b => Wire.mk s!"sel_line_{b}"
  let sel_line_gates : List Gate := List.flatten ((List.range lineBits).map fun b =>
    let t := (List.range ways).map fun w => Wire.mk s!"sel_line_and_w{w}_{b}"
    List.flatten ((List.range ways).map fun w =>
      [Gate.mkAND sel_way[w]! sel_line_w[w]![b]! t[w]!])
    ++ mkOrTree t sel_line[b]!)

  -- Word select: mux 1 of `words` words out of the selected line
  let word_mux_inst := CircuitInstance.mk s!"Mux{words}x32" "u_word_mux"
    ((List.range words).foldl (fun acc wordIdx =>
      acc ++ (List.range 32).map (fun b =>
        (s!"in{wordIdx}_{b}", sel_line[wordIdx * 32 + b]!))
    ) [] ++
    (List.range wordBits).map (fun i => (s!"sel_{i}", word_sel[i]!)) ++
    (List.range 32).map (fun b => (s!"out_{b}", resp_data[b]!)))

  -- Second word select: word_sel + 1 (wordBits-wide increment for dual fetch)
  let word_sel_1 := (List.range wordBits).map fun i => Wire.mk s!"word_sel_1_{i}"
  let ws1_gates : List Gate := List.flatten ((List.range wordBits).map fun i =>
    let carry_in := if i == 0 then const_one else Wire.mk s!"ws1_c{i - 1}"
    [Gate.mkXOR word_sel[i]! carry_in word_sel_1[i]!] ++
    (if i == wordBits - 1 then [] else
      [Gate.mkAND word_sel[i]! carry_in (Wire.mk s!"ws1_c{i}")]))

  -- last_word: every word-select bit set
  let lw_gates : List Gate :=
    if wordBits == 1 then
      [Gate.mkBUF word_sel[0]! last_word]
    else
      let folds := (List.range wordBits).foldl (fun (gs, prev) i =>
        if i == 0 then (gs, word_sel[0]!)
        else
          let out := if i == wordBits - 1 then last_word else Wire.mk s!"lw_c{i}"
          (gs ++ [Gate.mkAND prev word_sel[i]! out], out)) ([], const_one)
      folds.1

  let word_mux_1_inst := CircuitInstance.mk s!"Mux{words}x32" "u_word_mux_1"
    ((List.range words).foldl (fun acc wordIdx =>
      acc ++ (List.range 32).map (fun b =>
        (s!"in{wordIdx}_{b}", sel_line[wordIdx * 32 + b]!))
    ) [] ++
    (List.range wordBits).map (fun i => (s!"sel_{i}", word_sel_1[i]!)) ++
    (List.range 32).map fun b => (s!"out_{b}", resp_data_1[b]!))

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
    if i < offsetBits then
      -- Clear the offset bits for line alignment
      Gate.mkBUF const_zero (miss_addr[i]!)
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
    Gate.mkOR (Wire.mk "fsm_d0_tmp") stay_done (Wire.mk "fsm_d0_raw"),
    -- FENCE.I restarts the FSM: drop any in-flight refill, so a response that
    -- arrives after the invalidate can never (re)install a stale line.
    -- (fsm_d0_raw is 0 on the fence cycle anyway unless a miss is coincident.)
    Gate.mkAND (Wire.mk "fsm_d0_raw") (Wire.mk "not_fence_i") fsm_d[0]!,
    -- fsm_d[1] = is_refill_req (REFILL_REQ→REFILL_WAIT)
    --            OR (is_refill_wait AND NOT refill_valid) (stay in REFILL_WAIT)
    --            OR refill_done (REFILL_WAIT→REFILL_DONE)
    --            OR stay_done (REFILL_DONE stays until req_valid)
    Gate.mkNOT refill_valid (Wire.mk "not_refill_valid"),
    Gate.mkAND is_refill_wait (Wire.mk "not_refill_valid") (Wire.mk "stay_wait"),
    Gate.mkOR is_refill_req (Wire.mk "stay_wait") (Wire.mk "fsm_d1_tmp"),
    Gate.mkOR (Wire.mk "fsm_d1_tmp") refill_done (Wire.mk "fsm_d1_tmp2"),
    Gate.mkOR (Wire.mk "fsm_d1_tmp2") stay_done (Wire.mk "fsm_d1_raw"),
    Gate.mkAND (Wire.mk "fsm_d1_raw") (Wire.mk "not_fence_i") fsm_d[1]!
  ]

  -- MAR capture: save req_addr on miss_detect, hold otherwise
  let mar_capture_gates := (List.range 32).map fun i =>
    Gate.mkMUX mar_q[i]! req_addr[i]! miss_detect mar_d[i]!

  -- Collect all gates
  let allGates :=
    const_gates ++
    fsm_gates ++ mar_gates ++ valid_gates ++
    way_sel_gates ++ hit_gate ++
    victim_gates ++ req_victim_gates ++ plru_gates ++ ram_wr_gates ++ refill_write_gates ++
    sel_way_gates ++ sel_line_gates ++ ws1_gates ++ lw_gates ++
    fsm_logic_gates ++ miss_gates ++ resp_gates ++
    [miss_valid_gate] ++ not_idle_miss_gates ++ miss_addr_gates ++ stall_gates ++
    fsm_next_gates ++ mar_capture_gates ++
    valid_next_gates ++ tag_write_gates

  -- Collect all instances
  let allInstances :=
    tag_instances ++
    [req_dec_inst, refill_dec_inst] ++
    tag_mux_insts ++ tag_cmp_insts ++ plru_insts ++
    [word_mux_inst, word_mux_1_inst]

  { name := s!"L1ICache{g.nameSuffix}"
    inputs := [clock, reset, req_valid] ++ req_addr ++ [refill_valid] ++ refill_data ++ [fence_i]
    outputs := [resp_valid] ++ resp_data ++ resp_data_1 ++ [miss_valid] ++ miss_addr ++ [stall, last_word]
    gates := allGates
    instances := allInstances
    rams := data_rams
    signalGroups := [
      { name := "req_addr", width := 32, wires := req_addr },
      { name := "refill_data", width := lineBits, wires := refill_data },
      { name := "resp_data", width := 32, wires := resp_data },
      { name := "resp_data_1", width := 32, wires := resp_data_1 },
      { name := "miss_addr", width := 32, wires := miss_addr }
    ]
  }

end Shoumei.RISCV.Memory.Cache

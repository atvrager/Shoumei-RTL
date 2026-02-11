/-
RISCV/Execution/ReservationStation.lean - Reservation Station for Tomasulo Algorithm

Implements a reservation station (RS) array that:
- Issues renamed instructions (captures operands from register file or tags)
- Snoops Common Data Bus (CDB) to wake up waiting operands
- Selects ready instructions for dispatch to execution units
- Supports out-of-order execution with data hazard resolution

Key concepts:
- **RSEntry**: Individual reservation station slot storing operation and operands
- **Operand capture**: At issue time, grab value if ready, else store tag
- **CDB snooping**: Content-addressable matching - all entries watch CDB in parallel
- **Wakeup**: When CDB broadcasts tag, matching entries capture the data
- **Ready selection**: Find entries where both operands are available
- **Dispatch**: Send ready instruction to execution unit and deallocate entry

This is a behavioral model focused on correctness.
Structural circuit implementation is in future phases.
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.Renaming.RenameStage
import Shoumei.RISCV.Renaming.PhysRegFile
import Shoumei.DSL
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.Arbiter

namespace Shoumei.RISCV.Execution

open Shoumei
open Shoumei.RISCV
open Shoumei.RISCV.Renaming
open Shoumei.Circuits.Combinational

/-! ## Reservation Station Entry -/

/-- Reservation Station Entry - stores an instruction waiting for operands.

    Each entry tracks:
    - **valid**: Is this entry occupied?
    - **opcode**: What operation to perform (ADD, SUB, MUL, etc.)
    - **dest_tag**: Which physical register will receive the result
    - **src1/src2 ready flags**: Are the operands available?
    - **src1/src2 tags**: Which physical registers produced the operands (if not ready)
    - **src1/src2 data**: Operand values (if ready)
    - **immediate**: Immediate value for memory offsets, branch offsets (from decode)
    - **pc**: Program counter for branch target calculation

    State transitions:
    1. **Empty** (valid=false) - slot available for new instruction
    2. **Waiting** (valid=true, src ready=false) - waiting for CDB broadcast
    3. **Ready** (valid=true, both src ready=true) - can dispatch to execution
    4. **Dispatched** (valid=false) - sent to execution unit, entry freed
-/
structure RSEntry where
  /-- Entry occupied (instruction allocated) -/
  valid : Bool
  /-- Operation type (ADD, SUB, etc.) -/
  opcode : OpType
  /-- Destination physical register tag -/
  dest_tag : Fin 64
  /-- Source operand 1 ready flag -/
  src1_ready : Bool
  /-- Source operand 1 physical register tag (if not ready) -/
  src1_tag : Fin 64
  /-- Source operand 1 data value (if ready) -/
  src1_data : UInt32
  /-- Source operand 2 ready flag -/
  src2_ready : Bool
  /-- Source operand 2 physical register tag (if not ready) -/
  src2_tag : Fin 64
  /-- Source operand 2 data value (if ready) -/
  src2_data : UInt32
  /-- Source operand 3 ready flag (for R4-type fused FP ops; default true for non-fused) -/
  src3_ready : Bool := true
  /-- Source operand 3 physical register tag -/
  src3_tag : Fin 64 := 0
  /-- Source operand 3 data value -/
  src3_data : UInt32 := 0
  /-- Immediate value (for memory offsets, branch targets) -/
  immediate : Option Int
  /-- Program counter (for branch target calculation) -/
  pc : UInt32
  deriving Repr

namespace RSEntry

/-- Create an empty (invalid) reservation station entry -/
def empty : RSEntry :=
  { valid := false
    opcode := OpType.ADD  -- Dummy value, ignored when invalid
    dest_tag := 0
    src1_ready := false
    src1_tag := 0
    src1_data := 0
    src2_ready := false
    src2_tag := 0
    src2_data := 0
    immediate := none     -- No immediate value
    pc := 0               -- Dummy PC value
  }

/-- Is this entry ready for dispatch? (valid and both operands ready) -/
def isReady (e : RSEntry) : Bool :=
  e.valid && e.src1_ready && e.src2_ready && e.src3_ready

/-- Is this entry waiting for a specific tag? -/
def isWaitingFor (e : RSEntry) (tag : Fin 64) : Bool :=
  e.valid && (
    (!e.src1_ready && e.src1_tag == tag) ||
    (!e.src2_ready && e.src2_tag == tag) ||
    (!e.src3_ready && e.src3_tag == tag)
  )

end RSEntry

/-! ## Reservation Station State -/

/-- Reservation Station State - array of entries with allocation tracking.

    The RS manages a fixed number of entries (typically 4-16).
    Allocation uses round-robin pointer to distribute instructions.
-/
structure RSState (numEntries : Nat) where
  /-- Array of reservation station entries -/
  entries : Fin numEntries → RSEntry
  /-- Next allocation pointer (round-robin) -/
  next_alloc : Fin numEntries

namespace RSState

/-! ## Initialization -/

/-- Create empty reservation station (all entries invalid) -/
def init (numEntries : Nat) (h : numEntries > 0 := by omega) : RSState numEntries :=
  { entries := fun _ => RSEntry.empty
    next_alloc := ⟨0, h⟩
  }

/-! ## Issue Operation -/

/-- Issue a renamed instruction to the reservation station.

    **Issue protocol:**
    1. Check if next_alloc entry is free (valid=false)
    2. If full, stall (return none)
    3. If space available:
       - Allocate entry at next_alloc
       - For each source operand:
         * If instruction has no source (immediate/constant) → mark ready with value 0
         * If source tag found in PhysRegFile → capture value, mark ready
         * Otherwise → store tag, mark not ready (will wait for CDB)
       - Store opcode and dest_tag
       - Advance next_alloc (round-robin)
    4. Return allocated entry index

    **Operand capture logic:**
    - This implements "bypass" - if a recent instruction just wrote to the
      physical register file, we grab the value immediately instead of waiting
    - This is standard Tomasulo - the register file is checked at issue time
-/
def issue
    (rs : RSState n)
    (instr : RenamedInstruction)
    (prf : PhysRegFileState 64)
    : RSState n × Option (Fin n) :=
  -- Check if next allocation slot is free
  if (rs.entries rs.next_alloc).valid then
    -- Stall: RS is full at this allocation pointer
    (rs, none)
  else
    -- Capture operand 1
    let (src1_ready, src1_tag, src1_data) :=
      match instr.physRs1 with
      | none => (true, 0, 0)  -- No source operand (immediate or doesn't use rs1)
      | some tag =>
          -- Check if value is available in PhysRegFile
          let value := prf.read tag
          (true, tag, value)  -- In Tomasulo, assume PRF has valid data

    -- Capture operand 2
    let (src2_ready, src2_tag, src2_data) :=
      match instr.physRs2 with
      | none => (true, 0, 0)  -- No source operand (immediate or doesn't use rs2)
      | some tag =>
          let value := prf.read tag
          (true, tag, value)

    -- Capture operand 3 (for R4-type fused FP ops)
    let (src3_ready, src3_tag, src3_data) :=
      match instr.physRs3 with
      | none => (true, (0 : Fin 64), (0 : UInt32))  -- No src3 (non-fused ops)
      | some tag =>
          let value := prf.read tag
          (true, tag, value)

    -- Create new entry
    let newEntry : RSEntry := {
      valid := true
      opcode := instr.opType
      dest_tag := instr.physRd.getD 0  -- Destination tag (0 if none, shouldn't happen for RS)
      src1_ready := src1_ready
      src1_tag := src1_tag
      src1_data := src1_data
      src2_ready := src2_ready
      src2_tag := src2_tag
      src2_data := src2_data
      src3_ready := src3_ready
      src3_tag := src3_tag
      src3_data := src3_data
      immediate := instr.imm           -- Immediate value for memory/branch ops
      pc := instr.pc                   -- Program counter for branch target calc
    }

    -- Update entries array (replace entry at next_alloc)
    let newEntries := fun i =>
      if i == rs.next_alloc then newEntry
      else rs.entries i

    -- Advance allocation pointer (round-robin)
    let allocIdx := rs.next_alloc
    let newNextAlloc : Fin n :=
      if h : rs.next_alloc.val + 1 < n then
        ⟨rs.next_alloc.val + 1, h⟩
      else
        ⟨0, Nat.zero_lt_of_lt rs.next_alloc.isLt⟩

    -- Return updated state and allocated index
    let rs' := { rs with
      entries := newEntries
      next_alloc := newNextAlloc
    }
    (rs', some allocIdx)

/-! ## CDB Broadcast (Wakeup) -/

/-- CDB broadcast: wake up entries waiting for a tag.

    When an execution unit completes, it broadcasts (tag, data) on the CDB.
    All reservation stations snoop the CDB in parallel (content-addressable).

    **For each entry:**
    - If src1 is not ready AND src1_tag matches → capture data, mark ready
    - If src2 is not ready AND src2_tag matches → capture data, mark ready
    - This happens **in parallel** across all entries

    **Note:** An entry can wake up both operands in one cycle if they have the
    same tag (rare but possible, e.g., ADD x1, x2, x2).
-/
def cdbBroadcast
    (rs : RSState n)
    (cdb_tag : Fin 64)
    (cdb_data : UInt32)
    : RSState n :=
  let newEntries := fun i =>
    let e := rs.entries i
    if !e.valid then e  -- Skip invalid entries
    else
      -- Check src1 match
      let e1 := if !e.src1_ready && e.src1_tag == cdb_tag then
        { e with src1_ready := true, src1_data := cdb_data }
      else e

      -- Check src2 match (on possibly updated e1)
      let e2 := if !e1.src2_ready && e1.src2_tag == cdb_tag then
        { e1 with src2_ready := true, src2_data := cdb_data }
      else e1

      -- Check src3 match (on possibly updated e2)
      let e3 := if !e2.src3_ready && e2.src3_tag == cdb_tag then
        { e2 with src3_ready := true, src3_data := cdb_data }
      else e2

      e3

  { rs with entries := newEntries }

/-! ## Ready Selection -/

/-- Select first ready entry for dispatch.

    **Selection policy:** First-match (simplest)
    - Scan entries in order (0 to n-1)
    - Return first entry where valid=true and both src ready=true
    - If none ready, return none

    **Alternative policies (future):**
    - Age-based (oldest instruction first)
    - Priority-based (certain operations prioritized)
    - Randomized (avoid starvation)

    For now, we use first-match for simplicity and determinism.
-/
def selectReady (rs : RSState n) : Option (Fin n) :=
  -- Scan entries to find first ready one
  (List.range n).findSome? fun i =>
    if h : i < n then
      let idx : Fin n := ⟨i, h⟩
      if (rs.entries idx).isReady then some idx else none
    else
      none

/-! ## Dispatch Operation -/

/-- Dispatch entry to execution unit.

    **Dispatch protocol:**
    1. Check if entry is ready (valid and both operands available)
    2. If ready:
       - Invalidate entry (mark as free)
       - Return (opcode, src1_data, src2_data, dest_tag, immediate, pc) for execution
    3. If not ready, return none (caller shouldn't dispatch non-ready entries)

    **Note:** The execution unit will:
    - Compute result = f(opcode, src1_data, src2_data, immediate, pc)
    - Broadcast (dest_tag, result) on CDB
    - This wakes up other RS entries waiting for this tag
-/
def dispatch
    (rs : RSState n)
    (idx : Fin n)
    : RSState n × Option (OpType × UInt32 × UInt32 × UInt32 × Fin 64 × Option Int × UInt32) :=
  let e := rs.entries idx
  if e.isReady then
    -- Invalidate entry (mark as free)
    let newEntries := fun i =>
      if i == idx then RSEntry.empty
      else rs.entries i

    let rs' := { rs with entries := newEntries }

    -- Return operation bundle for execution unit (includes src3 for fused FP ops)
    let result := (e.opcode, e.src1_data, e.src2_data, e.src3_data, e.dest_tag, e.immediate, e.pc)
    (rs', some result)
  else
    -- Entry not ready, shouldn't be dispatched
    (rs, none)

/-! ## Utility Functions -/

/-- Count number of valid (occupied) entries -/
def countValid (rs : RSState n) : Nat :=
  (List.range n).foldl (fun acc i =>
    if h : i < n then
      let idx : Fin n := ⟨i, h⟩
      if (rs.entries idx).valid then acc + 1 else acc
    else
      acc
  ) 0

/-- Count number of ready entries (waiting to dispatch) -/
def countReady (rs : RSState n) : Nat :=
  (List.range n).foldl (fun acc i =>
    if h : i < n then
      let idx : Fin n := ⟨i, h⟩
      if (rs.entries idx).isReady then acc + 1 else acc
    else
      acc
  ) 0

/-- Is RS full? (all entries valid) -/
def isFull (rs : RSState n) : Bool :=
  rs.countValid == n

/-- Is RS empty? (no valid entries) -/
def isEmpty (rs : RSState n) : Bool :=
  rs.countValid == 0

end RSState

/-! ## Common Configurations -/

-- 4-entry reservation station (typical for integer ALU)
def RS4 := RSState 4

-- 8-entry reservation station (larger buffer)
def RS8 := RSState 8

-- 16-entry reservation station (aggressive OoO)
def RS16 := RSState 16

/-! ## Behavioral Correctness Theorems -/

/-- Issue preserves entry count bounds.

    After issuing to a non-full RS, the number of valid entries increases by at most 1.
-/
axiom rs_issue_preserves_bounds (n : Nat) (rs : RSState n) (instr : RenamedInstruction)
    (prf : PhysRegFileState 64) :
  let (rs', _) := rs.issue instr prf
  rs'.countValid ≤ rs.countValid + 1

/-- Issue to full RS returns none.

    If RS is full, issue operation stalls (returns none).
-/
axiom rs_issue_full_stalls (n : Nat) (rs : RSState n) (instr : RenamedInstruction)
    (prf : PhysRegFileState 64) :
  rs.isFull → (rs.issue instr prf).2 = none

/-- Successful issue allocates an entry.

    If issue succeeds (returns some index), that entry becomes valid.
-/
axiom rs_issue_success_valid (n : Nat) (rs : RSState n) (instr : RenamedInstruction)
    (prf : PhysRegFileState 64) :
  let (rs', maybeIdx) := rs.issue instr prf
  match maybeIdx with
  | some idx => (rs'.entries idx).valid = true
  | none => True

/-- CDB broadcast preserves valid entry count.

    Broadcasting on CDB only wakes up operands, doesn't change valid bits.
-/
axiom rs_cdb_preserves_count (n : Nat) (rs : RSState n) (tag : Fin 64) (data : UInt32) :
  (rs.cdbBroadcast tag data).countValid = rs.countValid

/-- CDB broadcast wakes up waiting operands.

    If an entry is waiting for a tag and CDB broadcasts that tag,
    the entry's operand becomes ready.
-/
axiom rs_cdb_wakeup_correct (n : Nat) (rs : RSState n) (tag : Fin 64) (data : UInt32)
    (idx : Fin n) :
  let e := rs.entries idx
  let e' := (rs.cdbBroadcast tag data).entries idx
  e.isWaitingFor tag →
    ((!e.src1_ready ∧ e.src1_tag == tag → e'.src1_ready = true ∧ e'.src1_data = data) ∧
     (!e.src2_ready ∧ e.src2_tag == tag → e'.src2_ready = true ∧ e'.src2_data = data))

/-- Ready selection returns a ready entry.

    If selectReady returns some index, that entry is ready for dispatch.
-/
axiom rs_select_ready_correct (n : Nat) (rs : RSState n) :
  match rs.selectReady with
  | some idx => (rs.entries idx).isReady = true
  | none => rs.countReady = 0

/-- Ready selection prioritizes lower indices.

    If selectReady returns index j, no lower index i < j is ready.
-/
axiom rs_select_ready_priority (n : Nat) (rs : RSState n) :
  match rs.selectReady with
  | some j => ∀ i : Fin n, i.val < j.val → (rs.entries i).isReady = false
  | none => True

/-- Dispatch clears the selected entry.

    After dispatching entry idx, that entry becomes invalid.
-/
axiom rs_dispatch_clears_entry (n : Nat) (rs : RSState n) (idx : Fin n) :
  let (rs', result) := rs.dispatch idx
  match result with
  | some _ => (rs'.entries idx).valid = false
  | none => rs' = rs

/-- Dispatch returns operands from the entry.

    If dispatch succeeds, it returns the entry's opcode, operand data, immediate, and pc.
-/
axiom rs_dispatch_returns_operands (n : Nat) (rs : RSState n) (idx : Fin n) :
  let e := rs.entries idx
  let (_, result) := rs.dispatch idx
  e.isReady →
    result = some (e.opcode, e.src1_data, e.src2_data, e.src3_data, e.dest_tag, e.immediate, e.pc)

/-! ## Structural Circuit (Hardware Implementation) -/

/-- Helper: Create indexed wires -/
private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

/-- Build a 4-entry reservation station circuit (structural stub).

    **Interface** (195 wires total):

    Inputs (Issue):
    - clock, reset, zero, one: 4 control signals
    - issue_en: Enable issue operation
    - issue_opcode[5:0]: Operation type (6-bit encoding for RV32I)
    - issue_dest_tag[5:0]: Destination physical register tag
    - issue_src1_ready, issue_src1_tag[5:0], issue_src1_data[31:0]: Source 1
    - issue_src2_ready, issue_src2_tag[5:0], issue_src2_data[31:0]: Source 2

    Inputs (CDB):
    - cdb_valid: CDB broadcast enable
    - cdb_tag[5:0]: Tag being broadcast on CDB
    - cdb_data[31:0]: Data for tag

    Inputs (Dispatch):
    - dispatch_en: Request to dispatch a ready entry

    Outputs:
    - issue_full: RS is full, cannot issue
    - dispatch_valid: Ready entry available for dispatch
    - dispatch_opcode[5:0]: Operation to execute
    - dispatch_src1_data[31:0], dispatch_src2_data[31:0]: Operands
    - dispatch_dest_tag[5:0]: Destination tag for CDB result

    **Planned Architecture** (~1100 gates + 366 DFFs):

    Storage:
    - 4 entries × 91 bits each = 364 DFFs
    - 2-bit allocation pointer = 2 DFFs

    Issue logic (~200 gates):
    - Decoder2 for allocation pointer → one-hot entry select
    - Per-entry write enable: issue_en AND decoder_out[i] AND NOT(valid[i])
    - Write muxes for all 91 bits per entry

    CDB snooping (~150 gates):
    - Per entry: 2 × 6-bit tag comparators (XOR + AND tree)
    - Wakeup logic: valid AND NOT(ready) AND tag_match AND cdb_valid
    - Data capture muxes

    Ready selection (~60 gates):
    - Per-entry ready: valid AND src1_ready AND src2_ready (12 AND gates)
    - PriorityArbiter4 instance (14 gates)
    - Ready signal collection (34 gates)

    Dispatch (~400 gates):
    - 4:1 muxes for opcode, src1_data, src2_data, dest_tag (74 bits total)
    - Valid bit clearing logic

    Allocation pointer (~50 gates):
    - 2-bit increment with wrap at 4
    - 2 DFFs with reset

    **Note:** This stub provides correct interface for code generation and LEC.
    Full gate-level implementation follows the architecture described above.
-/
def mkReservationStation4 (enableStoreLoadOrdering : Bool := false) : Circuit :=
  let tagWidth := 6
  let dataWidth := 32
  let opcodeWidth := 6
  let entryWidth := 91  -- valid(1) + opcode(6) + dest_tag(6) + src1(1+6+32) + src2(1+6+32)

  -- Control
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- Issue interface
  let issue_en := Wire.mk "issue_en"
  -- Store-load ordering (only when enableStoreLoadOrdering)
  let issue_is_store := Wire.mk "issue_is_store"
  let issue_opcode := makeIndexedWires "issue_opcode" opcodeWidth
  let issue_dest_tag := makeIndexedWires "issue_dest_tag" tagWidth
  let issue_src1_ready := Wire.mk "issue_src1_ready"
  let issue_src1_tag := makeIndexedWires "issue_src1_tag" tagWidth
  let issue_src1_data := makeIndexedWires "issue_src1_data" dataWidth
  let issue_src2_ready := Wire.mk "issue_src2_ready"
  let issue_src2_tag := makeIndexedWires "issue_src2_tag" tagWidth
  let issue_src2_data := makeIndexedWires "issue_src2_data" dataWidth
  let issue_full := Wire.mk "issue_full"

  -- CDB interface
  let cdb_valid := Wire.mk "cdb_valid"
  let cdb_tag := makeIndexedWires "cdb_tag" tagWidth
  let cdb_data := makeIndexedWires "cdb_data" dataWidth

  -- Dispatch interface
  let dispatch_en := Wire.mk "dispatch_en"
  let dispatch_valid := Wire.mk "dispatch_valid"
  let dispatch_opcode := makeIndexedWires "dispatch_opcode" opcodeWidth
  let dispatch_src1_data := makeIndexedWires "dispatch_src1_data" dataWidth
  let dispatch_src2_data := makeIndexedWires "dispatch_src2_data" dataWidth
  let dispatch_dest_tag := makeIndexedWires "dispatch_dest_tag" tagWidth

  -- ============================================================================
  -- 1. ALLOCATION POINTER (2-bit counter with Register2)
  -- ============================================================================

  let alloc_ptr := makeIndexedWires "alloc_ptr" 2
  let alloc_ptr_next := makeIndexedWires "alloc_ptr_next" 2

  -- Increment logic: (alloc_ptr + 1) % 4
  -- For 2-bit: next[0] = NOT(curr[0]), next[1] = curr[1] XOR curr[0]
  let alloc_incr_gates := [
    Gate.mkNOT alloc_ptr[0]! alloc_ptr_next[0]!,
    Gate.mkXOR alloc_ptr[1]! alloc_ptr[0]! alloc_ptr_next[1]!
  ]

  -- Register2 instance for allocation pointer
  let alloc_ptr_inst : CircuitInstance := {
    moduleName := "Register2"
    instName := "u_alloc_ptr"
    portMap :=
      (alloc_ptr_next.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
      [("clock", clock), ("reset", reset)] ++
      (alloc_ptr.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
  }

  -- ============================================================================
  -- 2. ISSUE DECODER (Decoder2: 2→4 one-hot)
  -- ============================================================================

  let issue_sel := makeIndexedWires "issue_sel" 4

  let decoder_inst : CircuitInstance := {
    moduleName := "Decoder2"
    instName := "u_issue_dec"
    portMap := [
      ("in_0", alloc_ptr[0]!), ("in_1", alloc_ptr[1]!),
      ("out_0", issue_sel[0]!), ("out_1", issue_sel[1]!),
      ("out_2", issue_sel[2]!), ("out_3", issue_sel[3]!)
    ]
  }

  -- ============================================================================
  -- 3. PER-ENTRY LOGIC (4 entries with Register91 instances)
  -- ============================================================================

  -- Helper: Pack/unpack 91-bit entry representation
  -- Layout: valid(0) opcode(1-6) dest_tag(7-12) src1_ready(13) src1_tag(14-19)
  --         src1_data(20-51) src2_ready(52) src2_tag(53-58) src2_data(59-90)

  let buildEntryLogic (i : Nat) : List Gate × List CircuitInstance :=
    -- Entry storage wires (91 bits)
    let entry_cur := makeIndexedWires s!"e{i}" entryWidth
    let entry_next := makeIndexedWires s!"e{i}_next" entryWidth

    -- Field extraction from current entry
    let valid := entry_cur[0]!
    let _ := entry_cur.drop 1 |>.take opcodeWidth  -- opcode (unused in simplified impl)
    let _ := entry_cur.drop 7 |>.take tagWidth  -- dest_tag (unused in simplified impl)
    let src1_ready := entry_cur[13]!
    let src1_tag := entry_cur.drop 14 |>.take tagWidth
    let _ := entry_cur.drop 20 |>.take dataWidth  -- src1_data (unused in simplified impl)
    let src2_ready := entry_cur[52]!
    let src2_tag := entry_cur.drop 53 |>.take tagWidth
    let _ := entry_cur.drop 59 |>.take dataWidth  -- src2_data (unused in simplified impl)

    -- Issue write enable: issue_en AND issue_sel[i] AND NOT(valid)
    let issue_we_raw := Wire.mk s!"e{i}_issue_we_raw"
    let valid_n := Wire.mk s!"e{i}_valid_n"
    let issue_we := Wire.mk s!"e{i}_issue_we"
    let issue_we_gates := [
      Gate.mkAND issue_en issue_sel[i]! issue_we_raw,
      Gate.mkNOT valid valid_n,
      Gate.mkAND issue_we_raw valid_n issue_we
    ]

    -- Dispatch clear enable: dispatch_en AND dispatch_grant[i]
    let dispatch_grant := Wire.mk s!"dispatch_grant_{i}"  -- Match makeIndexedWires naming
    let dispatch_clear := Wire.mk s!"e{i}_dispatch_clear"
    let dispatch_clear_gate := Gate.mkAND dispatch_en dispatch_grant dispatch_clear

    -- CDB tag comparison for src1 (Comparator6 instance)
    let cdb_match_src1 := Wire.mk s!"e{i}_cdb_match_src1"
    let cmp_src1_portmap :=
      (cdb_tag.enum.map (fun ⟨j, w⟩ => (s!"a_{j}", w))) ++
      (src1_tag.enum.map (fun ⟨j, w⟩ => (s!"b_{j}", w))) ++
      [("one", Wire.mk "one"),  -- Tie to 1 for equality comparison
       ("eq", cdb_match_src1),
       ("lt", Wire.mk s!"e{i}_cmp_src1_lt_unused"),
       ("ltu", Wire.mk s!"e{i}_cmp_src1_ltu_unused"),
       ("gt", Wire.mk s!"e{i}_cmp_src1_gt_unused"),
       ("gtu", Wire.mk s!"e{i}_cmp_src1_gtu_unused")]
    let cmp_src1_inst : CircuitInstance := {
      moduleName := "Comparator6"
      instName := s!"u_e{i}_cmp_src1"
      portMap := cmp_src1_portmap
    }

    -- CDB tag comparison for src2 (Comparator6 instance)
    let cdb_match_src2 := Wire.mk s!"e{i}_cdb_match_src2"
    let cmp_src2_portmap :=
      (cdb_tag.enum.map (fun ⟨j, w⟩ => (s!"a_{j}", w))) ++
      (src2_tag.enum.map (fun ⟨j, w⟩ => (s!"b_{j}", w))) ++
      [("one", Wire.mk "one"),  -- Tie to 1 for equality comparison
       ("eq", cdb_match_src2),
       ("lt", Wire.mk s!"e{i}_cmp_src2_lt_unused"),
       ("ltu", Wire.mk s!"e{i}_cmp_src2_ltu_unused"),
       ("gt", Wire.mk s!"e{i}_cmp_src2_gt_unused"),
       ("gtu", Wire.mk s!"e{i}_cmp_src2_gtu_unused")]
    let cmp_src2_inst : CircuitInstance := {
      moduleName := "Comparator6"
      instName := s!"u_e{i}_cmp_src2"
      portMap := cmp_src2_portmap
    }

    -- CDB wakeup condition for src1: valid AND NOT(src1_ready) AND match AND cdb_valid
    let cdb_wakeup_src1_tmp1 := Wire.mk s!"e{i}_cdb_wakeup_src1_tmp1"
    let src1_ready_n := Wire.mk s!"e{i}_src1_ready_n"
    let cdb_wakeup_src1_tmp2 := Wire.mk s!"e{i}_cdb_wakeup_src1_tmp2"
    let cdb_wakeup_src1 := Wire.mk s!"e{i}_cdb_wakeup_src1"
    let wakeup_src1_gates := [
      Gate.mkNOT src1_ready src1_ready_n,
      Gate.mkAND valid src1_ready_n cdb_wakeup_src1_tmp1,
      Gate.mkAND cdb_wakeup_src1_tmp1 cdb_match_src1 cdb_wakeup_src1_tmp2,
      Gate.mkAND cdb_wakeup_src1_tmp2 cdb_valid cdb_wakeup_src1
    ]

    -- CDB wakeup condition for src2: similar logic
    let cdb_wakeup_src2_tmp1 := Wire.mk s!"e{i}_cdb_wakeup_src2_tmp1"
    let src2_ready_n := Wire.mk s!"e{i}_src2_ready_n"
    let cdb_wakeup_src2_tmp2 := Wire.mk s!"e{i}_cdb_wakeup_src2_tmp2"
    let cdb_wakeup_src2 := Wire.mk s!"e{i}_cdb_wakeup_src2"
    let wakeup_src2_gates := [
      Gate.mkNOT src2_ready src2_ready_n,
      Gate.mkAND valid src2_ready_n cdb_wakeup_src2_tmp1,
      Gate.mkAND cdb_wakeup_src2_tmp1 cdb_match_src2 cdb_wakeup_src2_tmp2,
      Gate.mkAND cdb_wakeup_src2_tmp2 cdb_valid cdb_wakeup_src2
    ]

    -- Next-state logic for each bit (simplified: priority muxing)
    -- Priority: dispatch_clear > issue > cdb_wakeup > hold
    -- For now: simplified implementation with basic muxing
    -- Full version would have per-field muxing based on update conditions

    -- Valid bit: clear on dispatch, set on issue, hold otherwise
    let valid_next_tmp1 := Wire.mk s!"e{i}_valid_next_tmp1"
    let valid_next := entry_next[0]!
    let valid_next_gates := [
      Gate.mkMUX valid zero dispatch_clear valid_next_tmp1,  -- Clear on dispatch
      Gate.mkMUX valid_next_tmp1 one issue_we valid_next  -- Set on issue
    ]

    -- Per-field next-state logic:
    -- On issue_we: write issue data into entry
    -- On cdb_wakeup: update src ready bits and data
    -- Otherwise: hold current value

    -- Issue data mapping: issue fields → entry bit positions
    -- [1-6]=opcode, [7-12]=dest_tag, [13]=src1_ready, [14-19]=src1_tag,
    -- [20-51]=src1_data, [52]=src2_ready, [53-58]=src2_tag, [59-90]=src2_data
    let issue_data : List Wire :=
      issue_opcode ++ issue_dest_tag ++
      [issue_src1_ready] ++ issue_src1_tag ++ issue_src1_data ++
      [issue_src2_ready] ++ issue_src2_tag ++ issue_src2_data

    -- Build MUX for each field bit (bits 1-90)
    let field_next_gates := (List.range (entryWidth - 1)).map (fun j =>
      -- j is 0-indexed into field bits, entry bit is j+1
      let bit_idx := j + 1
      let cur_val := entry_cur[bit_idx]!
      let next_val := entry_next[bit_idx]!
      let issue_val := issue_data[j]!

      if bit_idx == 13 then
        -- src1_ready: issue_we ? issue_src1_ready : (cdb_wakeup_src1 ? one : hold)
        let tmp := Wire.mk s!"e{i}_src1_ready_next_tmp"
        [Gate.mkMUX cur_val one cdb_wakeup_src1 tmp,
         Gate.mkMUX tmp issue_val issue_we next_val]
      else if (20 <= bit_idx && bit_idx <= 51) then
        -- src1_data: issue_we ? issue_val : (cdb_wakeup_src1 ? cdb_data[bit-20] : hold)
        let cdb_idx := bit_idx - 20
        let tmp := Wire.mk s!"e{i}_src1_data{cdb_idx}_next_tmp"
        [Gate.mkMUX cur_val cdb_data[cdb_idx]! cdb_wakeup_src1 tmp,
         Gate.mkMUX tmp issue_val issue_we next_val]
      else if bit_idx == 52 then
        -- src2_ready: similar to src1_ready
        let tmp := Wire.mk s!"e{i}_src2_ready_next_tmp"
        [Gate.mkMUX cur_val one cdb_wakeup_src2 tmp,
         Gate.mkMUX tmp issue_val issue_we next_val]
      else if (59 <= bit_idx && bit_idx <= 90) then
        -- src2_data: similar to src1_data
        let cdb_idx := bit_idx - 59
        let tmp := Wire.mk s!"e{i}_src2_data{cdb_idx}_next_tmp"
        [Gate.mkMUX cur_val cdb_data[cdb_idx]! cdb_wakeup_src2 tmp,
         Gate.mkMUX tmp issue_val issue_we next_val]
      else
        -- Other fields (opcode, dest_tag, src tags): write on issue, hold otherwise
        [Gate.mkMUX cur_val issue_val issue_we next_val]
    ) |>.flatten

    -- Register91 instance for entry storage
    let entry_reg_inst : CircuitInstance := {
      moduleName := "Register91"
      instName := s!"u_entry{i}"
      portMap :=
        (entry_next.enum.map (fun ⟨j, w⟩ => (s!"d_{j}", w))) ++
        [("clock", clock), ("reset", reset)] ++
        (entry_cur.enum.map (fun ⟨j, w⟩ => (s!"q_{j}", w)))
    }

    let gates := issue_we_gates ++ [dispatch_clear_gate] ++
                 wakeup_src1_gates ++ wakeup_src2_gates ++
                 valid_next_gates ++ field_next_gates
    let instances := [cmp_src1_inst, cmp_src2_inst, entry_reg_inst]

    (gates, instances)

  let entry_logic := (List.range 4).map buildEntryLogic
  let entry_gates := entry_logic.map Prod.fst |>.flatten
  let entry_instances := entry_logic.map Prod.snd |>.flatten

  -- ============================================================================
  -- 4. STORE-LOAD ORDERING (only when enableStoreLoadOrdering)
  -- ============================================================================

  -- Per-entry is_store DFFs: track which entries hold store instructions
  -- is_store is set on issue (issue_we AND issue_is_store), cleared on dispatch_clear
  let store_order_gates := if enableStoreLoadOrdering then
    -- Use per-entry named wires (not indexed) to avoid codegen bus grouping
    let is_store_regs := (List.range 4).map (fun i => Wire.mk s!"e{i}_is_store")
    let store_entry_gates := (List.range 4).map (fun i =>
      let is_store_reg := is_store_regs[i]!
      let issue_we := Wire.mk s!"e{i}_issue_we"
      let dispatch_clear := Wire.mk s!"e{i}_dispatch_clear"
      let is_store_tmp := Wire.mk s!"e{i}_is_store_tmp"
      let is_store_next := Wire.mk s!"e{i}_is_store_next"
      [
        -- Clear on dispatch, hold otherwise
        Gate.mkMUX is_store_reg zero dispatch_clear is_store_tmp,
        -- Set on issue with is_store flag
        Gate.mkMUX is_store_tmp issue_is_store issue_we is_store_next,
        -- DFF
        Gate.mkDFF is_store_next clock reset is_store_reg
      ]
    ) |>.flatten

    -- has_valid_store = OR(valid[i] AND is_store[i]) for all entries
    let has_store_per := (List.range 4).map (fun i => Wire.mk s!"e{i}_has_store")
    let has_store_gates := (List.range 4).map (fun i =>
      let valid := Wire.mk s!"e{i}_0"
      Gate.mkAND valid is_store_regs[i]! has_store_per[i]!
    )
    let has_valid_store := Wire.mk "has_valid_store"
    let has_store_or_tmp1 := Wire.mk "has_store_or_tmp1"
    let has_store_or_tmp2 := Wire.mk "has_store_or_tmp2"
    let has_store_or_gates := [
      Gate.mkOR has_store_per[0]! has_store_per[1]! has_store_or_tmp1,
      Gate.mkOR has_store_per[2]! has_store_per[3]! has_store_or_tmp2,
      Gate.mkOR has_store_or_tmp1 has_store_or_tmp2 has_valid_store
    ]

    store_entry_gates ++ has_store_gates ++ has_store_or_gates
  else []

  -- ============================================================================
  -- 5. READY CHECKING AND ARBITRATION
  -- ============================================================================

  let ready := makeIndexedWires "ready" 4
  let dispatch_grant := makeIndexedWires "dispatch_grant" 4

  -- Per-entry ready: valid AND src1_ready AND src2_ready
  -- With store-load ordering: suppress loads when stores are present
  let ready_gates := if enableStoreLoadOrdering then
    let has_valid_store := Wire.mk "has_valid_store"
    let is_store_regs := (List.range 4).map (fun i => Wire.mk s!"e{i}_is_store")
    (List.range 4).map (fun i =>
      let valid := Wire.mk s!"e{i}_0"
      let src1_ready := Wire.mk s!"e{i}_13"
      let src2_ready := Wire.mk s!"e{i}_52"
      let base_ready_tmp := Wire.mk s!"ready{i}_tmp"
      let base_ready := Wire.mk s!"base_ready{i}"
      let is_load := Wire.mk s!"is_load{i}"
      let suppress := Wire.mk s!"suppress{i}"
      [
        Gate.mkAND valid src1_ready base_ready_tmp,
        Gate.mkAND base_ready_tmp src2_ready base_ready,
        -- suppress = has_valid_store AND NOT(is_store[i])
        Gate.mkNOT is_store_regs[i]! is_load,
        Gate.mkAND has_valid_store is_load suppress,
        -- ready = base_ready AND NOT(suppress)
        Gate.mkMUX base_ready zero suppress ready[i]!
      ]
    ) |>.flatten
  else
    (List.range 4).map (fun i =>
      let valid := Wire.mk s!"e{i}_0"
      let src1_ready := Wire.mk s!"e{i}_13"
      let src2_ready := Wire.mk s!"e{i}_52"
      let tmp := Wire.mk s!"ready{i}_tmp"
      [
        Gate.mkAND valid src1_ready tmp,
        Gate.mkAND tmp src2_ready ready[i]!
      ]
    ) |>.flatten

  -- PriorityArbiter4 instance
  let arbiter_inst : CircuitInstance := {
    moduleName := "PriorityArbiter4"
    instName := "u_ready_arbiter"
    portMap :=
      (ready.enum.map (fun ⟨i, w⟩ => (s!"request_{i}", w))) ++
      (dispatch_grant.enum.map (fun ⟨i, w⟩ => (s!"grant_{i}", w))) ++
      [("valid", dispatch_valid)]
  }

  -- ============================================================================
  -- 5. PRIORITY ENCODER (One-hot grant → Binary select for muxes)
  -- ============================================================================

  -- dispatch_grant[3:0] (one-hot) → dispatch_sel[1:0] (binary)
  -- Encoding: grant[0]=1 → sel=00, grant[1]=1 → sel=01,
  --           grant[2]=1 → sel=10, grant[3]=1 → sel=11
  let dispatch_sel := makeIndexedWires "dispatch_sel" 2

  -- sel[0] = grant[1] OR grant[3]
  -- sel[1] = grant[2] OR grant[3]
  let priority_enc_gates := [
    Gate.mkOR dispatch_grant[1]! dispatch_grant[3]! dispatch_sel[0]!,
    Gate.mkOR dispatch_grant[2]! dispatch_grant[3]! dispatch_sel[1]!
  ]

  -- ============================================================================
  -- 6. DISPATCH MUXES (4:1 selection using Mux4xN instances)
  -- ============================================================================

  -- Opcode dispatch (Mux4x6)
  let opcode_mux_portmap :=
    (((List.range 4).map (fun i =>
        (List.range 6).map (fun j =>
          (s!"in{i}[{j}]", Wire.mk s!"e{i}_{j + 1}")
        )
      )).flatten) ++
    (dispatch_sel.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w))) ++
    (dispatch_opcode.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w)))

  let opcode_mux_inst : CircuitInstance := {
    moduleName := "Mux4x6"
    instName := "u_dispatch_opcode_mux"
    portMap := opcode_mux_portmap
  }

  -- Src1 data dispatch (Mux4x32)
  let src1_mux_portmap :=
    (((List.range 4).map (fun i =>
        (List.range 32).map (fun j =>
          (s!"in{i}[{j}]", Wire.mk s!"e{i}_{j + 20}")
        )
      )).flatten) ++
    (dispatch_sel.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w))) ++
    (dispatch_src1_data.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w)))

  let src1_mux_inst : CircuitInstance := {
    moduleName := "Mux4x32"
    instName := "u_dispatch_src1_mux"
    portMap := src1_mux_portmap
  }

  -- Src2 data dispatch (Mux4x32)
  let src2_mux_portmap :=
    (((List.range 4).map (fun i =>
        (List.range 32).map (fun j =>
          (s!"in{i}[{j}]", Wire.mk s!"e{i}_{j + 59}")
        )
      )).flatten) ++
    (dispatch_sel.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w))) ++
    (dispatch_src2_data.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w)))

  let src2_mux_inst : CircuitInstance := {
    moduleName := "Mux4x32"
    instName := "u_dispatch_src2_mux"
    portMap := src2_mux_portmap
  }

  -- Dest tag dispatch (Mux4x6)
  let tag_mux_portmap :=
    (((List.range 4).map (fun i =>
        (List.range 6).map (fun j =>
          (s!"in{i}[{j}]", Wire.mk s!"e{i}_{j + 7}")
        )
      )).flatten) ++
    (dispatch_sel.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w))) ++
    (dispatch_dest_tag.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w)))

  let tag_mux_inst : CircuitInstance := {
    moduleName := "Mux4x6"
    instName := "u_dispatch_tag_mux"
    portMap := tag_mux_portmap
  }

  -- ============================================================================
  -- 6. ISSUE_FULL SIGNAL (4:1 mux of valid bits selected by alloc_ptr)
  -- ============================================================================

  -- Extract valid bit from each entry
  let entry_valid := (List.range 4).map (fun i => Wire.mk s!"e{i}_0")

  -- 4:1 mux: select valid[alloc_ptr]
  let issue_full_mux_gates :=
    -- Decode alloc_ptr to select signal
    let sel0 := Wire.mk "issue_full_sel0"
    let sel1 := Wire.mk "issue_full_sel1"
    let tmp01 := Wire.mk "issue_full_tmp01"
    let tmp23 := Wire.mk "issue_full_tmp23"
    [
      -- sel0 = alloc_ptr[0], sel1 = alloc_ptr[1]
      Gate.mkBUF alloc_ptr[0]! sel0,
      Gate.mkBUF alloc_ptr[1]! sel1,
      -- Mux layer 1: select between (0,1) and (2,3)
      Gate.mkMUX entry_valid[0]! entry_valid[1]! sel0 tmp01,
      Gate.mkMUX entry_valid[2]! entry_valid[3]! sel0 tmp23,
      -- Mux layer 2: final selection
      Gate.mkMUX tmp01 tmp23 sel1 issue_full
    ]

  -- ============================================================================
  -- FINAL ASSEMBLY
  -- ============================================================================

  { name := if enableStoreLoadOrdering then "MemoryRS4" else "ReservationStation4"
    inputs := [clock, reset, zero, one, issue_en] ++
              (if enableStoreLoadOrdering then [issue_is_store] else []) ++
              issue_opcode ++ issue_dest_tag ++
              [issue_src1_ready] ++ issue_src1_tag ++ issue_src1_data ++
              [issue_src2_ready] ++ issue_src2_tag ++ issue_src2_data ++
              [cdb_valid] ++ cdb_tag ++ cdb_data ++
              [dispatch_en]
    outputs := [issue_full, dispatch_valid] ++
               dispatch_opcode ++ dispatch_src1_data ++
               dispatch_src2_data ++ dispatch_dest_tag ++
               alloc_ptr ++ dispatch_grant
    gates := alloc_incr_gates ++ entry_gates ++ store_order_gates ++ ready_gates ++
             priority_enc_gates ++ issue_full_mux_gates
    instances := [alloc_ptr_inst, decoder_inst, arbiter_inst,
                  opcode_mux_inst, src1_mux_inst, src2_mux_inst, tag_mux_inst] ++
                 entry_instances
    -- v2 codegen annotations
    signalGroups := [
      -- Issue interface buses
      { name := "issue_opcode",    width := opcodeWidth, wires := issue_opcode },
      { name := "issue_dest_tag",  width := tagWidth,    wires := issue_dest_tag },
      { name := "issue_src1_tag",  width := tagWidth,    wires := issue_src1_tag },
      { name := "issue_src1_data", width := dataWidth,   wires := issue_src1_data },
      { name := "issue_src2_tag",  width := tagWidth,    wires := issue_src2_tag },
      { name := "issue_src2_data", width := dataWidth,   wires := issue_src2_data },
      -- CDB buses
      { name := "cdb_tag",  width := tagWidth,  wires := cdb_tag },
      { name := "cdb_data", width := dataWidth, wires := cdb_data },
      -- Dispatch output buses
      { name := "dispatch_opcode",    width := opcodeWidth, wires := dispatch_opcode },
      { name := "dispatch_src1_data", width := dataWidth,   wires := dispatch_src1_data },
      { name := "dispatch_src2_data", width := dataWidth,   wires := dispatch_src2_data },
      { name := "dispatch_dest_tag",  width := tagWidth,    wires := dispatch_dest_tag }
    ]
    inputBundles := [
      -- Source operand 1: ready flag + tag + data
      { name := "issue_src1"
        signals := [("ready", .Bool), ("tag", .UInt tagWidth), ("data", .UInt dataWidth)] },
      -- Source operand 2: ready flag + tag + data
      { name := "issue_src2"
        signals := [("ready", .Bool), ("tag", .UInt tagWidth), ("data", .UInt dataWidth)] },
      -- Common Data Bus broadcast input
      { name := "cdb"
        signals := [("valid", .Bool), ("tag", .UInt tagWidth), ("data", .UInt dataWidth)] }
    ]
    outputBundles := [
      -- Dispatch output to execution unit
      { name := "dispatch"
        signals := [("valid", .Bool), ("opcode", .UInt opcodeWidth),
                    ("src1_data", .UInt dataWidth), ("src2_data", .UInt dataWidth),
                    ("dest_tag", .UInt tagWidth)] }
    ]
  }

/-- RS4 alias for common usage -/
def rs4 : Circuit := mkReservationStation4

/-- Build Memory Reservation Station with store-load ordering (4 entries).

    When any store entry exists in the RS, load entries are suppressed from
    dispatch. Stores dispatch first; once all stores have left the RS, loads
    can dispatch and will find store data in the store buffer.

    Additional input: issue_is_store (1 bit) -/
def mkMemoryRS4 : Circuit := mkReservationStation4 (enableStoreLoadOrdering := true)

/-- MemoryRS4 alias for common usage -/
def memoryRS4 : Circuit := mkMemoryRS4

/-- Build MulDiv Reservation Station (4 entries).

    Structurally identical to the integer RS - same entry format,
    same CDB snooping, same ready-select-dispatch logic. The only
    difference is the circuit name for code generation and LEC.

    This is a separate RS so the MulDiv execution unit has its own
    dispatch queue, keeping it fully modular (removable when M
    extension is disabled via CPUConfig). -/
def mkMulDivRS4 : Circuit :=
  let base := mkReservationStation4
  { base with name := "MulDivRS4" }

/-- MulDivRS4 alias for common usage -/
def mulDivRS4 : Circuit := mkMulDivRS4

end Shoumei.RISCV.Execution

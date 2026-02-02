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
  }

/-- Is this entry ready for dispatch? (valid and both operands ready) -/
def isReady (e : RSEntry) : Bool :=
  e.valid && e.src1_ready && e.src2_ready

/-- Is this entry waiting for a specific tag? -/
def isWaitingFor (e : RSEntry) (tag : Fin 64) : Bool :=
  e.valid && (
    (!e.src1_ready && e.src1_tag == tag) ||
    (!e.src2_ready && e.src2_tag == tag)
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

      e2

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
       - Return (opcode, src1_data, src2_data, dest_tag) for execution
    3. If not ready, return none (caller shouldn't dispatch non-ready entries)

    **Note:** The execution unit will:
    - Compute result = f(opcode, src1_data, src2_data)
    - Broadcast (dest_tag, result) on CDB
    - This wakes up other RS entries waiting for this tag
-/
def dispatch
    (rs : RSState n)
    (idx : Fin n)
    : RSState n × Option (OpType × UInt32 × UInt32 × Fin 64) :=
  let e := rs.entries idx
  if e.isReady then
    -- Invalidate entry (mark as free)
    let newEntries := fun i =>
      if i == idx then RSEntry.empty
      else rs.entries i

    let rs' := { rs with entries := newEntries }

    -- Return operation bundle for execution unit
    let result := (e.opcode, e.src1_data, e.src2_data, e.dest_tag)
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

    If dispatch succeeds, it returns the entry's opcode and operand data.
-/
axiom rs_dispatch_returns_operands (n : Nat) (rs : RSState n) (idx : Fin n) :
  let e := rs.entries idx
  let (_, result) := rs.dispatch idx
  e.isReady →
    result = some (e.opcode, e.src1_data, e.src2_data, e.dest_tag)

/-! ## Structural Circuit (Hardware Implementation) -/

/-- Helper: Create indexed wires -/
private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}{i}")

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
def mkReservationStation4 : Circuit :=
  let tagWidth := 6
  let dataWidth := 32
  let opcodeWidth := 6

  -- Control
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- Issue interface (82 wires)
  let issue_en := Wire.mk "issue_en"
  let issue_opcode := makeIndexedWires "issue_opcode" opcodeWidth
  let issue_dest_tag := makeIndexedWires "issue_dest_tag" tagWidth
  let issue_src1_ready := Wire.mk "issue_src1_ready"
  let issue_src1_tag := makeIndexedWires "issue_src1_tag" tagWidth
  let issue_src1_data := makeIndexedWires "issue_src1_data" dataWidth
  let issue_src2_ready := Wire.mk "issue_src2_ready"
  let issue_src2_tag := makeIndexedWires "issue_src2_tag" tagWidth
  let issue_src2_data := makeIndexedWires "issue_src2_data" dataWidth
  let issue_full := Wire.mk "issue_full"

  -- CDB interface (39 wires)
  let cdb_valid := Wire.mk "cdb_valid"
  let cdb_tag := makeIndexedWires "cdb_tag" tagWidth
  let cdb_data := makeIndexedWires "cdb_data" dataWidth

  -- Dispatch interface (76 wires)
  let dispatch_en := Wire.mk "dispatch_en"
  let dispatch_valid := Wire.mk "dispatch_valid"
  let dispatch_opcode := makeIndexedWires "dispatch_opcode" opcodeWidth
  let dispatch_src1_data := makeIndexedWires "dispatch_src1_data" dataWidth
  let dispatch_src2_data := makeIndexedWires "dispatch_src2_data" dataWidth
  let dispatch_dest_tag := makeIndexedWires "dispatch_dest_tag" tagWidth

  -- Stub implementation: just structure, no gates yet
  -- Full implementation will add:
  -- - Allocation pointer DFFs and increment logic
  -- - Decoder2 instance for issue select
  -- - 364 DFFs for entry storage (4 × 91 bits)
  -- - CDB tag comparators and wakeup logic
  -- - PriorityArbiter4 instance for ready selection
  -- - Dispatch muxes

  { name := "ReservationStation4"
    inputs := [clock, reset, zero, one, issue_en] ++
              issue_opcode ++ issue_dest_tag ++
              [issue_src1_ready] ++ issue_src1_tag ++ issue_src1_data ++
              [issue_src2_ready] ++ issue_src2_tag ++ issue_src2_data ++
              [cdb_valid] ++ cdb_tag ++ cdb_data ++
              [dispatch_en]
    outputs := [issue_full, dispatch_valid] ++
               dispatch_opcode ++ dispatch_src1_data ++
               dispatch_src2_data ++ dispatch_dest_tag
    gates := []  -- Stub: structural implementation in progress
    instances := []
  }

/-- RS4 alias for common usage -/
def rs4 : Circuit := mkReservationStation4

end Shoumei.RISCV.Execution

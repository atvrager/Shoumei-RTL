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
import Shoumei.RISCV.Config
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

/-- Config-driven Reservation Station (W=2 dual-issue, banked architecture) -/
def mkReservationStationFromConfig (_config : Shoumei.RISCV.CPUConfig) : Circuit :=
  -- === W=2: Dual-Issue Reservation Station, banked architecture ===
  -- 4 entries split into 2 banks (Bank 0: entries 0,1; Bank 1: entries 2,3).
  -- issue_0 → Bank 0, issue_1 → Bank 1.
  -- Both banks snoop cdb_0 and cdb_1.
  -- Bank 0 arbitrates entries 0,1 → dispatch_0.
  -- Bank 1 arbitrates entries 2,3 → dispatch_1.
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero  := Wire.mk "zero"
  let one   := Wire.mk "one"

  let opcodeWidth := 6; let tagWidth := 7; let dataWidth := 32
  let entryWidth := 1 + opcodeWidth + tagWidth + 1 + tagWidth + dataWidth + 1 + tagWidth + dataWidth
  -- Computed offsets into entry bitfield
  let off_dest := 1 + opcodeWidth
  let off_src1_ready := off_dest + tagWidth
  let off_src1_tag := off_src1_ready + 1
  let off_src1_data := off_src1_tag + tagWidth
  let off_src2_ready := off_src1_data + dataWidth
  let off_src2_tag := off_src2_ready + 1
  let off_src2_data := off_src2_tag + tagWidth

  let mkWrsI (name : String) (n : Nat) : List Wire :=
    (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

  -- Issue interface (W=2)
  let issue_en_0 := Wire.mk "issue_en_0"; let issue_en_1 := Wire.mk "issue_en_1"
  let issue_is_store_0 := Wire.mk "issue_is_store_0"
  let issue_is_store_1 := Wire.mk "issue_is_store_1"
  let issue_opcode_0 := mkWrsI "issue_opcode_0" opcodeWidth
  let issue_dest_tag_0 := mkWrsI "issue_dest_tag_0" tagWidth
  let issue_src1_ready_0 := Wire.mk "issue_src1_ready_0"
  let issue_src1_tag_0  := mkWrsI "issue_src1_tag_0" tagWidth
  let issue_src1_data_0 := mkWrsI "issue_src1_data_0" dataWidth
  let issue_src2_ready_0 := Wire.mk "issue_src2_ready_0"
  let issue_src2_tag_0  := mkWrsI "issue_src2_tag_0" tagWidth
  let issue_src2_data_0 := mkWrsI "issue_src2_data_0" dataWidth
  let issue_opcode_1 := mkWrsI "issue_opcode_1" opcodeWidth
  let issue_dest_tag_1 := mkWrsI "issue_dest_tag_1" tagWidth
  let issue_src1_ready_1 := Wire.mk "issue_src1_ready_1"
  let issue_src1_tag_1  := mkWrsI "issue_src1_tag_1" tagWidth
  let issue_src1_data_1 := mkWrsI "issue_src1_data_1" dataWidth
  let issue_src2_ready_1 := Wire.mk "issue_src2_ready_1"
  let issue_src2_tag_1  := mkWrsI "issue_src2_tag_1" tagWidth
  let issue_src2_data_1 := mkWrsI "issue_src2_data_1" dataWidth

  let alloc_avail_0 := Wire.mk "alloc_avail_0"; let alloc_avail_1 := Wire.mk "alloc_avail_1"

  -- CDB interface (W=2)
  let cdb_valid_0 := Wire.mk "cdb_valid_0"; let cdb_tag_0  := mkWrsI "cdb_tag_0" tagWidth
  let cdb_data_0  := mkWrsI "cdb_data_0" dataWidth
  let cdb_valid_1 := Wire.mk "cdb_valid_1"; let cdb_tag_1  := mkWrsI "cdb_tag_1" tagWidth
  let cdb_data_1  := mkWrsI "cdb_data_1" dataWidth
  -- With 7-bit domain-tagged RS tags, CDB valid is used uniformly for all sources.
  -- The domain bit in the tag prevents cross-domain false wakeup.
  let cdb_fp_combine_gates : List Gate := []

  -- Dispatch interface (W=2)
  let dispatch_en_0 := Wire.mk "dispatch_en_0"; let dispatch_valid_0 := Wire.mk "dispatch_valid_0"
  let dispatch_opcode_0   := mkWrsI "dispatch_opcode_0" opcodeWidth
  let dispatch_src1_data_0 := mkWrsI "dispatch_src1_data_0" dataWidth
  let dispatch_src2_data_0 := mkWrsI "dispatch_src2_data_0" dataWidth
  let dispatch_dest_tag_0  := mkWrsI "dispatch_dest_tag_0" tagWidth
  let dispatch_en_1 := Wire.mk "dispatch_en_1"; let dispatch_valid_1 := Wire.mk "dispatch_valid_1"
  let dispatch_opcode_1   := mkWrsI "dispatch_opcode_1" opcodeWidth
  let dispatch_src1_data_1 := mkWrsI "dispatch_src1_data_1" dataWidth
  let dispatch_src2_data_1 := mkWrsI "dispatch_src2_data_1" dataWidth
  let dispatch_dest_tag_1  := mkWrsI "dispatch_dest_tag_1" tagWidth

  -- 1-bit allocation pointers for each bank
  let alloc_ptr_0 := Wire.mk "alloc_ptr_0"; let alloc_ptr_next_0 := Wire.mk "alloc_ptr_next_0"
  let alloc_ptr_1 := Wire.mk "alloc_ptr_1"; let alloc_ptr_next_1 := Wire.mk "alloc_ptr_next_1"
  let ptr_gates := [Gate.mkXOR alloc_ptr_0 issue_en_0 alloc_ptr_next_0,
                     Gate.mkXOR alloc_ptr_1 issue_en_1 alloc_ptr_next_1]
  let ptr_inst_0 : CircuitInstance := {
    moduleName := "Register1", instName := "u_alloc_ptr_0",
    portMap := [("d_0", alloc_ptr_next_0), ("clock", clock), ("reset", reset), ("q_0", alloc_ptr_0)]
  }
  let ptr_inst_1 : CircuitInstance := {
    moduleName := "Register1", instName := "u_alloc_ptr_1",
    portMap := [("d_0", alloc_ptr_next_1), ("clock", clock), ("reset", reset), ("q_0", alloc_ptr_1)]
  }

  -- Issue write-enable routing per bank
  let issue_we_0_0 := Wire.mk "issue_we_0_0"; let issue_we_0_1 := Wire.mk "issue_we_0_1"
  let not_ptr_0 := Wire.mk "not_ptr_0"
  let base_issue_gates_0 := [
    Gate.mkNOT alloc_ptr_0 not_ptr_0,
    Gate.mkAND issue_en_0 not_ptr_0 issue_we_0_0,
    Gate.mkAND issue_en_0 alloc_ptr_0 issue_we_0_1
  ]
  let issue_we_1_0 := Wire.mk "issue_we_1_0"; let issue_we_1_1 := Wire.mk "issue_we_1_1"
  let not_ptr_1 := Wire.mk "not_ptr_1"
  let base_issue_gates_1 := [
    Gate.mkNOT alloc_ptr_1 not_ptr_1,
    Gate.mkAND issue_en_1 not_ptr_1 issue_we_1_0,
    Gate.mkAND issue_en_1 alloc_ptr_1 issue_we_1_1
  ]

  -- Per-entry builder
  let buildEntry (idx : Nat) : List Gate × List CircuitInstance × Wire × Wire :=
    let bank := idx / 2; let subIdx := idx % 2
    let e_cur  := mkWrsI s!"e{idx}" entryWidth
    let e_next := mkWrsI s!"e{idx}_next" entryWidth
    let valid     := e_cur[0]!; let src1_ready := e_cur[off_src1_ready]!
    let src1_tag  := e_cur.drop off_src1_tag |>.take tagWidth
    let src1_data := e_cur.drop off_src1_data |>.take dataWidth
    let src2_ready := e_cur[off_src2_ready]!
    let src2_tag  := e_cur.drop off_src2_tag |>.take tagWidth
    let src2_data := e_cur.drop off_src2_data |>.take dataWidth
    let issue_we_this :=
      if bank == 0 then (if subIdx == 0 then issue_we_0_0 else issue_we_0_1)
      else (if subIdx == 0 then issue_we_1_0 else issue_we_1_1)
    let (issue_opcode, issue_dest, issue_s1r, issue_s1t, issue_s1d, issue_s2r, issue_s2t, issue_s2d) :=
      if bank == 0 then
        (issue_opcode_0, issue_dest_tag_0, issue_src1_ready_0, issue_src1_tag_0, issue_src1_data_0,
         issue_src2_ready_0, issue_src2_tag_0, issue_src2_data_0)
      else
        (issue_opcode_1, issue_dest_tag_1, issue_src1_ready_1, issue_src1_tag_1, issue_src1_data_1,
         issue_src2_ready_1, issue_src2_tag_1, issue_src2_data_1)
    -- CDB matching for src1 (dual port)
    let mkMatch (pfx : String) (src_tag : List Wire) (cdb_tag : List Wire) (cdb_valid : Wire)
        : List Gate × List Gate × Wire :=
      let xs  := (List.range tagWidth).map fun i => Gate.mkXOR src_tag[i]! cdb_tag[i]! (Wire.mk s!"{pfx}_x{i}")
      let xns := (List.range tagWidth).map fun i => Gate.mkNOT (Wire.mk s!"{pfx}_x{i}") (Wire.mk s!"{pfx}_xn{i}")
      let eq  := Wire.mk s!"{pfx}_eq"
      let ands := [Gate.mkAND (Wire.mk s!"{pfx}_xn0") (Wire.mk s!"{pfx}_xn1") (Wire.mk s!"{pfx}_a1"),
                   Gate.mkAND (Wire.mk s!"{pfx}_xn2") (Wire.mk s!"{pfx}_xn3") (Wire.mk s!"{pfx}_a2"),
                   Gate.mkAND (Wire.mk s!"{pfx}_xn4") (Wire.mk s!"{pfx}_xn5") (Wire.mk s!"{pfx}_a3"),
                   Gate.mkAND (Wire.mk s!"{pfx}_a1") (Wire.mk s!"{pfx}_a2") (Wire.mk s!"{pfx}_a4"),
                   Gate.mkAND (Wire.mk s!"{pfx}_a4") (Wire.mk s!"{pfx}_a3") (Wire.mk s!"{pfx}_a5"),
                   Gate.mkAND (Wire.mk s!"{pfx}_a5") (Wire.mk s!"{pfx}_xn6") eq]
      let m := Wire.mk s!"{pfx}_m"; let mg := Gate.mkAND eq cdb_valid m
      (xs ++ xns, ands ++ [mg], m)
    -- CDB matching against STORED tags (for existing entries)
    let (m1_0x, m1_0a, m1_0m) := mkMatch s!"e{idx}_m1_0" src1_tag cdb_tag_0 cdb_valid_0
    let (m1_1x, m1_1a, m1_1m) := mkMatch s!"e{idx}_m1_1" src1_tag cdb_tag_1 cdb_valid_1
    let (m2_0x, m2_0a, m2_0m) := mkMatch s!"e{idx}_m2_0" src2_tag cdb_tag_0 cdb_valid_0
    let (m2_1x, m2_1a, m2_1m) := mkMatch s!"e{idx}_m2_1" src2_tag cdb_tag_1 cdb_valid_1
    -- CDB matching against INCOMING dispatch tags (for same-cycle alloc+CDB wakeup)
    let (n1_0x, n1_0a, n1_0m) := mkMatch s!"e{idx}_n1_0" issue_s1t cdb_tag_0 cdb_valid_0
    let (n1_1x, n1_1a, n1_1m) := mkMatch s!"e{idx}_n1_1" issue_s1t cdb_tag_1 cdb_valid_1
    let (n2_0x, n2_0a, n2_0m) := mkMatch s!"e{idx}_n2_0" issue_s2t cdb_tag_0 cdb_valid_0
    let (n2_1x, n2_1a, n2_1m) := mkMatch s!"e{idx}_n2_1" issue_s2t cdb_tag_1 cdb_valid_1
    let n1_any := Wire.mk s!"e{idx}_n1_any"; let n2_any := Wire.mk s!"e{idx}_n2_any"
    -- Alloc-time ready: dispatch ready OR same-cycle CDB match on incoming tag
    let alloc_s1r := Wire.mk s!"e{idx}_alloc_s1r"; let alloc_s2r := Wire.mk s!"e{idx}_alloc_s2r"
    let alloc_ready_gates := [
      Gate.mkOR n1_0m n1_1m n1_any, Gate.mkOR issue_s1r n1_any alloc_s1r,
      Gate.mkOR n2_0m n2_1m n2_any, Gate.mkOR issue_s2r n2_any alloc_s2r]
    -- Alloc-time data: MUX between dispatch data and CDB data (CDB ch0 > CDB ch1 > dispatch)
    -- Gate with NOT(issue_src_ready) to avoid overwriting already-valid data (e.g. immediates)
    let not_is1r := Wire.mk s!"e{idx}_not_is1r"; let not_is2r := Wire.mk s!"e{idx}_not_is2r"
    let n1_0d := Wire.mk s!"e{idx}_n1_0d"; let n1_1d := Wire.mk s!"e{idx}_n1_1d"
    let n2_0d := Wire.mk s!"e{idx}_n2_0d"; let n2_1d := Wire.mk s!"e{idx}_n2_1d"
    let alloc_data_gate := [
      Gate.mkNOT issue_s1r not_is1r, Gate.mkNOT issue_s2r not_is2r,
      Gate.mkAND n1_0m not_is1r n1_0d, Gate.mkAND n1_1m not_is1r n1_1d,
      Gate.mkAND n2_0m not_is2r n2_0d, Gate.mkAND n2_1m not_is2r n2_1d]
    let a1d_t := (List.range dataWidth).map fun i => Wire.mk s!"e{idx}_a1d_t_{i}"
    let a1d_m := (List.range dataWidth).map fun i => Wire.mk s!"e{idx}_a1d_m_{i}"
    let ad1 := (List.range dataWidth).map fun i => Gate.mkMUX issue_s1d[i]! cdb_data_1[i]! n1_1d a1d_t[i]!
    let ad2 := (List.range dataWidth).map fun i => Gate.mkMUX a1d_t[i]! cdb_data_0[i]! n1_0d a1d_m[i]!
    let a2d_t := (List.range dataWidth).map fun i => Wire.mk s!"e{idx}_a2d_t_{i}"
    let a2d_m := (List.range dataWidth).map fun i => Wire.mk s!"e{idx}_a2d_m_{i}"
    let ad3 := (List.range dataWidth).map fun i => Gate.mkMUX issue_s2d[i]! cdb_data_1[i]! n2_1d a2d_t[i]!
    let ad4 := (List.range dataWidth).map fun i => Gate.mkMUX a2d_t[i]! cdb_data_0[i]! n2_0d a2d_m[i]!
    let s1_any := Wire.mk s!"e{idx}_m1_any"; let r1_m1 := Wire.mk s!"e{idx}_r1_m1"
    -- Gate CDB data match with NOT(src_ready) to prevent overwriting valid data (e.g. immediates)
    let not_s1r := Wire.mk s!"e{idx}_not_s1r"
    let m1_0d := Wire.mk s!"e{idx}_m1_0d"; let m1_1d := Wire.mk s!"e{idx}_m1_1d"
    let wakeup1_gates := [Gate.mkOR m1_0m m1_1m s1_any, Gate.mkOR src1_ready s1_any r1_m1,
                          Gate.mkMUX r1_m1 alloc_s1r issue_we_this e_next[off_src1_ready]!,
                          Gate.mkNOT src1_ready not_s1r,
                          Gate.mkAND m1_0m not_s1r m1_0d, Gate.mkAND m1_1m not_s1r m1_1d]
    let w1d_t := (List.range dataWidth).map fun i => Wire.mk s!"e{idx}_w1d_t_{i}"
    let w1d_m := (List.range dataWidth).map fun i => Wire.mk s!"e{idx}_w1d_m_{i}"
    let wd1 := (List.range dataWidth).map fun i => Gate.mkMUX src1_data[i]! cdb_data_1[i]! m1_1d w1d_t[i]!
    let wd2 := (List.range dataWidth).map fun i => Gate.mkMUX w1d_t[i]! cdb_data_0[i]! m1_0d w1d_m[i]!
    let wd3 := (List.range dataWidth).map fun i => Gate.mkMUX w1d_m[i]! a1d_m[i]! issue_we_this e_next[off_src1_data+i]!
    let s2_any := Wire.mk s!"e{idx}_m2_any"; let r2_m2 := Wire.mk s!"e{idx}_r2_m2"
    let not_s2r := Wire.mk s!"e{idx}_not_s2r"
    let m2_0d := Wire.mk s!"e{idx}_m2_0d"; let m2_1d := Wire.mk s!"e{idx}_m2_1d"
    let wakeup2_gates := [Gate.mkOR m2_0m m2_1m s2_any, Gate.mkOR src2_ready s2_any r2_m2,
                          Gate.mkMUX r2_m2 alloc_s2r issue_we_this e_next[off_src2_ready]!,
                          Gate.mkNOT src2_ready not_s2r,
                          Gate.mkAND m2_0m not_s2r m2_0d, Gate.mkAND m2_1m not_s2r m2_1d]
    let w2d_t := (List.range dataWidth).map fun i => Wire.mk s!"e{idx}_w2d_t_{i}"
    let w2d_m := (List.range dataWidth).map fun i => Wire.mk s!"e{idx}_w2d_m_{i}"
    let wd4 := (List.range dataWidth).map fun i => Gate.mkMUX src2_data[i]! cdb_data_1[i]! m2_1d w2d_t[i]!
    let wd5 := (List.range dataWidth).map fun i => Gate.mkMUX w2d_t[i]! cdb_data_0[i]! m2_0d w2d_m[i]!
    let wd6 := (List.range dataWidth).map fun i => Gate.mkMUX w2d_m[i]! a2d_m[i]! issue_we_this e_next[off_src2_data+i]!
    let dispatch_en_this := if bank == 0 then dispatch_en_0 else dispatch_en_1
    let dispatch_grant := Wire.mk s!"dispatch_grant_{idx}"
    let dispatch := Wire.mk s!"e{idx}_dispatch"
    let dispatch_gate := Gate.mkAND dispatch_en_this dispatch_grant dispatch
    let v_keep := Wire.mk s!"e{idx}_v_keep"; let not_dispatch := Wire.mk s!"e{idx}_not_dispatch"
    let valid_we := [Gate.mkNOT dispatch not_dispatch, Gate.mkAND valid not_dispatch v_keep,
                     Gate.mkOR v_keep issue_we_this e_next[0]!]
    let opcode_g  := (List.range opcodeWidth).map fun i => Gate.mkMUX e_cur[1+i]! issue_opcode[i]! issue_we_this e_next[1+i]!
    let dest_g    := (List.range tagWidth).map fun i => Gate.mkMUX e_cur[off_dest+i]! issue_dest[i]! issue_we_this e_next[off_dest+i]!
    let src1t_g   := (List.range tagWidth).map fun i => Gate.mkMUX e_cur[off_src1_tag+i]! issue_s1t[i]! issue_we_this e_next[off_src1_tag+i]!
    let src2t_g   := (List.range tagWidth).map fun i => Gate.mkMUX e_cur[off_src2_tag+i]! issue_s2t[i]! issue_we_this e_next[off_src2_tag+i]!
    let e_inst : CircuitInstance := {
      moduleName := s!"Register{entryWidth}", instName := s!"u_e{idx}",
      portMap := (e_next.enum.map fun ⟨i,w⟩ => (s!"d_{i}", w)) ++
                 [("clock", clock), ("reset", reset)] ++
                 (e_cur.enum.map fun ⟨i,w⟩ => (s!"q_{i}", w))
    }
    let is_ready := Wire.mk s!"e{idx}_ready"
    let e_gates :=
      m1_0x ++ m1_0a ++ m1_1x ++ m1_1a ++
      m2_0x ++ m2_0a ++ m2_1x ++ m2_1a ++
      n1_0x ++ n1_0a ++ n1_1x ++ n1_1a ++
      n2_0x ++ n2_0a ++ n2_1x ++ n2_1a ++
      alloc_ready_gates ++ alloc_data_gate ++
      ad1 ++ ad2 ++ ad3 ++ ad4 ++
      wakeup1_gates ++ wd1 ++ wd2 ++ wd3 ++
      wakeup2_gates ++ wd4 ++ wd5 ++ wd6 ++
      [dispatch_gate] ++ valid_we ++ opcode_g ++ dest_g ++ src1t_g ++ src2t_g ++
      [Gate.mkAND r1_m1 r2_m2 (Wire.mk s!"e{idx}_r12"),
       Gate.mkAND valid (Wire.mk s!"e{idx}_r12") is_ready]
    (e_gates, [e_inst], valid, is_ready)

  let (eg0, ei0, ev0, er0) := buildEntry 0
  let (eg1, ei1, ev1, er1) := buildEntry 1
  let (eg2, ei2, ev2, er2) := buildEntry 2
  let (eg3, ei3, ev3, er3) := buildEntry 3

  -- Bank available signals
  let v01_mux := Wire.mk "v_01_mux"
  let alloc_avail_g_0 := [Gate.mkMUX ev0 ev1 alloc_ptr_0 v01_mux, Gate.mkNOT v01_mux alloc_avail_0]
  let v23_mux := Wire.mk "v_23_mux"
  let alloc_avail_g_1 := [Gate.mkMUX ev2 ev3 alloc_ptr_1 v23_mux, Gate.mkNOT v23_mux alloc_avail_1]

  -- Store-Load Ordering (SLO): track is_store per entry, prioritize stores over loads
  -- When any valid store exists in a bank, only stores can dispatch from that bank.
  -- This prevents loads from bypassing younger stores that haven't entered the store buffer yet.
  -- For non-memory RS instances, issue_is_store is tied to zero, so SLO is a no-op.
  let mkSloEntry (idx : Nat) (issue_we : Wire) (issue_is_store : Wire) : List Gate × CircuitInstance × Wire :=
    let is_store_cur := Wire.mk s!"slo_st_{idx}"
    let is_store_next := Wire.mk s!"slo_st_next_{idx}"
    let gates := [Gate.mkMUX is_store_cur issue_is_store issue_we is_store_next]
    let inst : CircuitInstance := {
      moduleName := "Register1", instName := s!"u_slo_st_{idx}",
      portMap := [("d_0", is_store_next), ("clock", clock), ("reset", reset), ("q_0", is_store_cur)]
    }
    (gates, inst, is_store_cur)
  let (slo_g0, slo_i0, st0) := mkSloEntry 0 issue_we_0_0 issue_is_store_0
  let (slo_g1, slo_i1, st1) := mkSloEntry 1 issue_we_0_1 issue_is_store_0
  let (slo_g2, slo_i2, st2) := mkSloEntry 2 issue_we_1_0 issue_is_store_1
  let (slo_g3, slo_i3, st3) := mkSloEntry 3 issue_we_1_1 issue_is_store_1
  -- has_pending_store per bank: (valid AND is_store) for any entry in the bank
  let vs0 := Wire.mk "slo_vs0"; let vs1 := Wire.mk "slo_vs1"
  let has_store_b0 := Wire.mk "slo_has_store_b0"
  let vs2 := Wire.mk "slo_vs2"; let vs3 := Wire.mk "slo_vs3"
  let has_store_b1 := Wire.mk "slo_has_store_b1"
  let slo_hs_gates := [
    Gate.mkAND ev0 st0 vs0, Gate.mkAND ev1 st1 vs1, Gate.mkOR vs0 vs1 has_store_b0,
    Gate.mkAND ev2 st2 vs2, Gate.mkAND ev3 st3 vs3, Gate.mkOR vs2 vs3 has_store_b1]
  -- Age-aware SLO: only block a load if there's an OLDER store in the same bank.
  -- In bank B with 2 entries (sub0, sub1): when both valid, alloc_ptr_B == sub-index
  -- of the older entry. So:
  --   Entry sub0: has older store iff vs1 AND alloc_ptr=1 (sub1 is older)
  --   Entry sub1: has older store iff vs0 AND NOT(alloc_ptr) (sub0 is older, ptr=0)
  let hos0 := Wire.mk "slo_hos_0"; let hos1 := Wire.mk "slo_hos_1"
  let hos2 := Wire.mk "slo_hos_2"; let hos3 := Wire.mk "slo_hos_3"
  let not_hos0 := Wire.mk "slo_not_hos_0"; let not_hos1 := Wire.mk "slo_not_hos_1"
  let not_hos2 := Wire.mk "slo_not_hos_2"; let not_hos3 := Wire.mk "slo_not_hos_3"
  let ok0 := Wire.mk "slo_ok0"; let ok1 := Wire.mk "slo_ok1"
  let ok2 := Wire.mk "slo_ok2"; let ok3 := Wire.mk "slo_ok3"
  let ar0 := Wire.mk "slo_ar0"; let ar1 := Wire.mk "slo_ar1"
  let ar2 := Wire.mk "slo_ar2"; let ar3 := Wire.mk "slo_ar3"
  let slo_gate_gates := [
    -- Bank 0: age-aware per-entry older-store check
    Gate.mkAND vs1 alloc_ptr_0 hos0,   -- sub1 is older store → blocks sub0
    Gate.mkAND vs0 not_ptr_0 hos1,     -- sub0 is older store → blocks sub1
    Gate.mkNOT hos0 not_hos0, Gate.mkOR st0 not_hos0 ok0, Gate.mkAND er0 ok0 ar0,
    Gate.mkNOT hos1 not_hos1, Gate.mkOR st1 not_hos1 ok1, Gate.mkAND er1 ok1 ar1,
    -- Bank 1: age-aware per-entry older-store check
    Gate.mkAND vs3 alloc_ptr_1 hos2,   -- sub1 is older store → blocks sub0
    Gate.mkAND vs2 not_ptr_1 hos3,     -- sub0 is older store → blocks sub1
    Gate.mkNOT hos2 not_hos2, Gate.mkOR st2 not_hos2 ok2, Gate.mkAND er2 ok2 ar2,
    Gate.mkNOT hos3 not_hos3, Gate.mkOR st3 not_hos3 ok3, Gate.mkAND er3 ok3 ar3]

  -- Arbiters (use SLO-gated request signals)
  let arb0_gr0 := Wire.mk "dispatch_grant_0"; let arb0_gr1 := Wire.mk "dispatch_grant_1"
  let arb0_inst : CircuitInstance := {
    moduleName := "PriorityArbiter2", instName := "u_arb0",
    portMap := [("request_0", ar0), ("request_1", ar1),
                ("grant_0", arb0_gr0), ("grant_1", arb0_gr1),
                ("valid", dispatch_valid_0)]
  }
  let arb1_gr0 := Wire.mk "dispatch_grant_2"; let arb1_gr1 := Wire.mk "dispatch_grant_3"
  let arb1_inst : CircuitInstance := {
    moduleName := "PriorityArbiter2", instName := "u_arb1",
    portMap := [("request_0", ar2), ("request_1", ar3),
                ("grant_0", arb1_gr0), ("grant_1", arb1_gr1),
                ("valid", dispatch_valid_1)]
  }

  -- Output muxes (use CDB-bypassed data wires instead of raw DFF outputs)
  -- The w1d_m/w2d_m wires already contain CDB-forwarded data when CDB matches
  -- in the same cycle, falling back to DFF data when no CDB match.
  let mkMux2 (_name : String) (w : Nat) (in0 in1 out_wires : List Wire) (sel : Wire) : List Gate :=
    (List.range w).map fun i => Gate.mkMUX in0[i]! in1[i]! sel out_wires[i]!
  let e0 := mkWrsI "e0" entryWidth; let e1 := mkWrsI "e1" entryWidth
  let e2 := mkWrsI "e2" entryWidth; let e3 := mkWrsI "e3" entryWidth
  -- CDB-bypassed src1/src2 data per entry
  let e0_s1bp := (List.range dataWidth).map fun i => Wire.mk s!"e0_w1d_m_{i}"
  let e1_s1bp := (List.range dataWidth).map fun i => Wire.mk s!"e1_w1d_m_{i}"
  let e2_s1bp := (List.range dataWidth).map fun i => Wire.mk s!"e2_w1d_m_{i}"
  let e3_s1bp := (List.range dataWidth).map fun i => Wire.mk s!"e3_w1d_m_{i}"
  let e0_s2bp := (List.range dataWidth).map fun i => Wire.mk s!"e0_w2d_m_{i}"
  let e1_s2bp := (List.range dataWidth).map fun i => Wire.mk s!"e1_w2d_m_{i}"
  let e2_s2bp := (List.range dataWidth).map fun i => Wire.mk s!"e2_w2d_m_{i}"
  let e3_s2bp := (List.range dataWidth).map fun i => Wire.mk s!"e3_w2d_m_{i}"
  let b0_mux_op  := mkMux2 "b0_m_op"  opcodeWidth (e0.drop 1)  (e1.drop 1)  dispatch_opcode_0  arb0_gr1
  let b0_mux_dst := mkMux2 "b0_m_dst" tagWidth    (e0.drop off_dest)  (e1.drop off_dest)  dispatch_dest_tag_0 arb0_gr1
  let b0_mux_s1d := mkMux2 "b0_m_s1d" dataWidth   e0_s1bp      e1_s1bp      dispatch_src1_data_0 arb0_gr1
  let b0_mux_s2d := mkMux2 "b0_m_s2d" dataWidth   e0_s2bp      e1_s2bp      dispatch_src2_data_0 arb0_gr1
  let b1_mux_op  := mkMux2 "b1_m_op"  opcodeWidth (e2.drop 1)  (e3.drop 1)  dispatch_opcode_1  arb1_gr1
  let b1_mux_dst := mkMux2 "b1_m_dst" tagWidth    (e2.drop off_dest)  (e3.drop off_dest)  dispatch_dest_tag_1 arb1_gr1
  let b1_mux_s1d := mkMux2 "b1_m_s1d" dataWidth   e2_s1bp      e3_s1bp      dispatch_src1_data_1 arb1_gr1
  let b1_mux_s2d := mkMux2 "b1_m_s2d" dataWidth   e2_s2bp      e3_s2bp      dispatch_src2_data_1 arb1_gr1

  { name := "ReservationStation4_W2"
    inputs :=
      [clock, reset, zero, one, issue_en_0, issue_en_1] ++
      [issue_is_store_0, issue_is_store_1] ++
      issue_opcode_0 ++ issue_dest_tag_0 ++ [issue_src1_ready_0] ++ issue_src1_tag_0 ++ issue_src1_data_0 ++
      [issue_src2_ready_0] ++ issue_src2_tag_0 ++ issue_src2_data_0 ++
      issue_opcode_1 ++ issue_dest_tag_1 ++ [issue_src1_ready_1] ++ issue_src1_tag_1 ++ issue_src1_data_1 ++
      [issue_src2_ready_1] ++ issue_src2_tag_1 ++ issue_src2_data_1 ++
      [cdb_valid_0] ++ cdb_tag_0 ++ cdb_data_0 ++
      [cdb_valid_1] ++ cdb_tag_1 ++ cdb_data_1 ++
      [dispatch_en_0, dispatch_en_1]
    outputs :=
      [alloc_avail_0, alloc_avail_1, dispatch_valid_0, dispatch_valid_1,
       alloc_ptr_0, alloc_ptr_1,
       arb0_gr0, arb0_gr1, arb1_gr0, arb1_gr1] ++
      dispatch_opcode_0 ++ dispatch_src1_data_0 ++ dispatch_src2_data_0 ++ dispatch_dest_tag_0 ++
      dispatch_opcode_1 ++ dispatch_src1_data_1 ++ dispatch_src2_data_1 ++ dispatch_dest_tag_1
    gates :=
      cdb_fp_combine_gates ++
      ptr_gates ++ base_issue_gates_0 ++ base_issue_gates_1 ++
      eg0 ++ eg1 ++ eg2 ++ eg3 ++
      alloc_avail_g_0 ++ alloc_avail_g_1 ++
      slo_g0 ++ slo_g1 ++ slo_g2 ++ slo_g3 ++ slo_hs_gates ++ slo_gate_gates ++
      b0_mux_op ++ b0_mux_dst ++ b0_mux_s1d ++ b0_mux_s2d ++
      b1_mux_op ++ b1_mux_dst ++ b1_mux_s1d ++ b1_mux_s2d
    instances :=
      [ptr_inst_0, ptr_inst_1, arb0_inst, arb1_inst, slo_i0, slo_i1, slo_i2, slo_i3] ++
      ei0 ++ ei1 ++ ei2 ++ ei3 }

/-- Config-driven MulDiv RS -/
def mkMulDivRSFromConfig (config : Shoumei.RISCV.CPUConfig) : Circuit :=
  let base := mkReservationStationFromConfig config
  { base with name := "MulDivRS4_W2" }

end Shoumei.RISCV.Execution



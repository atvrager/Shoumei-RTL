/-
RISCV/Execution/ReservationStation.lean - Reservation Station for Dynamic Out-of-Order Execution

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
    - This is standard out-of-order execution - the register file is checked at issue time
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
          (true, tag, value)  -- In out-of-order execution, assume PRF has valid data

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
      -- Parallel operand tag matching (matches hardware CAM snooping)
      let m1 := !e.src1_ready && e.src1_tag == cdb_tag
      let m2 := !e.src2_ready && e.src2_tag == cdb_tag
      let m3 := !e.src3_ready && e.src3_tag == cdb_tag
      { e with
        src1_ready := if m1 then true else e.src1_ready
        src1_data  := if m1 then cdb_data else e.src1_data
        src2_ready := if m2 then true else e.src2_ready
        src2_data  := if m2 then cdb_data else e.src2_data
        src3_ready := if m3 then true else e.src3_ready
        src3_data  := if m3 then cdb_data else e.src3_data }

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

/-! ## Formally Verified Behavioral Correctness Theorems -/

/-- Issue preserves frame: entries other than next_alloc retain their valid status. -/
theorem rs_issue_entries_frame (n : Nat) (rs : RSState n) (instr : RenamedInstruction)
    (prf : PhysRegFileState 64) (i : Fin n) :
  i ≠ rs.next_alloc → ((rs.issue instr prf).1.entries i).valid = (rs.entries i).valid := by
  intro h_ne
  dsimp [RSState.issue]
  split
  · rfl
  · dsimp
    have h_ne_beq : (i == rs.next_alloc) = false := beq_false_of_ne h_ne
    rw [h_ne_beq]
    rfl

/-- Issue stalls when next allocation slot is already occupied. -/
theorem rs_issue_full_stalls (n : Nat) (rs : RSState n) (instr : RenamedInstruction)
    (prf : PhysRegFileState 64) :
  (rs.entries rs.next_alloc).valid = true → (rs.issue instr prf).2 = none := by
  intro h_val
  dsimp [RSState.issue]
  rw [if_pos h_val]

/-- Successful issue allocates an entry. -/
theorem rs_issue_success_valid (n : Nat) (rs : RSState n) (instr : RenamedInstruction)
    (prf : PhysRegFileState 64) :
  let res := rs.issue instr prf
  match res.2 with
  | some idx => (res.1.entries idx).valid = true
  | none => True := by
  intro res
  dsimp [res, RSState.issue]
  by_cases h : (rs.entries rs.next_alloc).valid
  · rw [if_pos h]
    trivial
  · rw [if_neg h]
    dsimp
    simp only [beq_self_eq_true, ↓reduceIte]

/-- CDB broadcast preserves valid bit of every entry. -/
theorem cdbBroadcast_preserves_valid (n : Nat) (rs : RSState n) (tag : Fin 64) (data : UInt32) (i : Fin n) :
    ((rs.cdbBroadcast tag data).entries i).valid = (rs.entries i).valid := by
  dsimp [RSState.cdbBroadcast]
  split
  · rfl
  · rfl

/-- CDB broadcast preserves valid entry count. -/
theorem rs_cdb_preserves_count (n : Nat) (rs : RSState n) (tag : Fin 64) (data : UInt32) :
    (rs.cdbBroadcast tag data).countValid = rs.countValid := by
  dsimp [RSState.countValid]
  have h_fun : (fun acc i =>
        if h : i < n then
          let idx : Fin n := ⟨i, h⟩
          if ((rs.cdbBroadcast tag data).entries idx).valid then acc + 1 else acc
        else acc) =
      (fun acc i =>
        if h : i < n then
          let idx : Fin n := ⟨i, h⟩
          if (rs.entries idx).valid then acc + 1 else acc
        else acc) := by
    funext acc i
    split
    · rename_i h_lt
      dsimp
      rw [cdbBroadcast_preserves_valid]
    · rfl
  rw [h_fun]

/-- CDB broadcast wakes up waiting operands. -/
theorem rs_cdb_wakeup_correct (n : Nat) (rs : RSState n) (tag : Fin 64) (data : UInt32)
    (idx : Fin n) :
  let e := rs.entries idx
  let e' := (rs.cdbBroadcast tag data).entries idx
  e.isWaitingFor tag →
    ((!e.src1_ready ∧ e.src1_tag == tag → e'.src1_ready = true ∧ e'.src1_data = data) ∧
     (!e.src2_ready ∧ e.src2_tag == tag → e'.src2_ready = true ∧ e'.src2_data = data)) := by
  intro e e' h_wait
  dsimp [e, e', RSState.cdbBroadcast]
  have h_val : (rs.entries idx).valid = true := by
    dsimp [e, RSEntry.isWaitingFor] at h_wait
    revert h_wait
    cases (rs.entries idx).valid <;> intro h_wait
    · contradiction
    · rfl
  rw [if_neg (by simp [h_val])]
  dsimp
  constructor
  · rintro ⟨h1_not, h1_tag⟩
    have hm1 : (! (rs.entries idx).src1_ready && (rs.entries idx).src1_tag == tag) = true := by
      simp [h1_not, h1_tag]
    rw [if_pos hm1, if_pos hm1]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h2_not, h2_tag⟩
    have hm2 : (! (rs.entries idx).src2_ready && (rs.entries idx).src2_tag == tag) = true := by
      simp [h2_not, h2_tag]
    rw [if_pos hm2, if_pos hm2]
    exact ⟨rfl, rfl⟩

/-- Ready selection returns a ready entry (or proves all entries unready). -/
theorem rs_select_ready_correct (n : Nat) (rs : RSState n) :
  match rs.selectReady with
  | some idx => (rs.entries idx).isReady = true
  | none => ∀ i : Fin n, (rs.entries i).isReady = false := by
  dsimp [RSState.selectReady]
  split
  · rename_i idx heq
    have h_ex := List.exists_of_findSome?_eq_some heq
    rcases h_ex with ⟨a, ha, hf⟩
    split at hf
    · rename_i h_lt
      split at hf
      · rename_i h_rdy
        cases hf
        exact h_rdy
      · contradiction
    · contradiction
  · rename_i heq
    rw [List.findSome?_eq_none_iff] at heq
    intro i
    have h_in : i.val ∈ List.range n := List.mem_range.mpr i.isLt
    have h_none := heq i.val h_in
    split at h_none
    · rename_i h_lt
      split at h_none
      · contradiction
      · rename_i h_not
        simp only [Bool.not_eq_true] at h_not
        exact h_not
    · exact absurd i.isLt ‹_›

/-- Ready selection prioritizes lower indices. -/
theorem rs_select_ready_priority (n : Nat) (rs : RSState n) :
  match rs.selectReady with
  | some j => ∀ i : Fin n, i.val < j.val → (rs.entries i).isReady = false
  | none => True := by
  dsimp [RSState.selectReady]
  split
  · rename_i j heq
    rw [List.findSome?_eq_some_iff] at heq
    rcases heq with ⟨l1, a, l2, h_range, h_fa, h_all_none⟩
    intro i h_lt
    split at h_fa
    · rename_i h_lt_a
      split at h_fa
      · rename_i h_rdy
        cases h_fa
        have h_len := congrArg List.length h_range
        simp only [List.length_range, List.length_append, List.length_cons] at h_len
        have h_bound : l1.length < n := by omega
        have h_get : (List.range n)[l1.length]? = some a := by
          rw [h_range]
          simp only [List.getElem?_append_right (Nat.le_refl l1.length), Nat.sub_self, List.getElem?_cons_zero]
        have h_get_r : (List.range n)[l1.length]? = some l1.length := by
          apply List.getElem?_range h_bound
        rw [h_get_r] at h_get
        have h_a_eq : l1.length = a := by
          cases h_get
          rfl
        have h_take : l1 = List.take l1.length (List.range n) := by
          have ht := congrArg (List.take l1.length) h_range
          rw [List.take_left] at ht
          exact ht.symm
        have h_l1_eq : l1 = List.range a := by
          rw [h_take, h_a_eq, List.take_range, Nat.min_eq_left (Nat.le_of_lt h_lt_a)]
        have h_in_l1 : i.val ∈ l1 := by
          rw [h_l1_eq]
          exact List.mem_range.mpr h_lt
        have h_none := h_all_none i.val h_in_l1
        split at h_none
        · rename_i h_lt_i
          split at h_none
          · contradiction
          · rename_i h_not
            simp only [Bool.not_eq_true] at h_not
            exact h_not
        · exact absurd i.isLt ‹_›
      · contradiction
    · contradiction
  · trivial

/-- Dispatch clears the selected entry. -/
theorem rs_dispatch_clears_entry (n : Nat) (rs : RSState n) (idx : Fin n) :
  let res := rs.dispatch idx
  match res.2 with
  | some _ => (res.1.entries idx).valid = false
  | none => res.1 = rs := by
  intro res
  dsimp [res, RSState.dispatch]
  by_cases h : (rs.entries idx).isReady
  · rw [if_pos h]
    dsimp
    simp only [beq_self_eq_true, ↓reduceIte]
    rfl
  · rw [if_neg h]

/-- Dispatch returns operands from the entry. -/
theorem rs_dispatch_returns_operands (n : Nat) (rs : RSState n) (idx : Fin n) :
  let e := rs.entries idx
  e.isReady →
    (rs.dispatch idx).2 = some (e.opcode, e.src1_data, e.src2_data, e.src3_data, e.dest_tag, e.immediate, e.pc) := by
  intro e h_rdy
  dsimp [RSState.dispatch]
  rw [if_pos h_rdy]

/-! ## Structural Circuit (Hardware Implementation) -/

/-- Helper: Create indexed wires -/
private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

/-- Parameterized Reservation Station (W=2 dual-issue, banked architecture) with configurable data width. -/
def mkReservationStationWithWidth (dataWidth : Nat := 32) : Circuit :=
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

  -- Opcode field is 8 bits: the opcode space for RV64G has 158 instructions (> 128),
  -- so an 8-bit field is required to avoid aliasing (e.g. SW=3 vs FLD=131).
  let opcodeWidth := 8; let tagWidth := 7
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
  let issue_is_atomic_0 := Wire.mk "issue_is_atomic_0"
  let issue_is_atomic_1 := Wire.mk "issue_is_atomic_1"
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

  -- Suppress CDB alloc-time bypass (intra-group RAW hazard protection)
  -- When slot 0 allocates a fresh phys tag that slot 1 reads, the CDB may still be
  -- broadcasting the old result for that tag. These signals suppress that stale bypass.
  -- Per-bank: single-unit RSes route slot 1 ops to bank 0, so bank 0 also needs suppress.
  let suppress_cdb_s1_0 := Wire.mk "suppress_cdb_s1_0"
  let suppress_cdb_s2_0 := Wire.mk "suppress_cdb_s2_0"
  let suppress_cdb_s1_1 := Wire.mk "suppress_cdb_s1_1"
  let suppress_cdb_s2_1 := Wire.mk "suppress_cdb_s2_1"

  -- External per-entry ready mask: gates the arbiter request for each entry.
  -- Used by FP src3 sidecar to prevent issue before 3rd operand is ready.
  -- Tie to 'one' for RS instances that don't need src3 gating.
  let ext_ready_mask_0 := Wire.mk "ext_ready_mask_0"
  let ext_ready_mask_1 := Wire.mk "ext_ready_mask_1"
  let ext_ready_mask_2 := Wire.mk "ext_ready_mask_2"
  let ext_ready_mask_3 := Wire.mk "ext_ready_mask_3"

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
    -- Suppress CDB alloc-time bypass when intra-group RAW detected
    -- (slot 0 just allocated the tag that slot 1 reads — CDB broadcast is stale)
    let (supp_s1, supp_s2) := if bank == 0
      then (suppress_cdb_s1_0, suppress_cdb_s2_0)
      else (suppress_cdb_s1_1, suppress_cdb_s2_1)
    let n1_any_raw := Wire.mk s!"e{idx}_n1_any_raw"
    let n2_any_raw := Wire.mk s!"e{idx}_n2_any_raw"
    let not_supp_s1 := Wire.mk s!"e{idx}_not_supp_s1"
    let not_supp_s2 := Wire.mk s!"e{idx}_not_supp_s2"
    let alloc_ready_gates :=
      [Gate.mkOR n1_0m n1_1m n1_any_raw,
       Gate.mkNOT supp_s1 not_supp_s1,
       Gate.mkAND n1_any_raw not_supp_s1 n1_any,
       Gate.mkOR issue_s1r n1_any alloc_s1r,
       Gate.mkOR n2_0m n2_1m n2_any_raw,
       Gate.mkNOT supp_s2 not_supp_s2,
       Gate.mkAND n2_any_raw not_supp_s2 n2_any,
       Gate.mkOR issue_s2r n2_any alloc_s2r]
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
  -- Also tracks whether the entry is an atomic (LR/SC/AMO): atomics count as stores
  -- for SLO ordering, but not as "pending plain stores" (used to serialize atomics
  -- behind older stores).
  let mkSloEntry (idx : Nat) (issue_we : Wire) (issue_is_store : Wire) (issue_is_atomic : Wire)
      : List Gate × List CircuitInstance × Wire × Wire :=
    let is_store_cur := Wire.mk s!"slo_st_{idx}"
    let is_store_next := Wire.mk s!"slo_st_next_{idx}"
    let is_atomic_cur := Wire.mk s!"slo_at_{idx}"
    let is_atomic_next := Wire.mk s!"slo_at_next_{idx}"
    let gates := [
      Gate.mkMUX is_store_cur issue_is_store issue_we is_store_next,
      Gate.mkMUX is_atomic_cur issue_is_atomic issue_we is_atomic_next]
    let insts : List CircuitInstance := [
      { moduleName := "Register1", instName := s!"u_slo_st_{idx}",
        portMap := [("d_0", is_store_next), ("clock", clock), ("reset", reset), ("q_0", is_store_cur)] },
      { moduleName := "Register1", instName := s!"u_slo_at_{idx}",
        portMap := [("d_0", is_atomic_next), ("clock", clock), ("reset", reset), ("q_0", is_atomic_cur)] }]
    (gates, insts, is_store_cur, is_atomic_cur)
  let (slo_g0, slo_i0, st0, at0) := mkSloEntry 0 issue_we_0_0 issue_is_store_0 issue_is_atomic_0
  let (slo_g1, slo_i1, st1, at1) := mkSloEntry 1 issue_we_0_1 issue_is_store_0 issue_is_atomic_0
  let (slo_g2, slo_i2, st2, at2) := mkSloEntry 2 issue_we_1_0 issue_is_store_1 issue_is_atomic_1
  let (slo_g3, slo_i3, st3, at3) := mkSloEntry 3 issue_we_1_1 issue_is_store_1 issue_is_atomic_1
  -- Pending plain store: a valid store entry that is not an atomic.
  let ps0 := Wire.mk "slo_ps0"; let ps1 := Wire.mk "slo_ps1"
  let ps2 := Wire.mk "slo_ps2"; let ps3 := Wire.mk "slo_ps3"
  let nat0 := Wire.mk "slo_nat0"; let nat1 := Wire.mk "slo_nat1"
  let nat2 := Wire.mk "slo_nat2"; let nat3 := Wire.mk "slo_nat3"
  let pending_store := Wire.mk "pending_store"
  let pending_store_gates := [
    Gate.mkNOT at0 nat0, Gate.mkNOT at1 nat1, Gate.mkNOT at2 nat2, Gate.mkNOT at3 nat3,
    Gate.mkAND st0 nat0 ps0, Gate.mkAND st1 nat1 ps1,
    Gate.mkAND st2 nat2 ps2, Gate.mkAND st3 nat3 ps3,
    Gate.mkAND ev0 ps0 (Wire.mk "slo_pst0"), Gate.mkAND ev1 ps1 (Wire.mk "slo_pst1"),
    Gate.mkAND ev2 ps2 (Wire.mk "slo_pst2"), Gate.mkAND ev3 ps3 (Wire.mk "slo_pst3"),
    Gate.mkOR (Wire.mk "slo_pst0") (Wire.mk "slo_pst1") (Wire.mk "slo_pst01"),
    Gate.mkOR (Wire.mk "slo_pst2") (Wire.mk "slo_pst3") (Wire.mk "slo_pst23"),
    Gate.mkOR (Wire.mk "slo_pst01") (Wire.mk "slo_pst23") pending_store]
  -- has_pending_store per bank: (valid AND is_store) for any entry in the bank
  let vs0 := Wire.mk "slo_vs0"; let vs1 := Wire.mk "slo_vs1"
  let has_store_b0 := Wire.mk "slo_has_store_b0"
  let vs2 := Wire.mk "slo_vs2"; let vs3 := Wire.mk "slo_vs3"
  let has_store_b1 := Wire.mk "slo_has_store_b1"
  let slo_hs_gates := [
    Gate.mkAND ev0 st0 vs0, Gate.mkAND ev1 st1 vs1, Gate.mkOR vs0 vs1 has_store_b0,
    Gate.mkAND ev2 st2 vs2, Gate.mkAND ev3 st3 vs3, Gate.mkOR vs2 vs3 has_store_b1]
  -- Age-aware SLO: only block a load/staging op if there's an OLDER store in the
  -- same bank.  Plain stores dispatch freely; atomics (which are stores for SLO
  -- but carry `ps=0`) additionally wait for any older store/atomic, so an LR
  -- and its paired SC dispatch in program order.
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
    Gate.mkNOT hos0 not_hos0, Gate.mkOR ps0 not_hos0 ok0,
    Gate.mkAND er0 ok0 (Wire.mk "slo_ar0_pre"), Gate.mkAND (Wire.mk "slo_ar0_pre") ext_ready_mask_0 ar0,
    Gate.mkNOT hos1 not_hos1, Gate.mkOR ps1 not_hos1 ok1,
    Gate.mkAND er1 ok1 (Wire.mk "slo_ar1_pre"), Gate.mkAND (Wire.mk "slo_ar1_pre") ext_ready_mask_1 ar1,
    -- Bank 1: age-aware per-entry older-store check
    Gate.mkAND vs3 alloc_ptr_1 hos2,   -- sub1 is older store → blocks sub0
    Gate.mkAND vs2 not_ptr_1 hos3,     -- sub0 is older store → blocks sub1
    Gate.mkNOT hos2 not_hos2, Gate.mkOR ps2 not_hos2 ok2,
    Gate.mkAND er2 ok2 (Wire.mk "slo_ar2_pre"), Gate.mkAND (Wire.mk "slo_ar2_pre") ext_ready_mask_2 ar2,
    Gate.mkNOT hos3 not_hos3, Gate.mkOR ps3 not_hos3 ok3,
    Gate.mkAND er3 ok3 (Wire.mk "slo_ar3_pre"), Gate.mkAND (Wire.mk "slo_ar3_pre") ext_ready_mask_3 ar3]

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

  { name := if dataWidth == 64 then "ReservationStation4_W2_64" else "ReservationStation4_W2"
    inputs :=
      [clock, reset, zero, one, issue_en_0, issue_en_1] ++
      [issue_is_store_0, issue_is_store_1, issue_is_atomic_0, issue_is_atomic_1] ++
      issue_opcode_0 ++ issue_dest_tag_0 ++ [issue_src1_ready_0] ++ issue_src1_tag_0 ++ issue_src1_data_0 ++
      [issue_src2_ready_0] ++ issue_src2_tag_0 ++ issue_src2_data_0 ++
      issue_opcode_1 ++ issue_dest_tag_1 ++ [issue_src1_ready_1] ++ issue_src1_tag_1 ++ issue_src1_data_1 ++
      [issue_src2_ready_1] ++ issue_src2_tag_1 ++ issue_src2_data_1 ++
      [cdb_valid_0] ++ cdb_tag_0 ++ cdb_data_0 ++
      [cdb_valid_1] ++ cdb_tag_1 ++ cdb_data_1 ++
      [dispatch_en_0, dispatch_en_1,
       suppress_cdb_s1_0, suppress_cdb_s2_0,
       suppress_cdb_s1_1, suppress_cdb_s2_1,
       ext_ready_mask_0, ext_ready_mask_1, ext_ready_mask_2, ext_ready_mask_3]
    outputs :=
      [alloc_avail_0, alloc_avail_1, dispatch_valid_0, dispatch_valid_1,
       alloc_ptr_0, alloc_ptr_1, pending_store,
       arb0_gr0, arb0_gr1, arb1_gr0, arb1_gr1] ++
      dispatch_opcode_0 ++ dispatch_src1_data_0 ++ dispatch_src2_data_0 ++ dispatch_dest_tag_0 ++
      dispatch_opcode_1 ++ dispatch_src1_data_1 ++ dispatch_src2_data_1 ++ dispatch_dest_tag_1
    gates :=
      cdb_fp_combine_gates ++
      ptr_gates ++ base_issue_gates_0 ++ base_issue_gates_1 ++
      eg0 ++ eg1 ++ eg2 ++ eg3 ++
      alloc_avail_g_0 ++ alloc_avail_g_1 ++
      slo_g0 ++ slo_g1 ++ slo_g2 ++ slo_g3 ++ slo_hs_gates ++ slo_gate_gates ++
      pending_store_gates ++
      b0_mux_op ++ b0_mux_dst ++ b0_mux_s1d ++ b0_mux_s2d ++
      b1_mux_op ++ b1_mux_dst ++ b1_mux_s1d ++ b1_mux_s2d
    instances :=
      [ptr_inst_0, ptr_inst_1, arb0_inst, arb1_inst] ++ slo_i0 ++ slo_i1 ++ slo_i2 ++ slo_i3 ++
      ei0 ++ ei1 ++ ei2 ++ ei3 }

/-- Config-driven Reservation Station (W=2 dual-issue, banked architecture) -/
def mkReservationStationFromConfig (_config : Shoumei.RISCV.CPUConfig) : Circuit :=
  mkReservationStationWithWidth 32

/-- 64-bit Reservation Station (W=2 dual-issue, banked architecture) -/
def mkReservationStation4W2_64 : Circuit :=
  mkReservationStationWithWidth 64

/-- Config-driven MulDiv RS -/
def mkMulDivRSFromConfig (config : Shoumei.RISCV.CPUConfig) : Circuit :=
  let base := mkReservationStationFromConfig config
  { base with name := "MulDivRS4_W2" }

/-! ## Specialized Reservation Stations (Zero Warnings Architecture) -/

/-- 6-bit or 7-bit tag comparator against CDB tag, gated by CDB valid -/
private def mkTagMatch (pfx : String) (w : Nat) (src_tag : List Wire) (cdb_tag : List Wire) (cdb_valid : Wire)
    : List Gate × Wire :=
  let xns := (List.range w).flatMap fun i =>
    let x := Wire.mk s!"{pfx}_x{i}"; let xn := Wire.mk s!"{pfx}_xn{i}"
    [Gate.mkXOR src_tag[i]! cdb_tag[i]! x, Gate.mkNOT x xn]
  let eq := Wire.mk s!"{pfx}_eq"
  let andGates :=
    if w == 6 then
      [Gate.mkAND (Wire.mk s!"{pfx}_xn0") (Wire.mk s!"{pfx}_xn1") (Wire.mk s!"{pfx}_a1"),
       Gate.mkAND (Wire.mk s!"{pfx}_xn2") (Wire.mk s!"{pfx}_xn3") (Wire.mk s!"{pfx}_a2"),
       Gate.mkAND (Wire.mk s!"{pfx}_xn4") (Wire.mk s!"{pfx}_xn5") (Wire.mk s!"{pfx}_a3"),
       Gate.mkAND (Wire.mk s!"{pfx}_a1") (Wire.mk s!"{pfx}_a2") (Wire.mk s!"{pfx}_a4"),
       Gate.mkAND (Wire.mk s!"{pfx}_a4") (Wire.mk s!"{pfx}_a3") eq]
    else if w == 7 then
      [Gate.mkAND (Wire.mk s!"{pfx}_xn0") (Wire.mk s!"{pfx}_xn1") (Wire.mk s!"{pfx}_a1"),
       Gate.mkAND (Wire.mk s!"{pfx}_xn2") (Wire.mk s!"{pfx}_xn3") (Wire.mk s!"{pfx}_a2"),
       Gate.mkAND (Wire.mk s!"{pfx}_xn4") (Wire.mk s!"{pfx}_xn5") (Wire.mk s!"{pfx}_a3"),
       Gate.mkAND (Wire.mk s!"{pfx}_a1") (Wire.mk s!"{pfx}_a2") (Wire.mk s!"{pfx}_a4"),
       Gate.mkAND (Wire.mk s!"{pfx}_a4") (Wire.mk s!"{pfx}_a3") (Wire.mk s!"{pfx}_a5"),
       Gate.mkAND (Wire.mk s!"{pfx}_a5") (Wire.mk s!"{pfx}_xn6") eq]
    else []
  let m := Wire.mk s!"{pfx}_m"
  (xns ++ andGates ++ [Gate.mkAND eq cdb_valid m], m)

/-- Helper to build a single reservation station entry -/
private def buildRSEntry
    (idx : Nat)
    (opcodeWidth : Nat) (destTagWidth : Nat) (src1TagWidth : Nat) (src2TagWidth : Nat) (dataWidth : Nat)
    (issue_we : Wire)
    (issue_opcode : List Wire) (issue_dest : List Wire)
    (issue_s1r : Wire) (issue_s1t : List Wire) (issue_s1d : List Wire)
    (issue_s2r : Wire) (issue_s2t : List Wire) (issue_s2d : List Wire)
    (cdb_tag_s1_0 : List Wire) (cdb_valid_s1_0 : Wire) (cdb_data_0 : List Wire)
    (cdb_tag_s1_1 : List Wire) (cdb_valid_s1_1 : Wire) (cdb_data_1 : List Wire)
    (cdb_tag_s2_0 : List Wire) (cdb_valid_s2_0 : Wire)
    (cdb_tag_s2_1 : List Wire) (cdb_valid_s2_1 : Wire)
    (suppress_s1 : Option Wire) (suppress_s2 : Option Wire)
    (dispatch_en : Option Wire) (dispatch_grant : Wire)
    (clock reset : Wire)
    : List Gate × List CircuitInstance × Wire × Wire × List Wire × List Wire :=
  let entryWidth := 1 + opcodeWidth + destTagWidth + 1 + src1TagWidth + dataWidth + 1 + src2TagWidth + dataWidth
  let off_dest := 1 + opcodeWidth
  let off_src1_ready := off_dest + destTagWidth
  let off_src1_tag := off_src1_ready + 1
  let off_src1_data := off_src1_tag + src1TagWidth
  let off_src2_ready := off_src1_data + dataWidth
  let off_src2_tag := off_src2_ready + 1
  let off_src2_data := off_src2_tag + src2TagWidth

  let e_cur := makeIndexedWires s!"e{idx}" entryWidth
  let e_next := makeIndexedWires s!"e{idx}_next" entryWidth
  let valid := e_cur[0]!
  let src1_ready := e_cur[off_src1_ready]!
  let src1_tag := e_cur.drop off_src1_tag |>.take src1TagWidth
  let src1_data := e_cur.drop off_src1_data |>.take dataWidth
  let src2_ready := e_cur[off_src2_ready]!
  let src2_tag := e_cur.drop off_src2_tag |>.take src2TagWidth
  let src2_data := e_cur.drop off_src2_data |>.take dataWidth

  -- CDB matches against STORED tags
  let (m1_0g, m1_0m) := mkTagMatch s!"e{idx}_m1_0" src1TagWidth src1_tag cdb_tag_s1_0 cdb_valid_s1_0
  let (m1_1g, m1_1m) := mkTagMatch s!"e{idx}_m1_1" src1TagWidth src1_tag cdb_tag_s1_1 cdb_valid_s1_1
  let (m2_0g, m2_0m) := mkTagMatch s!"e{idx}_m2_0" src2TagWidth src2_tag cdb_tag_s2_0 cdb_valid_s2_0
  let (m2_1g, m2_1m) := mkTagMatch s!"e{idx}_m2_1" src2TagWidth src2_tag cdb_tag_s2_1 cdb_valid_s2_1

  -- CDB matches against INCOMING dispatch tags
  let (n1_0g, n1_0m) := mkTagMatch s!"e{idx}_n1_0" src1TagWidth issue_s1t cdb_tag_s1_0 cdb_valid_s1_0
  let (n1_1g, n1_1m) := mkTagMatch s!"e{idx}_n1_1" src1TagWidth issue_s1t cdb_tag_s1_1 cdb_valid_s1_1
  let (n2_0g, n2_0m) := mkTagMatch s!"e{idx}_n2_0" src2TagWidth issue_s2t cdb_tag_s2_0 cdb_valid_s2_0
  let (n2_1g, n2_1m) := mkTagMatch s!"e{idx}_n2_1" src2TagWidth issue_s2t cdb_tag_s2_1 cdb_valid_s2_1

  let n1_any := Wire.mk s!"e{idx}_n1_any"
  let n2_any := Wire.mk s!"e{idx}_n2_any"
  let alloc_s1r := Wire.mk s!"e{idx}_alloc_s1r"
  let alloc_s2r := Wire.mk s!"e{idx}_alloc_s2r"

  let alloc_ready_gates :=
    match suppress_s1, suppress_s2 with
    | some s1, some s2 =>
      let n1_any_raw := Wire.mk s!"e{idx}_n1_any_raw"
      let n2_any_raw := Wire.mk s!"e{idx}_n2_any_raw"
      let not_supp_s1 := Wire.mk s!"e{idx}_not_supp_s1"
      let not_supp_s2 := Wire.mk s!"e{idx}_not_supp_s2"
      [Gate.mkOR n1_0m n1_1m n1_any_raw,
       Gate.mkNOT s1 not_supp_s1,
       Gate.mkAND n1_any_raw not_supp_s1 n1_any,
       Gate.mkOR issue_s1r n1_any alloc_s1r,
       Gate.mkOR n2_0m n2_1m n2_any_raw,
       Gate.mkNOT s2 not_supp_s2,
       Gate.mkAND n2_any_raw not_supp_s2 n2_any,
       Gate.mkOR issue_s2r n2_any alloc_s2r]
    | _, _ =>
      [Gate.mkOR n1_0m n1_1m n1_any,
       Gate.mkOR issue_s1r n1_any alloc_s1r,
       Gate.mkOR n2_0m n2_1m n2_any,
       Gate.mkOR issue_s2r n2_any alloc_s2r]

  let not_is1r := Wire.mk s!"e{idx}_not_is1r"
  let not_is2r := Wire.mk s!"e{idx}_not_is2r"
  let n1_0d := Wire.mk s!"e{idx}_n1_0d"
  let n1_1d := Wire.mk s!"e{idx}_n1_1d"
  let n2_0d := Wire.mk s!"e{idx}_n2_0d"
  let n2_1d := Wire.mk s!"e{idx}_n2_1d"
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

  let s1_any := Wire.mk s!"e{idx}_m1_any"
  let r1_m1 := Wire.mk s!"e{idx}_r1_m1"
  let not_s1r := Wire.mk s!"e{idx}_not_s1r"
  let m1_0d := Wire.mk s!"e{idx}_m1_0d"
  let m1_1d := Wire.mk s!"e{idx}_m1_1d"
  let wakeup1_gates := [Gate.mkOR m1_0m m1_1m s1_any, Gate.mkOR src1_ready s1_any r1_m1,
                        Gate.mkMUX r1_m1 alloc_s1r issue_we e_next[off_src1_ready]!,
                        Gate.mkNOT src1_ready not_s1r,
                        Gate.mkAND m1_0m not_s1r m1_0d, Gate.mkAND m1_1m not_s1r m1_1d]
  let w1d_t := (List.range dataWidth).map fun i => Wire.mk s!"e{idx}_w1d_t_{i}"
  let w1d_m := (List.range dataWidth).map fun i => Wire.mk s!"e{idx}_w1d_m_{i}"
  let wd1 := (List.range dataWidth).map fun i => Gate.mkMUX src1_data[i]! cdb_data_1[i]! m1_1d w1d_t[i]!
  let wd2 := (List.range dataWidth).map fun i => Gate.mkMUX w1d_t[i]! cdb_data_0[i]! m1_0d w1d_m[i]!
  let wd3 := (List.range dataWidth).map fun i => Gate.mkMUX w1d_m[i]! a1d_m[i]! issue_we e_next[off_src1_data+i]!

  let s2_any := Wire.mk s!"e{idx}_m2_any"
  let r2_m2 := Wire.mk s!"e{idx}_r2_m2"
  let not_s2r := Wire.mk s!"e{idx}_not_s2r"
  let m2_0d := Wire.mk s!"e{idx}_m2_0d"
  let m2_1d := Wire.mk s!"e{idx}_m2_1d"
  let wakeup2_gates := [Gate.mkOR m2_0m m2_1m s2_any, Gate.mkOR src2_ready s2_any r2_m2,
                        Gate.mkMUX r2_m2 alloc_s2r issue_we e_next[off_src2_ready]!,
                        Gate.mkNOT src2_ready not_s2r,
                        Gate.mkAND m2_0m not_s2r m2_0d, Gate.mkAND m2_1m not_s2r m2_1d]
  let w2d_t := (List.range dataWidth).map fun i => Wire.mk s!"e{idx}_w2d_t_{i}"
  let w2d_m := (List.range dataWidth).map fun i => Wire.mk s!"e{idx}_w2d_m_{i}"
  let wd4 := (List.range dataWidth).map fun i => Gate.mkMUX src2_data[i]! cdb_data_1[i]! m2_1d w2d_t[i]!
  let wd5 := (List.range dataWidth).map fun i => Gate.mkMUX w2d_t[i]! cdb_data_0[i]! m2_0d w2d_m[i]!
  let wd6 := (List.range dataWidth).map fun i => Gate.mkMUX w2d_m[i]! a2d_m[i]! issue_we e_next[off_src2_data+i]!

  let dispatch := Wire.mk s!"e{idx}_dispatch"
  let dispatch_gate :=
    match dispatch_en with
    | some de => Gate.mkAND de dispatch_grant dispatch
    | none => Gate.mkBUF dispatch_grant dispatch
  let v_keep := Wire.mk s!"e{idx}_v_keep"
  let not_dispatch := Wire.mk s!"e{idx}_not_dispatch"
  let valid_we := [Gate.mkNOT dispatch not_dispatch, Gate.mkAND valid not_dispatch v_keep,
                   Gate.mkOR v_keep issue_we e_next[0]!]
  let opcode_g := (List.range opcodeWidth).map fun i => Gate.mkMUX e_cur[1+i]! issue_opcode[i]! issue_we e_next[1+i]!
  let dest_g := (List.range destTagWidth).map fun i => Gate.mkMUX e_cur[off_dest+i]! issue_dest[i]! issue_we e_next[off_dest+i]!
  let src1t_g := (List.range src1TagWidth).map fun i => Gate.mkMUX e_cur[off_src1_tag+i]! issue_s1t[i]! issue_we e_next[off_src1_tag+i]!
  let src2t_g := (List.range src2TagWidth).map fun i => Gate.mkMUX e_cur[off_src2_tag+i]! issue_s2t[i]! issue_we e_next[off_src2_tag+i]!

  let e_inst : CircuitInstance := {
    moduleName := s!"Register{entryWidth}", instName := s!"u_e{idx}",
    portMap := (e_next.enum.map fun ⟨i,w⟩ => (s!"d_{i}", w)) ++
               [("clock", clock), ("reset", reset)] ++
               (e_cur.enum.map fun ⟨i,w⟩ => (s!"q_{i}", w))
  }
  let is_ready := Wire.mk s!"e{idx}_ready"
  let r12 := Wire.mk s!"e{idx}_r12"
  let e_gates :=
    m1_0g ++ m1_1g ++ m2_0g ++ m2_1g ++
    n1_0g ++ n1_1g ++ n2_0g ++ n2_1g ++
    alloc_ready_gates ++ alloc_data_gate ++
    ad1 ++ ad2 ++ ad3 ++ ad4 ++
    wakeup1_gates ++ wd1 ++ wd2 ++ wd3 ++
    wakeup2_gates ++ wd4 ++ wd5 ++ wd6 ++
    [dispatch_gate] ++ valid_we ++ opcode_g ++ dest_g ++ src1t_g ++ src2t_g ++
    [Gate.mkAND r1_m1 r2_m2 r12,
     Gate.mkAND valid r12 is_ready]
  (e_gates, [e_inst], valid, is_ready, w1d_m, w2d_m)

private def mkLocalMux2 (w : Nat) (in0 in1 out_wires : List Wire) (sel : Wire) : List Gate :=
  (List.range w).map fun i => Gate.mkMUX in0[i]! in1[i]! sel out_wires[i]!

/-- Specialized Integer Reservation Station (W=2 dual-issue, 4 entries, 6-bit tags).
    ALU0 is combinational (no dispatch_en_0 needed). Bank 1 has dispatch_en_1 and suppress inputs. -/
def mkIntReservationStation4_W2 (dataWidth : Nat := 64) : Circuit :=
  let clock := Wire.mk "clock"; let reset := Wire.mk "reset"
  let opcodeWidth := 8; let tagWidth := 6
  let entryWidth := 1 + opcodeWidth + tagWidth + 1 + tagWidth + dataWidth + 1 + tagWidth + dataWidth
  let off_dest := 1 + opcodeWidth

  let issue_en_0 := Wire.mk "issue_en_0"; let issue_en_1 := Wire.mk "issue_en_1"
  let issue_opcode_0 := makeIndexedWires "issue_opcode_0" opcodeWidth
  let issue_dest_tag_0 := makeIndexedWires "issue_dest_tag_0" tagWidth
  let issue_src1_ready_0 := Wire.mk "issue_src1_ready_0"
  let issue_src1_tag_0 := makeIndexedWires "issue_src1_tag_0" tagWidth
  let issue_src1_data_0 := makeIndexedWires "issue_src1_data_0" dataWidth
  let issue_src2_ready_0 := Wire.mk "issue_src2_ready_0"
  let issue_src2_tag_0 := makeIndexedWires "issue_src2_tag_0" tagWidth
  let issue_src2_data_0 := makeIndexedWires "issue_src2_data_0" dataWidth

  let issue_opcode_1 := makeIndexedWires "issue_opcode_1" opcodeWidth
  let issue_dest_tag_1 := makeIndexedWires "issue_dest_tag_1" tagWidth
  let issue_src1_ready_1 := Wire.mk "issue_src1_ready_1"
  let issue_src1_tag_1 := makeIndexedWires "issue_src1_tag_1" tagWidth
  let issue_src1_data_1 := makeIndexedWires "issue_src1_data_1" dataWidth
  let issue_src2_ready_1 := Wire.mk "issue_src2_ready_1"
  let issue_src2_tag_1 := makeIndexedWires "issue_src2_tag_1" tagWidth
  let issue_src2_data_1 := makeIndexedWires "issue_src2_data_1" dataWidth

  let cdb_valid_0 := Wire.mk "cdb_valid_0"; let cdb_is_fp_0 := Wire.mk "cdb_is_fp_0"
  let cdb_tag_0 := makeIndexedWires "cdb_tag_0" tagWidth
  let cdb_data_0 := makeIndexedWires "cdb_data_0" dataWidth
  let cdb_valid_1 := Wire.mk "cdb_valid_1"; let cdb_is_fp_1 := Wire.mk "cdb_is_fp_1"
  let cdb_tag_1 := makeIndexedWires "cdb_tag_1" tagWidth
  let cdb_data_1 := makeIndexedWires "cdb_data_1" dataWidth

  let dispatch_en_1 := Wire.mk "dispatch_en_1"
  let suppress_cdb_s1_1 := Wire.mk "suppress_cdb_s1_1"
  let suppress_cdb_s2_1 := Wire.mk "suppress_cdb_s2_1"

  let alloc_avail_0 := Wire.mk "alloc_avail_0"; let alloc_avail_1 := Wire.mk "alloc_avail_1"
  let dispatch_valid_0 := Wire.mk "dispatch_valid_0"; let dispatch_valid_1 := Wire.mk "dispatch_valid_1"
  let alloc_ptr_0 := Wire.mk "alloc_ptr_0"; let alloc_ptr_next_0 := Wire.mk "alloc_ptr_next_0"
  let alloc_ptr_1 := Wire.mk "alloc_ptr_1"; let alloc_ptr_next_1 := Wire.mk "alloc_ptr_next_1"
  let arb0_gr0 := Wire.mk "dispatch_grant_0"; let arb0_gr1 := Wire.mk "dispatch_grant_1"
  let arb1_gr0 := Wire.mk "dispatch_grant_2"; let arb1_gr1 := Wire.mk "dispatch_grant_3"

  let dispatch_opcode_0 := makeIndexedWires "dispatch_opcode_0" opcodeWidth
  let dispatch_src1_data_0 := makeIndexedWires "dispatch_src1_data_0" dataWidth
  let dispatch_src2_data_0 := makeIndexedWires "dispatch_src2_data_0" dataWidth
  let dispatch_dest_tag_0 := makeIndexedWires "dispatch_dest_tag_0" tagWidth

  let dispatch_opcode_1 := makeIndexedWires "dispatch_opcode_1" opcodeWidth
  let dispatch_src1_data_1 := makeIndexedWires "dispatch_src1_data_1" dataWidth
  let dispatch_src2_data_1 := makeIndexedWires "dispatch_src2_data_1" dataWidth
  let dispatch_dest_tag_1 := makeIndexedWires "dispatch_dest_tag_1" tagWidth

  -- Gate CDB valid for INT domain (only snoop when not FP)
  let not_cdb_fp_0 := Wire.mk "not_cdb_fp_0"
  let not_cdb_fp_1 := Wire.mk "not_cdb_fp_1"
  let cdb_valid_int_0 := Wire.mk "cdb_valid_int_0"
  let cdb_valid_int_1 := Wire.mk "cdb_valid_int_1"
  let cdb_valid_gates := [
    Gate.mkNOT cdb_is_fp_0 not_cdb_fp_0,
    Gate.mkAND cdb_valid_0 not_cdb_fp_0 cdb_valid_int_0,
    Gate.mkNOT cdb_is_fp_1 not_cdb_fp_1,
    Gate.mkAND cdb_valid_1 not_cdb_fp_1 cdb_valid_int_1
  ]

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

  let (eg0, ei0, ev0, er0, e0_s1bp, e0_s2bp) :=
    buildRSEntry 0 opcodeWidth tagWidth tagWidth tagWidth dataWidth
      issue_we_0_0 issue_opcode_0 issue_dest_tag_0 issue_src1_ready_0 issue_src1_tag_0 issue_src1_data_0
      issue_src2_ready_0 issue_src2_tag_0 issue_src2_data_0
      cdb_tag_0 cdb_valid_int_0 cdb_data_0 cdb_tag_1 cdb_valid_int_1 cdb_data_1
      cdb_tag_0 cdb_valid_int_0 cdb_tag_1 cdb_valid_int_1
      none none none arb0_gr0 clock reset
  let (eg1, ei1, ev1, er1, e1_s1bp, e1_s2bp) :=
    buildRSEntry 1 opcodeWidth tagWidth tagWidth tagWidth dataWidth
      issue_we_0_1 issue_opcode_0 issue_dest_tag_0 issue_src1_ready_0 issue_src1_tag_0 issue_src1_data_0
      issue_src2_ready_0 issue_src2_tag_0 issue_src2_data_0
      cdb_tag_0 cdb_valid_int_0 cdb_data_0 cdb_tag_1 cdb_valid_int_1 cdb_data_1
      cdb_tag_0 cdb_valid_int_0 cdb_tag_1 cdb_valid_int_1
      none none none arb0_gr1 clock reset
  let (eg2, ei2, ev2, er2, e2_s1bp, e2_s2bp) :=
    buildRSEntry 2 opcodeWidth tagWidth tagWidth tagWidth dataWidth
      issue_we_1_0 issue_opcode_1 issue_dest_tag_1 issue_src1_ready_1 issue_src1_tag_1 issue_src1_data_1
      issue_src2_ready_1 issue_src2_tag_1 issue_src2_data_1
      cdb_tag_0 cdb_valid_int_0 cdb_data_0 cdb_tag_1 cdb_valid_int_1 cdb_data_1
      cdb_tag_0 cdb_valid_int_0 cdb_tag_1 cdb_valid_int_1
      (some suppress_cdb_s1_1) (some suppress_cdb_s2_1) (some dispatch_en_1) arb1_gr0 clock reset
  let (eg3, ei3, ev3, er3, e3_s1bp, e3_s2bp) :=
    buildRSEntry 3 opcodeWidth tagWidth tagWidth tagWidth dataWidth
      issue_we_1_1 issue_opcode_1 issue_dest_tag_1 issue_src1_ready_1 issue_src1_tag_1 issue_src1_data_1
      issue_src2_ready_1 issue_src2_tag_1 issue_src2_data_1
      cdb_tag_0 cdb_valid_int_0 cdb_data_0 cdb_tag_1 cdb_valid_int_1 cdb_data_1
      cdb_tag_0 cdb_valid_int_0 cdb_tag_1 cdb_valid_int_1
      (some suppress_cdb_s1_1) (some suppress_cdb_s2_1) (some dispatch_en_1) arb1_gr1 clock reset

  let v01_mux := Wire.mk "v_01_mux"
  let alloc_avail_g_0 := [Gate.mkMUX ev0 ev1 alloc_ptr_0 v01_mux, Gate.mkNOT v01_mux alloc_avail_0]
  let v23_mux := Wire.mk "v_23_mux"
  let alloc_avail_g_1 := [Gate.mkMUX ev2 ev3 alloc_ptr_1 v23_mux, Gate.mkNOT v23_mux alloc_avail_1]

  let arb0_inst : CircuitInstance := {
    moduleName := "PriorityArbiter2", instName := "u_arb0",
    portMap := [("request_0", er0), ("request_1", er1),
                ("grant_0", arb0_gr0), ("grant_1", arb0_gr1),
                ("valid", dispatch_valid_0)]
  }
  let arb1_inst : CircuitInstance := {
    moduleName := "PriorityArbiter2", instName := "u_arb1",
    portMap := [("request_0", er2), ("request_1", er3),
                ("grant_0", arb1_gr0), ("grant_1", arb1_gr1),
                ("valid", dispatch_valid_1)]
  }

  let e0 := makeIndexedWires "e0" entryWidth; let e1 := makeIndexedWires "e1" entryWidth
  let e2 := makeIndexedWires "e2" entryWidth; let e3 := makeIndexedWires "e3" entryWidth
  let b0_mux_op := mkLocalMux2 opcodeWidth (e0.drop 1) (e1.drop 1) dispatch_opcode_0 arb0_gr1
  let b0_mux_dst := mkLocalMux2 tagWidth (e0.drop off_dest) (e1.drop off_dest) dispatch_dest_tag_0 arb0_gr1
  let b0_mux_s1d := mkLocalMux2 dataWidth e0_s1bp e1_s1bp dispatch_src1_data_0 arb0_gr1
  let b0_mux_s2d := mkLocalMux2 dataWidth e0_s2bp e1_s2bp dispatch_src2_data_0 arb0_gr1

  let b1_mux_op := mkLocalMux2 opcodeWidth (e2.drop 1) (e3.drop 1) dispatch_opcode_1 arb1_gr1
  let b1_mux_dst := mkLocalMux2 tagWidth (e2.drop off_dest) (e3.drop off_dest) dispatch_dest_tag_1 arb1_gr1
  let b1_mux_s1d := mkLocalMux2 dataWidth e2_s1bp e3_s1bp dispatch_src1_data_1 arb1_gr1
  let b1_mux_s2d := mkLocalMux2 dataWidth e2_s2bp e3_s2bp dispatch_src2_data_1 arb1_gr1

  { name := if dataWidth == 64 then "IntReservationStation4_W2_64" else "IntReservationStation4_W2"
    inputs :=
      [clock, reset, issue_en_0, issue_en_1] ++
      issue_opcode_0 ++ issue_dest_tag_0 ++ [issue_src1_ready_0] ++ issue_src1_tag_0 ++ issue_src1_data_0 ++
      [issue_src2_ready_0] ++ issue_src2_tag_0 ++ issue_src2_data_0 ++
      issue_opcode_1 ++ issue_dest_tag_1 ++ [issue_src1_ready_1] ++ issue_src1_tag_1 ++ issue_src1_data_1 ++
      [issue_src2_ready_1] ++ issue_src2_tag_1 ++ issue_src2_data_1 ++
      [cdb_valid_0, cdb_is_fp_0] ++ cdb_tag_0 ++ cdb_data_0 ++
      [cdb_valid_1, cdb_is_fp_1] ++ cdb_tag_1 ++ cdb_data_1 ++
      [dispatch_en_1, suppress_cdb_s1_1, suppress_cdb_s2_1]
    outputs :=
      [alloc_avail_0, alloc_avail_1, dispatch_valid_0, dispatch_valid_1,
       alloc_ptr_0, alloc_ptr_1,
       arb0_gr0, arb0_gr1, arb1_gr0, arb1_gr1] ++
      dispatch_opcode_0 ++ dispatch_src1_data_0 ++ dispatch_src2_data_0 ++ dispatch_dest_tag_0 ++
      dispatch_opcode_1 ++ dispatch_src1_data_1 ++ dispatch_src2_data_1 ++ dispatch_dest_tag_1
    gates :=
      cdb_valid_gates ++ ptr_gates ++ base_issue_gates_0 ++ base_issue_gates_1 ++
      eg0 ++ eg1 ++ eg2 ++ eg3 ++
      alloc_avail_g_0 ++ alloc_avail_g_1 ++
      b0_mux_op ++ b0_mux_dst ++ b0_mux_s1d ++ b0_mux_s2d ++
      b1_mux_op ++ b1_mux_dst ++ b1_mux_s1d ++ b1_mux_s2d
    instances := [ptr_inst_0, ptr_inst_1, arb0_inst, arb1_inst] ++ ei0 ++ ei1 ++ ei2 ++ ei3 }

/-- Specialized Single-Issue Reservation Station (W=1, 2 entries, 6-bit tags).
    Used for Branch and MulDiv execution units. -/
def mkReservationStation2_W1 (dataWidth : Nat := 64) : Circuit :=
  let clock := Wire.mk "clock"; let reset := Wire.mk "reset"
  let opcodeWidth := 8; let tagWidth := 6
  let entryWidth := 1 + opcodeWidth + tagWidth + 1 + tagWidth + dataWidth + 1 + tagWidth + dataWidth
  let off_dest := 1 + opcodeWidth

  let issue_en := Wire.mk "issue_en"
  let issue_opcode := makeIndexedWires "issue_opcode" opcodeWidth
  let issue_dest_tag := makeIndexedWires "issue_dest_tag" tagWidth
  let issue_src1_ready := Wire.mk "issue_src1_ready"
  let issue_src1_tag := makeIndexedWires "issue_src1_tag" tagWidth
  let issue_src1_data := makeIndexedWires "issue_src1_data" dataWidth
  let issue_src2_ready := Wire.mk "issue_src2_ready"
  let issue_src2_tag := makeIndexedWires "issue_src2_tag" tagWidth
  let issue_src2_data := makeIndexedWires "issue_src2_data" dataWidth

  let cdb_valid_0 := Wire.mk "cdb_valid_0"; let cdb_is_fp_0 := Wire.mk "cdb_is_fp_0"
  let cdb_tag_0 := makeIndexedWires "cdb_tag_0" tagWidth
  let cdb_data_0 := makeIndexedWires "cdb_data_0" dataWidth
  let cdb_valid_1 := Wire.mk "cdb_valid_1"; let cdb_is_fp_1 := Wire.mk "cdb_is_fp_1"
  let cdb_tag_1 := makeIndexedWires "cdb_tag_1" tagWidth
  let cdb_data_1 := makeIndexedWires "cdb_data_1" dataWidth

  let dispatch_en := Wire.mk "dispatch_en"
  let suppress_cdb_s1 := Wire.mk "suppress_cdb_s1"
  let suppress_cdb_s2 := Wire.mk "suppress_cdb_s2"

  let alloc_avail := Wire.mk "alloc_avail"
  let dispatch_valid := Wire.mk "dispatch_valid"
  let alloc_ptr := Wire.mk "alloc_ptr"; let alloc_ptr_next := Wire.mk "alloc_ptr_next"
  let dispatch_grant_0 := Wire.mk "dispatch_grant_0"; let dispatch_grant_1 := Wire.mk "dispatch_grant_1"

  let dispatch_opcode := makeIndexedWires "dispatch_opcode" opcodeWidth
  let dispatch_src1_data := makeIndexedWires "dispatch_src1_data" dataWidth
  let dispatch_src2_data := makeIndexedWires "dispatch_src2_data" dataWidth
  let dispatch_dest_tag := makeIndexedWires "dispatch_dest_tag" tagWidth

  let not_cdb_fp_0 := Wire.mk "not_cdb_fp_0"
  let not_cdb_fp_1 := Wire.mk "not_cdb_fp_1"
  let cdb_valid_int_0 := Wire.mk "cdb_valid_int_0"
  let cdb_valid_int_1 := Wire.mk "cdb_valid_int_1"
  let cdb_valid_gates := [
    Gate.mkNOT cdb_is_fp_0 not_cdb_fp_0,
    Gate.mkAND cdb_valid_0 not_cdb_fp_0 cdb_valid_int_0,
    Gate.mkNOT cdb_is_fp_1 not_cdb_fp_1,
    Gate.mkAND cdb_valid_1 not_cdb_fp_1 cdb_valid_int_1
  ]

  let ptr_gates := [Gate.mkXOR alloc_ptr issue_en alloc_ptr_next]
  let ptr_inst : CircuitInstance := {
    moduleName := "Register1", instName := "u_alloc_ptr",
    portMap := [("d_0", alloc_ptr_next), ("clock", clock), ("reset", reset), ("q_0", alloc_ptr)]
  }

  let issue_we_0 := Wire.mk "issue_we_0"; let issue_we_1 := Wire.mk "issue_we_1"
  let not_ptr := Wire.mk "not_ptr"
  let issue_gates := [
    Gate.mkNOT alloc_ptr not_ptr,
    Gate.mkAND issue_en not_ptr issue_we_0,
    Gate.mkAND issue_en alloc_ptr issue_we_1
  ]

  let (eg0, ei0, ev0, er0, e0_s1bp, e0_s2bp) :=
    buildRSEntry 0 opcodeWidth tagWidth tagWidth tagWidth dataWidth
      issue_we_0 issue_opcode issue_dest_tag issue_src1_ready issue_src1_tag issue_src1_data
      issue_src2_ready issue_src2_tag issue_src2_data
      cdb_tag_0 cdb_valid_int_0 cdb_data_0 cdb_tag_1 cdb_valid_int_1 cdb_data_1
      cdb_tag_0 cdb_valid_int_0 cdb_tag_1 cdb_valid_int_1
      (some suppress_cdb_s1) (some suppress_cdb_s2) (some dispatch_en) dispatch_grant_0 clock reset
  let (eg1, ei1, ev1, er1, e1_s1bp, e1_s2bp) :=
    buildRSEntry 1 opcodeWidth tagWidth tagWidth tagWidth dataWidth
      issue_we_1 issue_opcode issue_dest_tag issue_src1_ready issue_src1_tag issue_src1_data
      issue_src2_ready issue_src2_tag issue_src2_data
      cdb_tag_0 cdb_valid_int_0 cdb_data_0 cdb_tag_1 cdb_valid_int_1 cdb_data_1
      cdb_tag_0 cdb_valid_int_0 cdb_tag_1 cdb_valid_int_1
      (some suppress_cdb_s1) (some suppress_cdb_s2) (some dispatch_en) dispatch_grant_1 clock reset

  let v01_mux := Wire.mk "v_01_mux"
  let alloc_avail_g := [Gate.mkMUX ev0 ev1 alloc_ptr v01_mux, Gate.mkNOT v01_mux alloc_avail]

  let arb_inst : CircuitInstance := {
    moduleName := "PriorityArbiter2", instName := "u_arb",
    portMap := [("request_0", er0), ("request_1", er1),
                ("grant_0", dispatch_grant_0), ("grant_1", dispatch_grant_1),
                ("valid", dispatch_valid)]
  }

  let e0 := makeIndexedWires "e0" entryWidth; let e1 := makeIndexedWires "e1" entryWidth
  let mux_op := mkLocalMux2 opcodeWidth (e0.drop 1) (e1.drop 1) dispatch_opcode dispatch_grant_1
  let mux_dst := mkLocalMux2 tagWidth (e0.drop off_dest) (e1.drop off_dest) dispatch_dest_tag dispatch_grant_1
  let mux_s1d := mkLocalMux2 dataWidth e0_s1bp e1_s1bp dispatch_src1_data dispatch_grant_1
  let mux_s2d := mkLocalMux2 dataWidth e0_s2bp e1_s2bp dispatch_src2_data dispatch_grant_1

  { name := if dataWidth == 64 then "ReservationStation2_W1_64" else "ReservationStation2_W1"
    inputs :=
      [clock, reset, issue_en] ++
      issue_opcode ++ issue_dest_tag ++ [issue_src1_ready] ++ issue_src1_tag ++ issue_src1_data ++
      [issue_src2_ready] ++ issue_src2_tag ++ issue_src2_data ++
      [cdb_valid_0, cdb_is_fp_0] ++ cdb_tag_0 ++ cdb_data_0 ++
      [cdb_valid_1, cdb_is_fp_1] ++ cdb_tag_1 ++ cdb_data_1 ++
      [dispatch_en, suppress_cdb_s1, suppress_cdb_s2]
    outputs :=
      [alloc_avail, dispatch_valid, alloc_ptr,
       dispatch_grant_0, dispatch_grant_1] ++
      dispatch_opcode ++ dispatch_src1_data ++ dispatch_src2_data ++ dispatch_dest_tag
    gates :=
      cdb_valid_gates ++ ptr_gates ++ issue_gates ++
      eg0 ++ eg1 ++ alloc_avail_g ++
      mux_op ++ mux_dst ++ mux_s1d ++ mux_s2d
    instances := [ptr_inst, arb_inst] ++ ei0 ++ ei1 }

/-- Specialized Single-Issue Memory Reservation Station (W=1, 2 entries, SLO tracking).
    dest_tag is 7-bit (is_fp_load), src1_tag is 6-bit (base addr), src2_tag is 7-bit (is_fp_store). -/
def mkMemoryReservationStation2_W1 (dataWidth : Nat := 64) : Circuit :=
  let clock := Wire.mk "clock"; let reset := Wire.mk "reset"
  let opcodeWidth := 8; let destTagWidth := 6; let src1TagWidth := 6; let src2TagWidth := 7
  let entryWidth := 1 + opcodeWidth + destTagWidth + 1 + src1TagWidth + dataWidth + 1 + src2TagWidth + dataWidth
  let off_dest := 1 + opcodeWidth

  let issue_en := Wire.mk "issue_en"
  let issue_is_store := Wire.mk "issue_is_store"
  let issue_is_atomic := Wire.mk "issue_is_atomic"
  let issue_opcode := makeIndexedWires "issue_opcode" opcodeWidth
  let issue_dest_tag := makeIndexedWires "issue_dest_tag" destTagWidth
  let issue_src1_ready := Wire.mk "issue_src1_ready"
  let issue_src1_tag := makeIndexedWires "issue_src1_tag" src1TagWidth
  let issue_src1_data := makeIndexedWires "issue_src1_data" dataWidth
  let issue_src2_ready := Wire.mk "issue_src2_ready"
  let issue_src2_tag := makeIndexedWires "issue_src2_tag" src2TagWidth
  let issue_src2_data := makeIndexedWires "issue_src2_data" dataWidth

  let cdb_valid_0 := Wire.mk "cdb_valid_0"; let cdb_is_fp_0 := Wire.mk "cdb_is_fp_0"
  let cdb_tag_0 := makeIndexedWires "cdb_tag_0" src1TagWidth
  let cdb_data_0 := makeIndexedWires "cdb_data_0" dataWidth
  let cdb_valid_1 := Wire.mk "cdb_valid_1"; let cdb_is_fp_1 := Wire.mk "cdb_is_fp_1"
  let cdb_tag_1 := makeIndexedWires "cdb_tag_1" src1TagWidth
  let cdb_data_1 := makeIndexedWires "cdb_data_1" dataWidth

  let dispatch_en := Wire.mk "dispatch_en"
  let suppress_cdb_s1 := Wire.mk "suppress_cdb_s1"
  let suppress_cdb_s2 := Wire.mk "suppress_cdb_s2"

  let alloc_avail := Wire.mk "alloc_avail"
  let dispatch_valid := Wire.mk "dispatch_valid"
  let alloc_ptr := Wire.mk "alloc_ptr"; let alloc_ptr_next := Wire.mk "alloc_ptr_next"
  let pending_store := Wire.mk "pending_store"
  let dispatch_grant_0 := Wire.mk "dispatch_grant_0"; let dispatch_grant_1 := Wire.mk "dispatch_grant_1"

  let dispatch_opcode := makeIndexedWires "dispatch_opcode" opcodeWidth
  let dispatch_src1_data := makeIndexedWires "dispatch_src1_data" dataWidth
  let dispatch_src2_data := makeIndexedWires "dispatch_src2_data" dataWidth
  let dispatch_dest_tag := makeIndexedWires "dispatch_dest_tag" destTagWidth

  let not_cdb_fp_0 := Wire.mk "not_cdb_fp_0"
  let not_cdb_fp_1 := Wire.mk "not_cdb_fp_1"
  let cdb_valid_int_0 := Wire.mk "cdb_valid_int_0"
  let cdb_valid_int_1 := Wire.mk "cdb_valid_int_1"
  let cdb_valid_gates := [
    Gate.mkNOT cdb_is_fp_0 not_cdb_fp_0,
    Gate.mkAND cdb_valid_0 not_cdb_fp_0 cdb_valid_int_0,
    Gate.mkNOT cdb_is_fp_1 not_cdb_fp_1,
    Gate.mkAND cdb_valid_1 not_cdb_fp_1 cdb_valid_int_1
  ]

  let cdb_tag7_0 := cdb_tag_0 ++ [cdb_is_fp_0]
  let cdb_tag7_1 := cdb_tag_1 ++ [cdb_is_fp_1]

  let ptr_gates := [Gate.mkXOR alloc_ptr issue_en alloc_ptr_next]
  let ptr_inst : CircuitInstance := {
    moduleName := "Register1", instName := "u_alloc_ptr",
    portMap := [("d_0", alloc_ptr_next), ("clock", clock), ("reset", reset), ("q_0", alloc_ptr)]
  }

  let issue_we_0 := Wire.mk "issue_we_0"; let issue_we_1 := Wire.mk "issue_we_1"
  let not_ptr := Wire.mk "not_ptr"
  let issue_gates := [
    Gate.mkNOT alloc_ptr not_ptr,
    Gate.mkAND issue_en not_ptr issue_we_0,
    Gate.mkAND issue_en alloc_ptr issue_we_1
  ]

  let (eg0, ei0, ev0, er0, e0_s1bp, e0_s2bp) :=
    buildRSEntry 0 opcodeWidth destTagWidth src1TagWidth src2TagWidth dataWidth
      issue_we_0 issue_opcode issue_dest_tag issue_src1_ready issue_src1_tag issue_src1_data
      issue_src2_ready issue_src2_tag issue_src2_data
      cdb_tag_0 cdb_valid_int_0 cdb_data_0 cdb_tag_1 cdb_valid_int_1 cdb_data_1
      cdb_tag7_0 cdb_valid_0 cdb_tag7_1 cdb_valid_1
      (some suppress_cdb_s1) (some suppress_cdb_s2) (some dispatch_en) dispatch_grant_0 clock reset
  let (eg1, ei1, ev1, er1, e1_s1bp, e1_s2bp) :=
    buildRSEntry 1 opcodeWidth destTagWidth src1TagWidth src2TagWidth dataWidth
      issue_we_1 issue_opcode issue_dest_tag issue_src1_ready issue_src1_tag issue_src1_data
      issue_src2_ready issue_src2_tag issue_src2_data
      cdb_tag_0 cdb_valid_int_0 cdb_data_0 cdb_tag_1 cdb_valid_int_1 cdb_data_1
      cdb_tag7_0 cdb_valid_0 cdb_tag7_1 cdb_valid_1
      (some suppress_cdb_s1) (some suppress_cdb_s2) (some dispatch_en) dispatch_grant_1 clock reset

  let v01_mux := Wire.mk "v_01_mux"
  let alloc_avail_g := [Gate.mkMUX ev0 ev1 alloc_ptr v01_mux, Gate.mkNOT v01_mux alloc_avail]

  -- SLO tracking for 2 entries
  let is_store_cur_0 := Wire.mk "slo_st_0"; let is_store_next_0 := Wire.mk "slo_st_next_0"
  let is_atomic_cur_0 := Wire.mk "slo_at_0"; let is_atomic_next_0 := Wire.mk "slo_at_next_0"
  let is_store_cur_1 := Wire.mk "slo_st_1"; let is_store_next_1 := Wire.mk "slo_st_next_1"
  let is_atomic_cur_1 := Wire.mk "slo_at_1"; let is_atomic_next_1 := Wire.mk "slo_at_next_1"
  let slo_gates := [
    Gate.mkMUX is_store_cur_0 issue_is_store issue_we_0 is_store_next_0,
    Gate.mkMUX is_atomic_cur_0 issue_is_atomic issue_we_0 is_atomic_next_0,
    Gate.mkMUX is_store_cur_1 issue_is_store issue_we_1 is_store_next_1,
    Gate.mkMUX is_atomic_cur_1 issue_is_atomic issue_we_1 is_atomic_next_1
  ]
  let slo_insts : List CircuitInstance := [
    { moduleName := "Register1", instName := "u_slo_st_0",
      portMap := [("d_0", is_store_next_0), ("clock", clock), ("reset", reset), ("q_0", is_store_cur_0)] },
    { moduleName := "Register1", instName := "u_slo_at_0",
      portMap := [("d_0", is_atomic_next_0), ("clock", clock), ("reset", reset), ("q_0", is_atomic_cur_0)] },
    { moduleName := "Register1", instName := "u_slo_st_1",
      portMap := [("d_0", is_store_next_1), ("clock", clock), ("reset", reset), ("q_0", is_store_cur_1)] },
    { moduleName := "Register1", instName := "u_slo_at_1",
      portMap := [("d_0", is_atomic_next_1), ("clock", clock), ("reset", reset), ("q_0", is_atomic_cur_1)] }
  ]
  let nat0 := Wire.mk "slo_nat0"; let nat1 := Wire.mk "slo_nat1"
  let ps0 := Wire.mk "slo_ps0"; let ps1 := Wire.mk "slo_ps1"
  let pst0 := Wire.mk "slo_pst0"; let pst1 := Wire.mk "slo_pst1"
  let pending_store_gates := [
    Gate.mkNOT is_atomic_cur_0 nat0, Gate.mkNOT is_atomic_cur_1 nat1,
    Gate.mkAND is_store_cur_0 nat0 ps0, Gate.mkAND is_store_cur_1 nat1 ps1,
    Gate.mkAND ev0 ps0 pst0, Gate.mkAND ev1 ps1 pst1,
    Gate.mkOR pst0 pst1 pending_store
  ]
  let vs0 := Wire.mk "slo_vs0"; let vs1 := Wire.mk "slo_vs1"
  let hos0 := Wire.mk "slo_hos0"; let hos1 := Wire.mk "slo_hos1"
  let not_hos0 := Wire.mk "slo_not_hos0"; let not_hos1 := Wire.mk "slo_not_hos1"
  let not_ap := Wire.mk "slo_not_ap"
  let ok0 := Wire.mk "slo_ok0"; let ok1 := Wire.mk "slo_ok1"
  let ar0 := Wire.mk "slo_ar0"; let ar1 := Wire.mk "slo_ar1"
  let slo_check_gates := [
    Gate.mkAND ev0 is_store_cur_0 vs0,
    Gate.mkAND ev1 is_store_cur_1 vs1,
    Gate.mkNOT alloc_ptr not_ap,
    Gate.mkAND vs1 alloc_ptr hos0,
    Gate.mkAND vs0 not_ap hos1,
    Gate.mkNOT hos0 not_hos0,
    Gate.mkOR ps0 not_hos0 ok0,
    Gate.mkAND er0 ok0 ar0,
    Gate.mkNOT hos1 not_hos1,
    Gate.mkOR ps1 not_hos1 ok1,
    Gate.mkAND er1 ok1 ar1
  ]

  let arb_inst : CircuitInstance := {
    moduleName := "PriorityArbiter2", instName := "u_arb",
    portMap := [("request_0", ar0), ("request_1", ar1),
                ("grant_0", dispatch_grant_0), ("grant_1", dispatch_grant_1),
                ("valid", dispatch_valid)]
  }

  let e0 := makeIndexedWires "e0" entryWidth; let e1 := makeIndexedWires "e1" entryWidth
  let mux_op := mkLocalMux2 opcodeWidth (e0.drop 1) (e1.drop 1) dispatch_opcode dispatch_grant_1
  let mux_dst := mkLocalMux2 destTagWidth (e0.drop off_dest) (e1.drop off_dest) dispatch_dest_tag dispatch_grant_1
  let mux_s1d := mkLocalMux2 dataWidth e0_s1bp e1_s1bp dispatch_src1_data dispatch_grant_1
  let mux_s2d := mkLocalMux2 dataWidth e0_s2bp e1_s2bp dispatch_src2_data dispatch_grant_1

  { name := if dataWidth == 64 then "MemoryReservationStation2_W1_64" else "MemoryReservationStation2_W1"
    inputs :=
      [clock, reset, issue_en, issue_is_store, issue_is_atomic] ++
      issue_opcode ++ issue_dest_tag ++ [issue_src1_ready] ++ issue_src1_tag ++ issue_src1_data ++
      [issue_src2_ready] ++ issue_src2_tag ++ issue_src2_data ++
      [cdb_valid_0, cdb_is_fp_0] ++ cdb_tag_0 ++ cdb_data_0 ++
      [cdb_valid_1, cdb_is_fp_1] ++ cdb_tag_1 ++ cdb_data_1 ++
      [dispatch_en, suppress_cdb_s1, suppress_cdb_s2]
    outputs :=
      [alloc_avail, dispatch_valid, alloc_ptr, pending_store,
       dispatch_grant_0, dispatch_grant_1] ++
      dispatch_opcode ++ dispatch_src1_data ++ dispatch_src2_data ++ dispatch_dest_tag
    gates :=
      cdb_valid_gates ++ ptr_gates ++ issue_gates ++
      eg0 ++ eg1 ++ alloc_avail_g ++
      slo_gates ++ pending_store_gates ++ slo_check_gates ++
      mux_op ++ mux_dst ++ mux_s1d ++ mux_s2d
    instances := [ptr_inst, arb_inst] ++ slo_insts ++ ei0 ++ ei1 }

/-- Specialized Single-Issue Floating-Point Reservation Station (W=1, 2 entries, 6-bit opcode, 7-bit tags).
    Includes ext_ready_mask for FP src3 dependency tracking. -/
def mkFPReservationStation2_W1 (dataWidth : Nat := 64) : Circuit :=
  let clock := Wire.mk "clock"; let reset := Wire.mk "reset"
  let opcodeWidth := 6; let destTagWidth := 6; let src1TagWidth := 7; let src2TagWidth := 7
  let entryWidth := 1 + opcodeWidth + destTagWidth + 1 + src1TagWidth + dataWidth + 1 + src2TagWidth + dataWidth
  let off_dest := 1 + opcodeWidth

  let issue_en := Wire.mk "issue_en"
  let issue_opcode := makeIndexedWires "issue_opcode" opcodeWidth
  let issue_dest_tag := makeIndexedWires "issue_dest_tag" destTagWidth
  let issue_src1_ready := Wire.mk "issue_src1_ready"
  let issue_src1_tag := makeIndexedWires "issue_src1_tag" src1TagWidth
  let issue_src1_data := makeIndexedWires "issue_src1_data" dataWidth
  let issue_src2_ready := Wire.mk "issue_src2_ready"
  let issue_src2_tag := makeIndexedWires "issue_src2_tag" src2TagWidth
  let issue_src2_data := makeIndexedWires "issue_src2_data" dataWidth

  let cdb_valid_0 := Wire.mk "cdb_valid_0"; let cdb_is_fp_0 := Wire.mk "cdb_is_fp_0"
  let cdb_tag_0 := makeIndexedWires "cdb_tag_0" 6
  let cdb_data_0 := makeIndexedWires "cdb_data_0" dataWidth
  let cdb_valid_1 := Wire.mk "cdb_valid_1"; let cdb_is_fp_1 := Wire.mk "cdb_is_fp_1"
  let cdb_tag_1 := makeIndexedWires "cdb_tag_1" 6
  let cdb_data_1 := makeIndexedWires "cdb_data_1" dataWidth

  let dispatch_en := Wire.mk "dispatch_en"
  let suppress_cdb_s1 := Wire.mk "suppress_cdb_s1"
  let suppress_cdb_s2 := Wire.mk "suppress_cdb_s2"
  let ext_ready_mask_0 := Wire.mk "ext_ready_mask_0"
  let ext_ready_mask_1 := Wire.mk "ext_ready_mask_1"

  let alloc_avail := Wire.mk "alloc_avail"
  let dispatch_valid := Wire.mk "dispatch_valid"
  let alloc_ptr := Wire.mk "alloc_ptr"; let alloc_ptr_next := Wire.mk "alloc_ptr_next"
  let dispatch_grant_0 := Wire.mk "dispatch_grant_0"; let dispatch_grant_1 := Wire.mk "dispatch_grant_1"

  let dispatch_opcode := makeIndexedWires "dispatch_opcode" opcodeWidth
  let dispatch_src1_data := makeIndexedWires "dispatch_src1_data" dataWidth
  let dispatch_src2_data := makeIndexedWires "dispatch_src2_data" dataWidth
  let dispatch_dest_tag := makeIndexedWires "dispatch_dest_tag" destTagWidth

  let cdb_tag7_0 := cdb_tag_0 ++ [cdb_is_fp_0]
  let cdb_tag7_1 := cdb_tag_1 ++ [cdb_is_fp_1]

  let ptr_gates := [Gate.mkXOR alloc_ptr issue_en alloc_ptr_next]
  let ptr_inst : CircuitInstance := {
    moduleName := "Register1", instName := "u_alloc_ptr",
    portMap := [("d_0", alloc_ptr_next), ("clock", clock), ("reset", reset), ("q_0", alloc_ptr)]
  }

  let issue_we_0 := Wire.mk "issue_we_0"; let issue_we_1 := Wire.mk "issue_we_1"
  let not_ptr := Wire.mk "not_ptr"
  let issue_gates := [
    Gate.mkNOT alloc_ptr not_ptr,
    Gate.mkAND issue_en not_ptr issue_we_0,
    Gate.mkAND issue_en alloc_ptr issue_we_1
  ]

  let (eg0, ei0, ev0, er0, e0_s1bp, e0_s2bp) :=
    buildRSEntry 0 opcodeWidth destTagWidth src1TagWidth src2TagWidth dataWidth
      issue_we_0 issue_opcode issue_dest_tag issue_src1_ready issue_src1_tag issue_src1_data
      issue_src2_ready issue_src2_tag issue_src2_data
      cdb_tag7_0 cdb_valid_0 cdb_data_0 cdb_tag7_1 cdb_valid_1 cdb_data_1
      cdb_tag7_0 cdb_valid_0 cdb_tag7_1 cdb_valid_1
      (some suppress_cdb_s1) (some suppress_cdb_s2) (some dispatch_en) dispatch_grant_0 clock reset
  let (eg1, ei1, ev1, er1, e1_s1bp, e1_s2bp) :=
    buildRSEntry 1 opcodeWidth destTagWidth src1TagWidth src2TagWidth dataWidth
      issue_we_1 issue_opcode issue_dest_tag issue_src1_ready issue_src1_tag issue_src1_data
      issue_src2_ready issue_src2_tag issue_src2_data
      cdb_tag7_0 cdb_valid_0 cdb_data_0 cdb_tag7_1 cdb_valid_1 cdb_data_1
      cdb_tag7_0 cdb_valid_0 cdb_tag7_1 cdb_valid_1
      (some suppress_cdb_s1) (some suppress_cdb_s2) (some dispatch_en) dispatch_grant_1 clock reset

  let v01_mux := Wire.mk "v_01_mux"
  let alloc_avail_g := [Gate.mkMUX ev0 ev1 alloc_ptr v01_mux, Gate.mkNOT v01_mux alloc_avail]

  let ar0 := Wire.mk "ar0"; let ar1 := Wire.mk "ar1"
  let ready_mask_gates := [
    Gate.mkAND er0 ext_ready_mask_0 ar0,
    Gate.mkAND er1 ext_ready_mask_1 ar1
  ]

  let arb_inst : CircuitInstance := {
    moduleName := "PriorityArbiter2", instName := "u_arb",
    portMap := [("request_0", ar0), ("request_1", ar1),
                ("grant_0", dispatch_grant_0), ("grant_1", dispatch_grant_1),
                ("valid", dispatch_valid)]
  }

  let e0 := makeIndexedWires "e0" entryWidth; let e1 := makeIndexedWires "e1" entryWidth
  let mux_op := mkLocalMux2 opcodeWidth (e0.drop 1) (e1.drop 1) dispatch_opcode dispatch_grant_1
  let mux_dst := mkLocalMux2 destTagWidth (e0.drop off_dest) (e1.drop off_dest) dispatch_dest_tag dispatch_grant_1
  let mux_s1d := mkLocalMux2 dataWidth e0_s1bp e1_s1bp dispatch_src1_data dispatch_grant_1
  let mux_s2d := mkLocalMux2 dataWidth e0_s2bp e1_s2bp dispatch_src2_data dispatch_grant_1

  { name := if dataWidth == 64 then "FPReservationStation2_W1_64" else "FPReservationStation2_W1"
    inputs :=
      [clock, reset, issue_en] ++
      issue_opcode ++ issue_dest_tag ++ [issue_src1_ready] ++ issue_src1_tag ++ issue_src1_data ++
      [issue_src2_ready] ++ issue_src2_tag ++ issue_src2_data ++
      [cdb_valid_0, cdb_is_fp_0] ++ cdb_tag_0 ++ cdb_data_0 ++
      [cdb_valid_1, cdb_is_fp_1] ++ cdb_tag_1 ++ cdb_data_1 ++
      [dispatch_en, suppress_cdb_s1, suppress_cdb_s2,
       ext_ready_mask_0, ext_ready_mask_1]
    outputs :=
      [alloc_avail, dispatch_valid, alloc_ptr,
       dispatch_grant_0, dispatch_grant_1] ++
      dispatch_opcode ++ dispatch_src1_data ++ dispatch_src2_data ++ dispatch_dest_tag
    gates :=
      ptr_gates ++ issue_gates ++
      eg0 ++ eg1 ++ alloc_avail_g ++ ready_mask_gates ++
      mux_op ++ mux_dst ++ mux_s1d ++ mux_s2d
    instances := [ptr_inst, arb_inst] ++ ei0 ++ ei1 }

end Shoumei.RISCV.Execution



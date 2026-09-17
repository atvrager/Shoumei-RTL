/-
Circuits/Combinational/Arbiter.lean - Priority Arbiter

Implements fixed-priority arbitration for resource allocation.
Used in RS ready selection, CDB arbitration, issue logic, etc.

Design:
- N request inputs (request[n-1:0])
- N grant outputs (one-hot encoding, grant[n-1:0])
- 1 valid output (any request present)

Priority: Lower index = higher priority
- If request[0] = true, grant[0] = true (all others = false)
- If request[0] = false and request[1] = true, grant[1] = true
- And so on...

Properties:
- One-hot grant: At most one grant bit is high
- Priority ordering: Grant goes to lowest index request
- Valid correctness: valid = OR(all requests)
-/

import Shoumei.DSL
import Shoumei.Semantics

namespace Shoumei.Circuits.Combinational

open Shoumei

/-! ## Behavioral Model -/

/-- Priority arbiter state: just the grant decision

    Given n requests, returns:
    - grants: one-hot encoded grant (at most one bit set)
    - valid: true if any request is present
-/
structure ArbiterResult (n : Nat) where
  /-- One-hot grant vector (at most one bit set) -/
  grants : Fin n → Bool
  /-- Valid flag (true if any request granted) -/
  valid : Bool

namespace ArbiterResult

/-- Fixed priority arbitration logic (behavioral).

    Scans requests from index 0 to n-1, grants to first true request.
    Returns one-hot grant vector and valid flag.
-/
def priorityArbitrate (n : Nat) (requests : Fin n → Bool) : ArbiterResult n :=
  -- Find first request (lowest index)
  let firstReq := (List.range n).findIdx? (fun i =>
    if h : i < n then
      requests ⟨i, h⟩
    else
      false)

  match firstReq with
  | none =>
      -- No requests, all grants false
      { grants := fun _ => false
        valid := false }
  | some idx =>
      -- Grant to first request (one-hot)
      if _ : idx < n then
        { grants := fun i => i.val == idx
          valid := true }
      else
        { grants := fun _ => false
          valid := false }

end ArbiterResult

/-! ## Structural Circuit -/

/-- Helper: Create indexed wires -/
private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

/-- Build a fixed-priority arbiter circuit.

    Parameters:
    - n: Number of request inputs (and grant outputs)

    Ports:
    - Inputs: request[n-1:0]
    - Outputs: grant[n-1:0], valid

    Architecture:
    - Priority chain: Each position checks if all higher priorities are inactive
    - Grant[i] = request[i] AND NOT(request[0]) AND NOT(request[1]) ... AND NOT(request[i-1])
    - Valid = OR(all requests)

    Example for n=4:
    - grant[0] = request[0]
    - grant[1] = request[1] AND NOT(request[0])
    - grant[2] = request[2] AND NOT(request[0]) AND NOT(request[1])
    - grant[3] = request[3] AND NOT(request[0]) AND NOT(request[1]) AND NOT(request[2])
    - valid = request[0] OR request[1] OR request[2] OR request[3]

    Gate count: ~n² for AND chain + n for OR tree = O(n²)
-/
def mkPriorityArbiter (n : Nat) : Circuit :=
  if n == 0 then
    -- Degenerate case: no requests
    { name := "PriorityArbiter0"
      inputs := []
      outputs := [Wire.mk "valid"]
      gates := [Gate.mkNOT (Wire.mk "valid") (Wire.mk "valid")]  -- valid = false (dummy)
      instances := []
    }
  else
    let request := makeIndexedWires "request" n
    let grant := makeIndexedWires "grant" n
    let valid := Wire.mk "valid"

    -- Internal: NOT of each request (for masking)
    let request_n := makeIndexedWires "request_n" n
    let not_gates := List.zipWith (fun req req_n =>
      Gate.mkNOT req req_n
    ) request request_n

    -- Grant logic: grant[i] = request[i] AND (AND of all request_n[j] for j < i)
    -- Build iteratively for each position
    let grant_gates := (List.range n).foldl (fun acc i =>
      if i == 0 then
        -- grant[0] = request[0] (highest priority, no mask)
        acc ++ [Gate.mkBUF request[i]! grant[i]!]
      else
        -- Build AND chain: mask = request_n[0] AND request_n[1] AND ... AND request_n[i-1]
        -- Use iterative chaining
        let maskChain := (List.range i).foldl (fun (gates, prevWire) j =>
          if j == 0 then
            -- First element: no gate needed yet
            (gates, request_n[0]!)
          else
            let maskWire := Wire.mk s!"mask_{i}_{j}"
            let andGate := Gate.mkAND prevWire request_n[j]! maskWire
            (gates ++ [andGate], maskWire)
        ) ([], request_n[0]!)

        let (maskGates, finalMask) := maskChain
        -- grant[i] = finalMask AND request[i]
        let grantGate := Gate.mkAND finalMask request[i]! grant[i]!
        acc ++ maskGates ++ [grantGate]
    ) []

    -- Valid logic: OR chain of all requests
    -- valid = request[0] OR request[1] OR ... OR request[n-1]
    let validGates :=
      if n == 1 then
        [Gate.mkBUF request[0]! valid]
      else if n == 2 then
        [Gate.mkOR request[0]! request[1]! valid]
      else
        -- Build linear OR chain: or_0 = req[0] OR req[1], or_1 = or_0 OR req[2], ...
        let (gates, _) := (List.range (n - 1)).foldl (fun (gates, prevWire) i =>
          let nextReq := request[i + 1]!
          let orWire := if i == n - 2 then valid else Wire.mk s!"or_chain_{i}"
          let orGate := Gate.mkOR prevWire nextReq orWire
          (gates ++ [orGate], orWire)
        ) ([], request[0]!)
        gates

    { name := s!"PriorityArbiter{n}"
      inputs := request
      outputs := grant ++ [valid]
      gates := not_gates ++ grant_gates ++ validGates
      instances := []
      -- V2 codegen annotations
      signalGroups := [
        { name := "request", width := n, wires := request },
        { name := "grant", width := n, wires := grant },
        { name := "request_n", width := n, wires := request_n }
      ]
    }

/-! ## Common Configurations -/

/-- 2-input arbiter (for dual-port arbitration) -/
def mkPriorityArbiter2 : Circuit := mkPriorityArbiter 2

/-- 4-input arbiter (for RS4 ready selection) -/
def mkPriorityArbiter4 : Circuit := mkPriorityArbiter 4

/-- 8-input arbiter (for RS8 ready selection) -/
def mkPriorityArbiter8 : Circuit := mkPriorityArbiter 8

/-- 64-input hierarchical priority arbiter (for bitmap free list allocation).
    Decomposed into a 2-level 8-way tree using 9 instances of PriorityArbiter8:
    - Level 1: 8 instances of PriorityArbiter8 (u_sub_0 .. u_sub_7),
      each arbitrating 8 request bits, producing an 8-bit sub-grant and group_valid.
    - Level 2: 1 instance of PriorityArbiter8 (u_top),
      arbitrating across the 8 group_valid signals, producing group_grant and top-level valid.
    - Output grant: grant[8*i + j] = sub_grant[8*i + j] AND group_grant[i].
    Reduces gate count from 2,144 flat gates to 64 AND gates + 9 instances,
    eliminating 2,016 raw mask wires and reducing emitted SV from 4,052 lines to ~90 lines. -/
def mkPriorityArbiter64Hierarchical : Circuit :=
  let request := makeIndexedWires "request" 64
  let grant := makeIndexedWires "grant" 64
  let valid := Wire.mk "valid"
  let group_valid := makeIndexedWires "group_valid" 8
  let group_grant := makeIndexedWires "group_grant" 8
  let sub_grant := makeIndexedWires "sub_grant" 64

  -- 8 Level-1 PriorityArbiter8 instances
  let subInstances := (List.range 8).map fun i =>
    let portMap :=
      ((List.range 8).map fun j => (s!"request_{j}", request[8 * i + j]!)) ++
      ((List.range 8).map fun j => (s!"grant_{j}", sub_grant[8 * i + j]!)) ++
      [("valid", group_valid[i]!)]
    { moduleName := "PriorityArbiter8"
      instName := s!"u_sub_{i}"
      portMap := portMap }

  -- 1 Level-2 PriorityArbiter8 instance
  let topInstance : CircuitInstance := {
    moduleName := "PriorityArbiter8"
    instName := "u_top"
    portMap :=
      ((List.range 8).map fun i => (s!"request_{i}", group_valid[i]!)) ++
      ((List.range 8).map fun i => (s!"grant_{i}", group_grant[i]!)) ++
      [("valid", valid)]
  }

  -- Final gating: grant[8*i + j] = sub_grant[8*i + j] AND group_grant[i]
  let grantGates := (List.range 8).flatMap fun i =>
    (List.range 8).map fun j =>
      Gate.mkAND (sub_grant[8 * i + j]!) (group_grant[i]!) (grant[8 * i + j]!)

  { name := "PriorityArbiter64"
    inputs := request
    outputs := grant ++ [valid]
    gates := grantGates
    instances := subInstances ++ [topInstance]
    signalGroups := [
      { name := "request", width := 64, wires := request },
      { name := "grant", width := 64, wires := grant },
      { name := "group_valid", width := 8, wires := group_valid },
      { name := "group_grant", width := 8, wires := group_grant },
      { name := "sub_grant", width := 64, wires := sub_grant }
    ]
    keepHierarchy := true
  }

/-- 64-input arbiter (hierarchical 2-level 8-way tree) -/
def mkPriorityArbiter64 : Circuit := mkPriorityArbiter64Hierarchical

/-! ## Formally Verified Behavioral Theorems -/

/-- At most one grant signal is high (one-hot property).

    For any request vector, the grant output is one-hot encoded:
    there exists at most one index i where grants[i] = true.
-/
theorem arbiter_onehot (n : Nat) (requests : Fin n → Bool) :
  let result := ArbiterResult.priorityArbitrate n requests
  (∀ i j : Fin n, i ≠ j → result.grants i = true → result.grants j = false) := by
  intro result i j h_ne h_gi
  dsimp [result, ArbiterResult.priorityArbitrate] at h_gi ⊢
  split at h_gi
  · contradiction
  · split at h_gi
    · rename_i idx heq h_lt
      rw [if_pos h_lt]
      dsimp
      dsimp at h_gi
      cases h_gj : (j.val == idx)
      · rfl
      · have hi : i.val = idx := beq_iff_eq.mp h_gi
        have hj : j.val = idx := beq_iff_eq.mp h_gj
        have hij : i = j := Fin.ext (hi.trans hj.symm)
        exact absurd hij h_ne
    · contradiction

/-- Priority ordering: lowest index wins.

    If requests[i] = true and grants[j] = true, then j ≤ i.
    (The granted index is not higher than any requesting index)
-/
theorem arbiter_priority (n : Nat) (requests : Fin n → Bool) :
  let result := ArbiterResult.priorityArbitrate n requests
  (∀ i j : Fin n, requests i = true → result.grants j = true → j.val ≤ i.val) := by
  intro result i j h_req h_gj
  dsimp [result, ArbiterResult.priorityArbitrate] at h_gj
  split at h_gj
  · contradiction
  · rename_i idx heq
    split at h_gj
    · rename_i h_lt
      have hj : j.val = idx := beq_iff_eq.mp h_gj
      rw [hj]
      rw [List.findIdx?_eq_some_iff_getElem] at heq
      rcases heq with ⟨hlen, _, hmin⟩
      by_cases h_lt_i : i.val < idx
      · have h_not := hmin i.val h_lt_i
        simp only [List.getElem_range] at h_not
        rw [dif_pos i.isLt] at h_not
        exact False.elim (h_not h_req)
      · exact Nat.le_of_not_lt h_lt_i
    · contradiction

/-- Valid correctness: valid iff at least one request.

    The valid signal is true exactly when there is at least one request.
-/
theorem arbiter_valid (n : Nat) (requests : Fin n → Bool) :
  let result := ArbiterResult.priorityArbitrate n requests
  result.valid = true ↔ (∃ i : Fin n, requests i = true) := by
  intro result
  dsimp [result, ArbiterResult.priorityArbitrate]
  constructor
  · intro h_val
    split at h_val
    · contradiction
    · rename_i idx heq
      split at h_val
      · rename_i h_lt
        rw [List.findIdx?_eq_some_iff_getElem] at heq
        rcases heq with ⟨hlen, hp, _⟩
        simp only [List.length_range] at hlen
        simp only [List.getElem_range] at hp
        rw [dif_pos hlen] at hp
        exact ⟨⟨idx, hlen⟩, hp⟩
      · contradiction
  · rintro ⟨i, h_req⟩
    split
    · rename_i h_none
      rw [List.findIdx?_eq_none_iff] at h_none
      have h_in : i.val ∈ List.range n := List.mem_range.mpr i.isLt
      have h_false := h_none i.val h_in
      rw [dif_pos i.isLt] at h_false
      simp [h_req] at h_false
    · rename_i idx heq
      rw [List.findIdx?_eq_some_iff_getElem] at heq
      rcases heq with ⟨hlen, _, _⟩
      simp only [List.length_range] at hlen
      rw [if_pos hlen]

/-- Completeness: if any request, exactly one grant.

    If valid = true, then exactly one grant bit is high.
-/
theorem arbiter_completeness (n : Nat) (requests : Fin n → Bool) :
  let result := ArbiterResult.priorityArbitrate n requests
  result.valid = true →
    (∃ i : Fin n, result.grants i = true ∧
      ∀ j : Fin n, result.grants j = true → i = j) := by
  intro result h_val
  dsimp [result, ArbiterResult.priorityArbitrate] at h_val ⊢
  split at h_val
  · contradiction
  · rename_i idx heq
    split at h_val
    · rename_i h_lt
      refine ⟨⟨idx, h_lt⟩, ?_⟩
      constructor
      · rw [if_pos h_lt]
        dsimp
        exact beq_self_eq_true idx
      · intro j h_gj
        rw [if_pos h_lt] at h_gj
        dsimp at h_gj
        have hj : j.val = idx := beq_iff_eq.mp h_gj
        exact Fin.ext hj.symm
    · contradiction

/-- Grant implies request: if granted, then requested.

    If grants[i] = true, then requests[i] = true.
-/
theorem arbiter_grant_implies_request (n : Nat) (requests : Fin n → Bool) :
  let result := ArbiterResult.priorityArbitrate n requests
  (∀ i : Fin n, result.grants i = true → requests i = true) := by
  intro result i h_gi
  dsimp [result, ArbiterResult.priorityArbitrate] at h_gi
  split at h_gi
  · contradiction
  · rename_i idx heq
    split at h_gi
    · rename_i h_lt
      have hi : i.val = idx := beq_iff_eq.mp h_gi
      rw [List.findIdx?_eq_some_iff_getElem] at heq
      rcases heq with ⟨hlen, hp, _⟩
      simp only [List.length_range] at hlen
      simp only [List.getElem_range] at hp
      rw [dif_pos hlen] at hp
      have hext : i = ⟨idx, hlen⟩ := Fin.ext hi
      rw [hext]
      exact hp
    · contradiction

end Shoumei.Circuits.Combinational

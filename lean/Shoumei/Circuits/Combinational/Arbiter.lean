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
  (List.range n).map (fun i => Wire.mk s!"{name}{i}")

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
    }

/-! ## Common Configurations -/

/-- 2-input arbiter (for dual-port arbitration) -/
def mkPriorityArbiter2 : Circuit := mkPriorityArbiter 2

/-- 4-input arbiter (for RS4 ready selection) -/
def mkPriorityArbiter4 : Circuit := mkPriorityArbiter 4

/-- 8-input arbiter (for RS8 ready selection) -/
def mkPriorityArbiter8 : Circuit := mkPriorityArbiter 8

/-! ## Theorems (Stub Placeholders for Future Proofs) -/

/-- At most one grant signal is high (one-hot property).

    For any request vector, the grant output is one-hot encoded:
    there exists at most one index i where grants[i] = true.
-/
axiom arbiter_onehot (n : Nat) (requests : Fin n → Bool) :
  let result := ArbiterResult.priorityArbitrate n requests
  (∀ i j : Fin n, i ≠ j → result.grants i = true → result.grants j = false)

/-- Priority ordering: lowest index wins.

    If requests[i] = true and grants[j] = true, then j ≤ i.
    (The granted index is not higher than any requesting index)
-/
axiom arbiter_priority (n : Nat) (requests : Fin n → Bool) :
  let result := ArbiterResult.priorityArbitrate n requests
  (∀ i j : Fin n, requests i = true → result.grants j = true → j.val ≤ i.val)

/-- Valid correctness: valid iff at least one request.

    The valid signal is true exactly when there is at least one request.
-/
axiom arbiter_valid (n : Nat) (requests : Fin n → Bool) :
  let result := ArbiterResult.priorityArbitrate n requests
  result.valid = true ↔ (∃ i : Fin n, requests i = true)

/-- Completeness: if any request, exactly one grant.

    If valid = true, then exactly one grant bit is high.
-/
axiom arbiter_completeness (n : Nat) (requests : Fin n → Bool) :
  let result := ArbiterResult.priorityArbitrate n requests
  result.valid = true →
    (∃ i : Fin n, result.grants i = true ∧
      ∀ j : Fin n, result.grants j = true → i = j)

/-- Grant implies request: if granted, then requested.

    If grants[i] = true, then requests[i] = true.
-/
axiom arbiter_grant_implies_request (n : Nat) (requests : Fin n → Bool) :
  let result := ArbiterResult.priorityArbitrate n requests
  (∀ i : Fin n, result.grants i = true → requests i = true)

end Shoumei.Circuits.Combinational

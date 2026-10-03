/-
Verification/ExportRefinements.lean - Export Refinement Atoms Registry

Validates refinement atoms against the emitted circuit registry.
-/

import Shoumei.DSL
import Shoumei.Verification.Refinements
import Shoumei.Verification.ExportCerts

namespace Shoumei.Verification.ExportRefinements

open Shoumei
open Shoumei.Verification
open Shoumei.Verification.Refinements

/-- Check that two circuits have identical ports, gate lists, and instance lists. -/
def circuitStructurallyEq (a b : Circuit) : Bool :=
  a.name == b.name
  && a.inputs == b.inputs
  && a.outputs == b.outputs
  && a.gates == b.gates
  && a.instances == b.instances

/-- One export line for one refinement atom, or the reason it cannot be exported.
    Verifies both that `atom.circuit.name == atom.moduleName` and that `atom.circuit`
    is structurally identical to the emitted `Circuit` in `allCircuits`. -/
def refinementLine (emitted : List Circuit) (extraEmitted : List String)
    (atom : RefinementAtom) : Except String String :=
  if atom.circuit.name != atom.moduleName then
    .error s!"{atom.moduleName}: refinement atom circuit has mismatched name '{atom.circuit.name}'"
  else
    match emitted.find? (·.name == atom.moduleName) with
    | some c =>
      if circuitStructurallyEq c atom.circuit then
        .ok s!"{atom.moduleName}|{atom.specName}"
      else
        .error s!"{atom.moduleName}: refinement atom circuit does not match the emitted circuit (ports/gates/instances differ)"
    | none =>
      if extraEmitted.contains atom.moduleName then
        .ok s!"{atom.moduleName}|{atom.specName}"
      else
        .error s!"{atom.moduleName}: refinement atom names a module that is not emitted"

/-- The refinement registry for a given circuit registry, or every
    inconsistency found in it. -/
def exportRefinements (circuits : List Circuit) (extraEmitted : List String) :
    Except String (List String) :=
  let results := allRefinements.map (refinementLine circuits extraEmitted)
  let errors := results.filterMap fun r => match r with | .error e => some e | .ok _ => none
  if errors.isEmpty then
    .ok (results.filterMap fun r => match r with | .ok l => some l | .error _ => none)
  else
    .error ("refinement registry is inconsistent with the circuits:\n  "
            ++ String.intercalate "\n  " errors)

/-- Print the refinement registry, or explain what is wrong and exit non-zero. -/
def printRefinements (circuits : List Circuit) (extraEmitted : List String) : IO Unit := do
  match exportRefinements circuits extraEmitted with
  | .error msg =>
    IO.eprintln s!"✗ {msg}"
    IO.eprintln ""
    IO.eprintln "  A refinement atom must name an emitted circuit and its proven Circuit"
    IO.eprintln "  must be structurally identical to the emitted Circuit."
    IO.Process.exit 1
  | .ok lines =>
    for line in lines do
      IO.println line

end Shoumei.Verification.ExportRefinements

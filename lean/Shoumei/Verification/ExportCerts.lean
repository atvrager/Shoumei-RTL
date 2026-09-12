/-
Verification/ExportCerts.lean - Derive the compositional certificate registry

A certificate says "this module is correct because its sub-modules are".  The
sub-modules of a circuit are its instances, which the DSL already records, so
the registry derives them from the circuits instead of restating them by hand.
Two failure modes disappear with the hand-written list:

1. A certificate could rest on fewer modules than the circuit instantiates
   (`PipelinedMultiplier` claimed 4; the circuit instantiated 8), so the
   composition was accepted against an incomplete premise.
2. A certificate could name a module that is no longer emitted.  After a rename
   the old certificate matched nothing and the new module matched no
   certificate, so it silently fell through to direct LEC -- for the CPU that
   means flattening the whole core.

An inconsistent registry is a hard error here, which fails `make codegen` and
the LEC job rather than degrading verification quietly.

Output format (pipe-separated), consumed by verification/run-lec.sh:
ModuleName|Dependency1,Dependency2,...|ProofReference
-/

import Shoumei.DSL
import Shoumei.Verification.CompositionalCerts

namespace Shoumei.Verification.ExportCerts

open Shoumei.Verification
open Shoumei.Verification.CompositionalCerts

/-- The sub-modules a circuit's correctness rests on: the modules it
    instantiates, deduplicated, excluding itself. -/
def certDeps (c : Circuit) : List String :=
  ((c.instances.map (·.moduleName)).filter (fun m => m != c.name)).eraseDups

/-- One export line for one certificate, or the reason it cannot be exported.

    `extraEmitted` names modules that are emitted without a `Circuit` of their
    own (the RISC-V decoders are LUTs generated from riscv-opcodes).  Such a
    module has no instances, so its dependency list is empty. -/
def certLine (emitted : List Circuit) (extraEmitted : List String)
    (cert : CompositionalCert) : Except String String :=
  let emittedNames := emitted.map (·.name) ++ extraEmitted
  match emitted.find? (·.name == cert.moduleName) with
  | none =>
    if extraEmitted.contains cert.moduleName then
      .ok s!"{cert.moduleName}||{cert.proofReference}"
    else
      .error s!"{cert.moduleName}: certificate names a module that is not emitted"
  | some c =>
    let deps := certDeps c
    let unknown := deps.filter (fun d => !(emittedNames.contains d))
    if unknown.isEmpty then
      .ok s!"{cert.moduleName}|{String.intercalate "," deps}|{cert.proofReference}"
    else
      .error s!"{cert.moduleName}: instantiates {String.intercalate ", " unknown}, \
                which the code generator does not emit"

/-- The certificate registry for a given circuit registry, or every
    inconsistency found in it. -/
def exportCertificates (circuits : List Circuit) (extraEmitted : List String) :
    Except String (List String) :=
  let results := allCerts.map (certLine circuits extraEmitted)
  let errors := results.filterMap fun r => match r with | .error e => some e | .ok _ => none
  if errors.isEmpty then
    .ok (results.filterMap fun r => match r with | .ok l => some l | .error _ => none)
  else
    .error ("certificate registry is inconsistent with the circuits:\n  "
            ++ String.intercalate "\n  " errors)

/-- Print the registry, or explain what is wrong and exit non-zero. -/
def printCertificates (circuits : List Circuit) (extraEmitted : List String) : IO Unit := do
  match exportCertificates circuits extraEmitted with
  | .error msg =>
    IO.eprintln s!"✗ {msg}"
    IO.eprintln ""
    IO.eprintln "  A certificate must name an emitted circuit, and every module that"
    IO.eprintln "  circuit instantiates must be emitted too.  Delete the entry, or point"
    IO.eprintln "  it at the circuit's current name."
    IO.Process.exit 1
  | .ok lines =>
    for line in lines do
      IO.println line

end Shoumei.Verification.ExportCerts

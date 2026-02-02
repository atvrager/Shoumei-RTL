/-
ExportVerificationCerts.lean - Export Compositional Verification Certificates

Generates certificates for modules that use compositional verification instead of
full LEC. Each certificate specifies:
- Module name
- Building block dependencies (must pass LEC first)
- Lean proof reference (structural + compositional correctness)

Output format (pipe-separated):
ModuleName|Dependency1,Dependency2,...|ProofReference
-/

import Shoumei.Verification.CompositionalCerts

open Shoumei.Verification.CompositionalCerts

/-- Format a compositional certificate for shell consumption -/
def formatCert (cert : Shoumei.Verification.CompositionalCert) : String :=
  let deps := String.intercalate "," cert.dependencies
  s!"{cert.moduleName}|{deps}|{cert.proofReference}"

/-- Export all certificates to stdout -/
def main : IO Unit := do
  for cert in allCerts do
    IO.println (formatCert cert)

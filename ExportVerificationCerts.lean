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

import Shoumei.RISCV.Execution.ReservationStationProofs

open Shoumei.RISCV.Execution

/-- Format a compositional certificate for shell consumption -/
def formatCert (cert : CompositionalCert) : String :=
  let deps := String.intercalate "," cert.dependencies
  s!"{cert.moduleName}|{deps}|{cert.proofReference}"

/-- All compositional verification certificates in the project -/
def allCerts : List CompositionalCert := [
  rs4_cert
  -- Add more certs here as we create them (e.g., PhysRegFile, RenameStage, etc.)
]

/-- Export all certificates to stdout -/
def main : IO Unit := do
  for cert in allCerts do
    IO.println (formatCert cert)

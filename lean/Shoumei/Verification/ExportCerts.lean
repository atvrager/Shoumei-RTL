-- Export Verification Certificates
-- Generates the compositional verification registry from Lean certificates

import Shoumei.Verification.Compositional

namespace Shoumei.Verification.ExportCerts

open Shoumei.Verification

def formatDependencies (deps : List String) : String :=
  String.intercalate "," deps

def exportCertificate (cert : VerificationCertificate) : Option String :=
  match cert.method with
  | .Compositional =>
    let deps := formatDependencies cert.dependencies
    let proof := cert.leanProof.getD "unknown"
    some s!"{cert.moduleName}|{deps}|{proof}"
  | _ => none  -- Only export compositional certs, LEC handles the rest

def exportAllCertificates : String :=
  let header := "# Compositional Verification Certificates\n" ++
                "# Auto-generated from lean/Shoumei/Verification/Compositional.lean\n" ++
                "# Format: MODULE_NAME | DEPENDENCIES | LEAN_PROOF\n" ++
                "#\n" ++
                "# DO NOT EDIT - Regenerate with: lake exe export_verification_certs\n\n"

  let compositionalCerts := allCertificates.filterMap exportCertificate

  header ++ String.intercalate "\n" compositionalCerts ++ "\n"

-- Output format: one certificate per line, pipe-separated
def mainStdout : IO Unit := do
  for cert in allCertificates do
    match cert.method with
    | .Compositional =>
      let deps := formatDependencies cert.dependencies
      let proof := cert.leanProof.getD "unknown"
      IO.println s!"{cert.moduleName}|{deps}|{proof}"
    | _ => pure ()  -- Skip LEC certs

-- Legacy mode: write to file (for debugging)
def mainFile : IO Unit := do
  let content := exportAllCertificates
  IO.FS.writeFile "verification/compositional-certs.txt" content
  IO.println s!"✓ Exported {allCertificates.length} verification certificates"
  IO.println s!"  Compositional: {countByMethod .Compositional}"
  IO.println s!"  LEC: {countByMethod .LEC}"
  IO.println "✓ Written to: verification/compositional-certs.txt"

def main (args : List String) : IO Unit :=
  match args with
  | ["--stdout"] => mainStdout
  | _ => mainFile  -- Default: write file for compatibility

end Shoumei.Verification.ExportCerts

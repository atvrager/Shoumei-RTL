/-
scripts/export-proof-manifest.lean - Export Lean-native proof manifest to JSON
Run via: lake env lean --run scripts/export-proof-manifest.lean [output/proof-manifest.json]
-/

import Shoumei.Verification.ProofManifest

open Shoumei.Verification.ProofManifest

unsafe def main (args : List String) : IO Unit := do
  let outPath := match args.head? with
    | some p => p
    | none => "output/proof-manifest.json"
  generateProofManifest outPath

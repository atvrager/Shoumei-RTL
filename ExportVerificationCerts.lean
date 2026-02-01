-- Export Verification Certificates Executable
-- Generates compositional verification registry from Lean certificates

import Shoumei.Verification.ExportCerts

def main (args : List String) : IO Unit :=
  Shoumei.Verification.ExportCerts.main args

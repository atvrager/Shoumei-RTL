/-
GenerateQueueN.lean - Executable for generating QueueN circuits
-/

import Shoumei.Circuits.Sequential.QueueNCodegen

open Shoumei.Circuits.Sequential

def main (_args : List String) : IO Unit := do
  Shoumei.Circuits.Sequential.main

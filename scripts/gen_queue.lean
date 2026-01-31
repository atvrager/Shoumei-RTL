import Shoumei.Examples.QueueExample

open Shoumei.Examples

def main : IO Unit := do
  writeQueue1_8bit
  writeQueue1_32bit
  IO.println "✓ All queues generated"

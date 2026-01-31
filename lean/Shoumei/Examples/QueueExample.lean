/-
QueueExample.lean - Queue/FIFO Code Generation Example

Generates SystemVerilog and Chisel for various Queue sizes.
This demonstrates ready/valid handshaking in synthesizable hardware.
-/

import Shoumei.Circuits.Sequential.Queue
import Shoumei.Codegen.Queue

namespace Shoumei.Examples

open Shoumei.Circuits.Sequential
open Shoumei.Codegen.Queue

-- Helper to generate Queue files for any width
def writeQueueFiles (width : Nat) : IO Unit := do
  let q := mkQueue1 width
  let svPath := s!"output/sv-from-lean/{q.name}.sv"
  let chiselPath := s!"chisel/src/main/scala/generated/{q.name}.scala"

  IO.FS.writeFile svPath (toSystemVerilog q)
  IO.FS.writeFile chiselPath (toChisel q)

  IO.println s!"✓ Generated: {svPath}"
  IO.println s!"✓ Generated: {chiselPath}"

-- Specific widths
def writeQueue1_8bit : IO Unit := writeQueueFiles 8
def writeQueue1_32bit : IO Unit := writeQueueFiles 32

-- Main entry point for Queue generation
def main : IO Unit := do
  IO.println "証明 Shoumei RTL - Queue Code Generation"
  IO.println "========================================"
  IO.println ""

  IO.println "==> Queue1_8 (8-bit data, 1-entry)"
  writeQueue1_8bit
  IO.println ""

  IO.println "==> Queue1_32 (32-bit data, 1-entry)"
  writeQueue1_32bit
  IO.println ""

  IO.println "✓ Queue code generation complete"
  IO.println ""
  IO.println "Note: Multi-entry queues (depth > 1) require circular buffer"
  IO.println "      implementation with head/tail pointers. This is a future"
  IO.println "      enhancement for Phase 1."

end Shoumei.Examples

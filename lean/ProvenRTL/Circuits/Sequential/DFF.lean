/-
Circuits/Sequential/DFF.lean - D Flip-Flop Example

A simple D flip-flop with synchronous reset.

Behavior:
- On rising edge of clock:
  - If reset is high: q = 0
  - Otherwise: q = d (capture data input)
-/

import ProvenRTL.DSL

namespace ProvenRTL.Circuits.Sequential

open ProvenRTL

-- Build a simple D Flip-Flop circuit
-- Note: Use "clock" as wire name to match Chisel Module conventions
def mkDFlipFlop : Circuit :=
  let d := Wire.mk "d"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let q := Wire.mk "q"

  { name := "DFlipFlop"
    inputs := [d, clock, reset]
    outputs := [q]
    gates := [
      Gate.mkDFF d clock reset q
    ]
  }

-- Example: DFF that captures a data bit
def dff : Circuit := mkDFlipFlop

end ProvenRTL.Circuits.Sequential

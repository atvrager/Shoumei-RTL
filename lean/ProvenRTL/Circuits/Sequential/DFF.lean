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
def mkDFlipFlop : Circuit :=
  let d := Wire.mk "d"
  let clk := Wire.mk "clk"
  let reset := Wire.mk "reset"
  let q := Wire.mk "q"

  { name := "DFlipFlop"
    inputs := [d, clk, reset]
    outputs := [q]
    gates := [
      Gate.mkDFF d clk reset q
    ]
  }

-- Example: DFF that captures a data bit
def dff : Circuit := mkDFlipFlop

end ProvenRTL.Circuits.Sequential

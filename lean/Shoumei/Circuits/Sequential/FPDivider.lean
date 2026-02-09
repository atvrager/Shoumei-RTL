/-
Circuits/Sequential/FPDivider.lean - 24-Cycle Iterative FP Divider

An iterative floating-point divider for IEEE 754 binary32.
Uses a busy/done state machine protocol identical to the integer Divider32.

Algorithm:
  Latches inputs on start, counts 24 cycles (0..23), asserts done when
  counter reaches 23. Result and exception outputs are placeholders.

Architecture:
- Sequential circuit (DFF registers, clock, reset)
- 24 cycles to complete one division
- Busy/done handshake protocol

State registers:
- src1_q[31:0]: Latched dividend (32 DFFs)
- src2_q[31:0]: Latched divisor (32 DFFs)
- rm_q[2:0]: Latched rounding mode (3 DFFs)
- tag_q[5:0]: Latched destination tag (6 DFFs)
- cnt_q[4:0]: 5-bit cycle counter 0..23 (5 DFFs)
- busy_q: Busy flag (1 DFF)
Total: 79 DFFs

Interface:
- Inputs: src1[31:0], src2[31:0], rm[2:0], dest_tag[5:0], start,
          clock, reset, zero, one
- Outputs: result[31:0], tag_out[5:0], exc[4:0], valid_out, busy
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.RippleCarryAdder

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Circuits.Combinational

/-! ## Helper: Indexed Wire Generation -/

private def makeIndexedWires (pfx : String) (n : Nat) : List Wire :=
  (List.range n).map fun i => Wire.mk (pfx ++ "_" ++ toString i)

/-! ## Structural Circuit -/

/-- Build the 24-cycle iterative FP divider structural circuit.

    **Inputs (76 total):**
    - src1[31:0]: Dividend (32 bits)
    - src2[31:0]: Divisor (32 bits)
    - rm[2:0]: Rounding mode (3 bits)
    - dest_tag[5:0]: Physical register tag (6 bits)
    - start: Begin new division
    - clock, reset: Sequential control
    - zero: Constant low
    - one: Constant high

    **Outputs (44 total):**
    - result[31:0]: FP result (placeholder: passes src1 through)
    - tag_out[5:0]: Destination tag pass-through
    - exc[4:0]: Exception flags (placeholder: all zero)
    - valid_out: Result ready this cycle
    - busy: Cannot accept new operations

    **State registers (79 DFFs):**
    - src1_q[31:0]: 32 DFFs
    - src2_q[31:0]: 32 DFFs
    - rm_q[2:0]: 3 DFFs
    - tag_q[5:0]: 6 DFFs
    - cnt_q[4:0]: 5 DFFs
    - busy_q: 1 DFF
-/
def mkFPDivider : Circuit :=
  -- ══════════════════════════════════════════════
  -- Input wires
  -- ══════════════════════════════════════════════
  let src1_in := makeIndexedWires "src1" 32
  let src2_in := makeIndexedWires "src2" 32
  let rm_in := makeIndexedWires "rm" 3
  let dest_tag := makeIndexedWires "dest_tag" 6
  let start := Wire.mk "start"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- ══════════════════════════════════════════════
  -- Output wires
  -- ══════════════════════════════════════════════
  let result := makeIndexedWires "result" 32
  let tag_out := makeIndexedWires "tag_out" 6
  let exc := makeIndexedWires "exc" 5
  let valid_out := Wire.mk "valid_out"
  let busy_out := Wire.mk "busy"

  -- ══════════════════════════════════════════════
  -- State register wires (DFF outputs = current state)
  -- ══════════════════════════════════════════════
  let src1_q := makeIndexedWires "src1_q" 32
  let src2_q := makeIndexedWires "src2_q" 32
  let rm_q := makeIndexedWires "rm_q" 3
  let tag_q := makeIndexedWires "tag_q" 6
  let cnt_q := makeIndexedWires "cnt_q" 5
  let busy_q := Wire.mk "busy_q"

  -- Next-state wires (DFF inputs)
  let src1_d := makeIndexedWires "src1_d" 32
  let src2_d := makeIndexedWires "src2_d" 32
  let rm_d := makeIndexedWires "rm_d" 3
  let tag_d := makeIndexedWires "tag_d" 6
  let cnt_d := makeIndexedWires "cnt_d" 5
  let busy_d := Wire.mk "busy_d"

  -- ══════════════════════════════════════════════
  -- Control signals (combinational)
  -- ══════════════════════════════════════════════
  let not_busy := Wire.mk "not_busy"
  let start_new := Wire.mk "start_new"           -- start AND NOT busy_q
  let cnt_is_23 := Wire.mk "cnt_is_23"           -- counter == 23 (10111)
  let done := Wire.mk "done"                      -- busy_q AND cnt_is_23
  let not_done := Wire.mk "not_done"
  let busy_and_not_done := Wire.mk "busy_and_not_done"

  -- cnt == 23 = 10111: bits 0,1,2 = 1, bit 3 = 0, bit 4 = 1
  let cnt3_inv := Wire.mk "cnt3_inv"

  let ctrl_gates := [
    -- not_busy = !busy_q
    Gate.mkNOT busy_q not_busy,
    -- start_new = start && !busy_q
    Gate.mkAND start not_busy start_new,
    -- cnt_is_23: counter[4:0] == 5'b10111
    Gate.mkNOT (cnt_q[3]!) cnt3_inv,
    Gate.mkAND (cnt_q[0]!) (cnt_q[1]!) (Wire.mk "cnt_01"),
    Gate.mkAND (cnt_q[2]!) cnt3_inv (Wire.mk "cnt_2n3"),
    Gate.mkAND (Wire.mk "cnt_01") (Wire.mk "cnt_2n3") (Wire.mk "cnt_0123"),
    Gate.mkAND (Wire.mk "cnt_0123") (cnt_q[4]!) cnt_is_23,
    -- done = busy_q && cnt_is_23
    Gate.mkAND busy_q cnt_is_23 done,
    -- not_done = !done
    Gate.mkNOT done not_done,
    -- busy_and_not_done = busy_q && !done
    Gate.mkAND busy_q not_done busy_and_not_done
  ]

  -- ══════════════════════════════════════════════
  -- Busy flag next state
  -- busy_d = start_new OR busy_and_not_done
  -- ══════════════════════════════════════════════
  let busy_gates := [
    Gate.mkOR start_new busy_and_not_done busy_d
  ]

  -- ══════════════════════════════════════════════
  -- Counter increment logic (5-bit ripple incrementer)
  -- cnt_next = cnt_q + 1
  -- ══════════════════════════════════════════════
  let cnt_next := makeIndexedWires "cnt_next" 5
  let inc_carry := makeIndexedWires "inc_carry" 6

  let cnt_inc_gates :=
    [Gate.mkBUF one (inc_carry[0]!)] ++
    (List.range 5).flatMap (fun i =>
      [
        Gate.mkXOR (cnt_q[i]!) (inc_carry[i]!) (cnt_next[i]!),
        Gate.mkAND (cnt_q[i]!) (inc_carry[i]!) (inc_carry[i + 1]!)
      ]
    )

  -- ══════════════════════════════════════════════
  -- Counter next-state MUX (two-level)
  -- m1[i] = MUX(cnt_q[i], cnt_next[i], busy_and_not_done)
  -- cnt_d[i] = MUX(m1[i], zero, start_new)
  -- ══════════════════════════════════════════════
  let cnt_m1 := makeIndexedWires "cnt_m1" 5
  let cnt_mux_gates := (List.range 5).flatMap (fun i => [
    Gate.mkMUX (cnt_q[i]!) (cnt_next[i]!) busy_and_not_done (cnt_m1[i]!),
    Gate.mkMUX (cnt_m1[i]!) zero start_new (cnt_d[i]!)
  ])

  -- ══════════════════════════════════════════════
  -- Data latch MUXes: latch on start_new, hold otherwise
  -- src1_d[i] = MUX(src1_q[i], src1_in[i], start_new)
  -- ══════════════════════════════════════════════
  let src1_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (src1_q[i]!) (src1_in[i]!) start_new (src1_d[i]!)
  )

  let src2_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (src2_q[i]!) (src2_in[i]!) start_new (src2_d[i]!)
  )

  let rm_mux_gates := (List.range 3).map (fun i =>
    Gate.mkMUX (rm_q[i]!) (rm_in[i]!) start_new (rm_d[i]!)
  )

  let tag_mux_gates := (List.range 6).map (fun i =>
    Gate.mkMUX (tag_q[i]!) (dest_tag[i]!) start_new (tag_d[i]!)
  )

  -- ══════════════════════════════════════════════
  -- DFF registers (all state elements)
  -- ══════════════════════════════════════════════
  let src1_dffs := (List.range 32).map (fun i =>
    Gate.mkDFF (src1_d[i]!) clock reset (src1_q[i]!)
  )
  let src2_dffs := (List.range 32).map (fun i =>
    Gate.mkDFF (src2_d[i]!) clock reset (src2_q[i]!)
  )
  let rm_dffs := (List.range 3).map (fun i =>
    Gate.mkDFF (rm_d[i]!) clock reset (rm_q[i]!)
  )
  let tag_dffs := (List.range 6).map (fun i =>
    Gate.mkDFF (tag_d[i]!) clock reset (tag_q[i]!)
  )
  let cnt_dffs := (List.range 5).map (fun i =>
    Gate.mkDFF (cnt_d[i]!) clock reset (cnt_q[i]!)
  )
  let busy_dff := [Gate.mkDFF busy_d clock reset busy_q]

  -- ══════════════════════════════════════════════
  -- Output connections
  -- ══════════════════════════════════════════════

  -- result[31:0] = BUF from src1_q (placeholder)
  let result_gates := (List.range 32).map (fun i =>
    Gate.mkBUF (src1_q[i]!) (result[i]!)
  )

  -- tag_out[5:0] = BUF from tag_q
  let tag_out_gates := (List.range 6).map (fun i =>
    Gate.mkBUF (tag_q[i]!) (tag_out[i]!)
  )

  -- exc[4:0] = all zero (placeholder)
  let exc_gates := (List.range 5).map (fun i =>
    Gate.mkBUF zero (exc[i]!)
  )

  -- valid_out = done
  let valid_gate := [Gate.mkBUF done valid_out]

  -- busy output = busy_q
  let busy_gate := [Gate.mkBUF busy_q busy_out]

  -- ══════════════════════════════════════════════
  -- Assemble all gates
  -- ══════════════════════════════════════════════
  let all_gates :=
    ctrl_gates ++
    busy_gates ++
    cnt_inc_gates ++
    cnt_mux_gates ++
    src1_mux_gates ++
    src2_mux_gates ++
    rm_mux_gates ++
    tag_mux_gates ++
    src1_dffs ++
    src2_dffs ++
    rm_dffs ++
    tag_dffs ++
    cnt_dffs ++
    busy_dff ++
    result_gates ++
    tag_out_gates ++
    exc_gates ++
    valid_gate ++
    busy_gate

  { name := "FPDivider"
    inputs := src1_in ++ src2_in ++ rm_in ++ dest_tag ++
              [start, clock, reset, zero, one]
    outputs := result ++ tag_out ++ exc ++ [valid_out, busy_out]
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "src1", width := 32, wires := src1_in },
      { name := "src2", width := 32, wires := src2_in },
      { name := "rm", width := 3, wires := rm_in },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 32, wires := result },
      { name := "tag_out", width := 6, wires := tag_out },
      { name := "exc", width := 5, wires := exc },
      { name := "cnt_q", width := 5, wires := cnt_q }
    ]
  }

/-- Convenience definition for the FP divider circuit. -/
def fpDividerCircuit : Circuit := mkFPDivider

end Shoumei.Circuits.Sequential

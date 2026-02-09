/-
Circuits/Sequential/FPSqrt.lean - 24-cycle Iterative FP Square Root

An iterative floating-point square root unit for IEEE 754 binary32.
Takes a single source operand and produces the square root over 24 cycles.

State registers:
- src1_q[31:0]: Latched source operand
- rm_q[2:0]: Latched rounding mode
- tag_q[5:0]: Latched destination tag
- cnt_q[4:0]: Cycle counter (0..23)
- busy_q: Busy flag
Total: 47 DFFs

Interface:
- Inputs: src1[31:0], rm[2:0], dest_tag[5:0], start, clock, reset, zero, one
- Outputs: result[31:0], tag_out[5:0], exc[4:0], valid_out, busy
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.RippleCarryAdder

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Circuits.Combinational

/-- Build the 24-cycle iterative FP square root structural circuit.

    **Inputs (44 total):**
    - src1[31:0]: Source operand (32 bits)
    - rm[2:0]: Rounding mode
    - dest_tag[5:0]: Physical register tag
    - start: Begin new operation
    - clock, reset: Sequential control
    - zero: Constant low
    - one: Constant high

    **Outputs (44 total):**
    - result[31:0]: Square root result (placeholder: BUF src1_q)
    - tag_out[5:0]: Pass-through destination tag
    - exc[4:0]: Exception flags (all zero placeholder)
    - valid_out: Result ready this cycle
    - busy: Cannot accept new operations

    **State registers (DFFs):**
    - src1_q[31:0]: 32 DFFs
    - rm_q[2:0]: 3 DFFs
    - tag_q[5:0]: 6 DFFs
    - cnt_q[4:0]: 5 DFFs
    - busy_q: 1 DFF
    Total: 47 DFFs
-/
def mkFPSqrt : Circuit :=
  -- ══════════════════════════════════════════════
  -- Input wires
  -- ══════════════════════════════════════════════
  let src1_in := makeIndexedWires "src1" 32
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
  let rm_q := makeIndexedWires "rm_q" 3
  let tag_q := makeIndexedWires "tag_q" 6
  let cnt_q := makeIndexedWires "cnt_q" 5
  let busy_q := Wire.mk "busy_q"

  -- Next-state wires (DFF inputs)
  let src1_d := makeIndexedWires "src1_d" 32
  let rm_d := makeIndexedWires "rm_d" 3
  let tag_d := makeIndexedWires "tag_d" 6
  let cnt_d := makeIndexedWires "cnt_d" 5
  let busy_d := Wire.mk "busy_d"

  -- ══════════════════════════════════════════════
  -- Control signals
  -- ══════════════════════════════════════════════
  let not_busy := Wire.mk "not_busy"
  let start_new := Wire.mk "start_new"
  let cnt_is_23 := Wire.mk "cnt_is_23"
  let done := Wire.mk "done"
  let not_done := Wire.mk "not_done"
  let busy_and_not_done := Wire.mk "busy_and_not_done"
  let not_cnt3 := Wire.mk "not_cnt3"

  -- cnt_is_23: cnt_q[4:0] == 5'b10111 (23 decimal)
  -- bit0=1, bit1=1, bit2=1, bit3=0, bit4=1
  let ctrl_gates := [
    Gate.mkNOT busy_q not_busy,
    Gate.mkAND start not_busy start_new,
    -- cnt_is_23 decode: bits 0,1,2,4 high; bit 3 low
    Gate.mkNOT (cnt_q[3]!) not_cnt3,
    Gate.mkAND (cnt_q[0]!) (cnt_q[1]!) (Wire.mk "cnt_01"),
    Gate.mkAND (cnt_q[2]!) not_cnt3 (Wire.mk "cnt_2n3"),
    Gate.mkAND (Wire.mk "cnt_01") (Wire.mk "cnt_2n3") (Wire.mk "cnt_0123"),
    Gate.mkAND (Wire.mk "cnt_0123") (cnt_q[4]!) cnt_is_23,
    -- done / busy control
    Gate.mkAND busy_q cnt_is_23 done,
    Gate.mkNOT done not_done,
    Gate.mkAND busy_q not_done busy_and_not_done
  ]

  -- ══════════════════════════════════════════════
  -- Busy flag next state: busy_d = start_new OR busy_and_not_done
  -- ══════════════════════════════════════════════
  let busy_gates := [
    Gate.mkOR start_new busy_and_not_done busy_d
  ]

  -- ══════════════════════════════════════════════
  -- Counter increment logic (5-bit ripple)
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
  -- Counter next-state MUX:
  --   m1 = MUX(cnt_q, cnt_next, busy_and_not_done)
  --   cnt_d = MUX(m1, zero, start_new)
  -- ══════════════════════════════════════════════
  let cnt_m1 := makeIndexedWires "cnt_m1" 5
  let cnt_mux_gates := (List.range 5).flatMap (fun i => [
    Gate.mkMUX (cnt_q[i]!) (cnt_next[i]!) busy_and_not_done (cnt_m1[i]!),
    Gate.mkMUX (cnt_m1[i]!) zero start_new (cnt_d[i]!)
  ])

  -- ══════════════════════════════════════════════
  -- Latch logic: src1_d = MUX(src1_q, src1_in, start_new)
  -- ══════════════════════════════════════════════
  let src1_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (src1_q[i]!) (src1_in[i]!) start_new (src1_d[i]!)
  )

  -- rm_d = MUX(rm_q, rm_in, start_new)
  let rm_mux_gates := (List.range 3).map (fun i =>
    Gate.mkMUX (rm_q[i]!) (rm_in[i]!) start_new (rm_d[i]!)
  )

  -- tag_d = MUX(tag_q, dest_tag, start_new)
  let tag_mux_gates := (List.range 6).map (fun i =>
    Gate.mkMUX (tag_q[i]!) (dest_tag[i]!) start_new (tag_d[i]!)
  )

  -- ══════════════════════════════════════════════
  -- DFF registers
  -- ══════════════════════════════════════════════
  let src1_dffs := (List.range 32).map (fun i =>
    Gate.mkDFF (src1_d[i]!) clock reset (src1_q[i]!)
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

  -- result = BUF src1_q (placeholder for actual sqrt computation)
  let result_gates := (List.range 32).map (fun i =>
    Gate.mkBUF (src1_q[i]!) (result[i]!)
  )

  -- tag_out = BUF tag_q
  let tag_out_gates := (List.range 6).map (fun i =>
    Gate.mkBUF (tag_q[i]!) (tag_out[i]!)
  )

  -- valid_out = done
  let valid_gate := [Gate.mkBUF done valid_out]

  -- busy = BUF busy_q
  let busy_gate := [Gate.mkBUF busy_q busy_out]

  -- exc = all zero (placeholder)
  let exc_gates := (List.range 5).map (fun i =>
    Gate.mkBUF zero (exc[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Assemble all gates
  -- ══════════════════════════════════════════════
  let all_gates :=
    ctrl_gates ++
    busy_gates ++
    cnt_inc_gates ++
    cnt_mux_gates ++
    src1_mux_gates ++
    rm_mux_gates ++
    tag_mux_gates ++
    src1_dffs ++
    rm_dffs ++
    tag_dffs ++
    cnt_dffs ++
    busy_dff ++
    result_gates ++
    tag_out_gates ++
    valid_gate ++
    busy_gate ++
    exc_gates

  { name := "FPSqrt"
    inputs := src1_in ++ rm_in ++ dest_tag ++ [start, clock, reset, zero, one]
    outputs := result ++ tag_out ++ exc ++ [valid_out, busy_out]
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "src1", width := 32, wires := src1_in },
      { name := "rm", width := 3, wires := rm_in },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 32, wires := result },
      { name := "tag_out", width := 6, wires := tag_out },
      { name := "exc", width := 5, wires := exc },
      { name := "cnt_q", width := 5, wires := cnt_q }
    ]
  }

/-- Convenience definition for the FP square root circuit. -/
def fpSqrtCircuit : Circuit := mkFPSqrt

end Shoumei.Circuits.Sequential

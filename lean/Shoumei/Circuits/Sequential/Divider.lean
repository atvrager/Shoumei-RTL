/-
Circuits/Sequential/Divider.lean - 32-cycle Restoring Divider

A sequential restoring divider for RV32IM M-extension division operations.

Algorithm (restoring division):
  Each cycle (0..31):
    1. Shift remainder left by 1 bit
    2. Trial-subtract divisor from upper 32 bits of remainder
    3. If result non-negative (no borrow): keep subtracted value, quotient bit = 1
    4. If negative (borrow): restore old value, quotient bit = 0
  After 32 cycles: quotient and remainder are ready

Architecture:
- Sequential circuit (DFF registers, clock, reset)
- Uses Subtractor32 instance for trial subtraction
- 32 cycles to complete one division

State registers:
- remainder[63:0]: 64-bit shift register (running remainder)
- divisor[31:0]: Latched divisor value
- quotient[31:0]: Accumulates quotient bits MSB to LSB
- counter[4:0]: 5-bit cycle counter (0-31)
- busy: Single-bit busy flag
- tag[5:0]: Latched destination tag
- op[2:0]: Latched operation type (DIV/DIVU/REM/REMU selection)

Interface:
- Inputs: a[31:0], b[31:0], op[2:0], dest_tag[5:0], start, clock, reset
- Outputs: result[31:0], tag_out[5:0], valid_out, busy
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.RippleCarryAdder

namespace Shoumei.Circuits.Sequential

open Shoumei

/-! ## Behavioral Model -/

/-- State of the restoring divider.

    Tracks all internal registers needed for the 32-cycle division algorithm.
-/
structure DividerState where
  /-- 64-bit running remainder (upper 32 bits are the partial remainder) -/
  remainder : UInt64 := 0
  /-- Latched divisor value -/
  divisor : UInt32 := 0
  /-- Accumulated quotient bits -/
  quotient : UInt32 := 0
  /-- Cycle counter (0-31) -/
  counter : Nat := 0
  /-- Whether the divider is currently busy -/
  busy : Bool := false
  /-- Latched destination physical register tag -/
  tag : Fin 64 := 0
  /-- Latched operation type encoding:
      4 = DIV (signed), 5 = DIVU (unsigned),
      6 = REM (signed), 7 = REMU (unsigned) -/
  op : Nat := 0
  /-- Whether the original dividend was negative (for signed result correction) -/
  a_neg : Bool := false
  /-- Whether the original divisor was negative (for signed result correction) -/
  b_neg : Bool := false
  deriving Repr

/-- Initialize the divider for a new division operation.

    Latches dividend, divisor, tag, and op code.
    Sets remainder to {0, dividend} (dividend in lower 32 bits).
    Clears quotient and resets counter to 0.
-/
def dividerStart (a b : UInt32) (tag : Fin 64) (op : Nat) : DividerState :=
  -- Signed operations (DIV=4, REM=6) have op[0]=0; unsigned (DIVU=5, REMU=7) have op[0]=1
  let is_signed := op % 2 == 0
  let a_neg := is_signed && (a >>> 31 == 1)
  let b_neg := is_signed && (b >>> 31 == 1)
  -- Take absolute values for signed operations
  let abs_a := if a_neg then (0 : UInt32) - a else a
  let abs_b := if b_neg then (0 : UInt32) - b else b
  { remainder := abs_a.toUInt64
    divisor := abs_b
    quotient := 0
    counter := 0
    busy := true
    tag := tag
    op := op
    a_neg := a_neg
    b_neg := b_neg
  }

/-- Perform one iteration of the restoring division algorithm.

    Returns the updated state and optionally the result if this is the
    final cycle (counter = 31).

    **Algorithm per cycle:**
    1. Shift remainder left by 1: `shifted = remainder << 1`
    2. Extract upper 32 bits: `upper = shifted[63:32]`
    3. Trial subtract: `trial = upper - divisor`
    4. If trial >= 0 (no borrow):
       - `remainder = {trial[31:0], shifted[31:0]}`
       - `quotient[31 - counter] = 1`
    5. If trial < 0 (borrow):
       - `remainder = shifted` (restore)
       - `quotient[31 - counter] = 0`

    **Result selection (on final cycle):**
    - DIV/DIVU (op=4,5): return quotient
    - REM/REMU (op=6,7): return remainder[63:32]
-/
def dividerStep (state : DividerState) : DividerState × Option (Fin 64 × UInt32) :=
  if !state.busy then
    (state, none)
  else
    -- Step 1: Shift remainder left by 1
    let shifted := state.remainder <<< 1

    -- Step 2: Extract upper 32 bits
    let upper := (shifted >>> 32).toUInt32

    -- Step 3: Trial subtraction (upper - divisor)
    -- Check if upper >= divisor (no borrow)
    let no_borrow := upper >= state.divisor
    let trial := upper - state.divisor

    -- Step 4/5: Update remainder and quotient
    let new_remainder :=
      if no_borrow then
        -- Keep subtracted value: {trial, shifted[31:0]}
        (trial.toUInt64 <<< 32) ||| (shifted &&& 0xFFFFFFFF)
      else
        -- Restore: keep shifted value
        shifted

    -- Set quotient bit at position (31 - counter)
    let bit_pos := 31 - state.counter
    let new_quotient :=
      if no_borrow then
        state.quotient ||| (1 <<< bit_pos.toUInt32)
      else
        state.quotient

    -- Check if this is the final cycle
    if state.counter == 31 then
      -- Select raw result based on operation type
      let raw_result :=
        if state.op == 6 || state.op == 7 then
          -- REM/REMU: return upper remainder
          (new_remainder >>> 32).toUInt32
        else
          -- DIV/DIVU: return quotient
          new_quotient
      -- Apply sign correction for signed operations
      -- DIV: negate quotient if signs of dividend and divisor differ
      -- REM: negate remainder if dividend was negative
      let needs_negate :=
        if state.op == 4 then state.a_neg != state.b_neg  -- DIV: xor signs
        else if state.op == 6 then state.a_neg             -- REM: dividend sign
        else false                                          -- DIVU/REMU: no correction
      let result_val := if needs_negate then (0 : UInt32) - raw_result else raw_result
      let final_state := { state with
        remainder := new_remainder
        quotient := new_quotient
        counter := 0
        busy := false
      }
      (final_state, some (state.tag, result_val))
    else
      let next_state := { state with
        remainder := new_remainder
        quotient := new_quotient
        counter := state.counter + 1
      }
      (next_state, none)

/-- Run the divider to completion (all 32 cycles).

    Convenience function for testing. Starts a division and steps until
    a result is produced.
-/
def dividerRun (a b : UInt32) (tag : Fin 64) (op : Nat) : Option (Fin 64 × UInt32) :=
  let init := dividerStart a b tag op
  let rec loop (state : DividerState) (fuel : Nat) : Option (Fin 64 × UInt32) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let (next, result) := dividerStep state
      match result with
      | some r => some r
      | none => loop next fuel'
  loop init 33  -- 32 cycles + 1 for safety

/-! ## Verification Helpers -/

/-- Verify unsigned division. -/
def verifyDIVU (a b : UInt32) : Bool :=
  if b == 0 then true  -- Division by zero is undefined
  else
    match dividerRun a b 0 5 with
    | some (_, result) => result == a / b
    | none => false

/-- Verify unsigned remainder. -/
def verifyREMU (a b : UInt32) : Bool :=
  if b == 0 then true  -- Division by zero is undefined
  else
    match dividerRun a b 0 7 with
    | some (_, result) => result == a % b
    | none => false

/-! ## Structural Circuit

The structural circuit uses a hierarchical approach:
- Subtractor32 instance for trial subtraction
- DFF gates for all state registers
- MUX gates for restore/keep decision
- AND/OR/NOT gates for control logic

The circuit is organized into:
1. State registers (DFFs for remainder, divisor, quotient, counter, busy, tag, op)
2. Shift logic (combinational, shifts remainder left by 1)
3. Trial subtraction (Subtractor32 instance)
4. Restore/keep MUX (select between subtracted and shifted based on borrow)
5. Quotient bit insertion (set bit at position 31-counter)
6. Counter logic (increment, detect completion)
7. Control logic (start/busy/done FSM)
8. Result selection (MUX between quotient and remainder based on op)
-/

open Shoumei.Circuits.Combinational

/-- Build the 32-cycle restoring divider structural circuit.

    **Inputs (76 total):**
    - a[31:0]: Dividend (32 bits)
    - b[31:0]: Divisor (32 bits)
    - op[2:0]: Operation type
    - dest_tag[5:0]: Physical register tag
    - start: Begin new division
    - clock, reset: Sequential control
    - one: Constant high (for Subtractor32 cin)

    **Outputs (40 total):**
    - result[31:0]: Division result
    - tag_out[5:0]: Pass-through destination tag
    - valid_out: Result ready this cycle
    - busy: Cannot accept new operations

    **Instances:**
    - Subtractor32: Trial subtraction (remainder_upper - divisor)

    **State registers (DFFs):**
    - remainder[63:0]: 64 DFFs
    - divisor[31:0]: 32 DFFs
    - quotient[31:0]: 32 DFFs
    - counter[4:0]: 5 DFFs
    - busy: 1 DFF
    - tag[5:0]: 6 DFFs
    - op[2:0]: 3 DFFs
    Total: 143 DFFs
-/
def mkDividerCircuit : Circuit :=
  -- ══════════════════════════════════════════════
  -- Input wires
  -- ══════════════════════════════════════════════
  let a_in := makeIndexedWires "a" 32
  let b_in := makeIndexedWires "b" 32
  let op_in := makeIndexedWires "op" 3
  let dest_tag := makeIndexedWires "dest_tag" 6
  let start := Wire.mk "start"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let one := Wire.mk "one"

  -- ══════════════════════════════════════════════
  -- Output wires
  -- ══════════════════════════════════════════════
  let result := makeIndexedWires "result" 32
  let tag_out := makeIndexedWires "tag_out" 6
  let valid_out := Wire.mk "valid_out"
  let busy_out := Wire.mk "busy"

  -- ══════════════════════════════════════════════
  -- State register wires (DFF outputs = current state)
  -- ══════════════════════════════════════════════
  let rem_q := makeIndexedWires "rem_q" 64    -- remainder register
  let div_q := makeIndexedWires "div_q" 32    -- divisor register
  let quo_q := makeIndexedWires "quo_q" 32    -- quotient register
  let cnt_q := makeIndexedWires "cnt_q" 5     -- counter register
  let busy_q := Wire.mk "busy_q"             -- busy flag
  let tag_q := makeIndexedWires "tag_q" 6     -- tag register
  let op_q := makeIndexedWires "op_q" 3       -- op register
  let a_neg_q := Wire.mk "a_neg_q"           -- dividend was negative (signed ops)
  let b_neg_q := Wire.mk "b_neg_q"           -- divisor was negative (signed ops)

  -- Next-state wires (DFF inputs)
  let rem_d := makeIndexedWires "rem_d" 64
  let div_d := makeIndexedWires "div_d" 32
  let quo_d := makeIndexedWires "quo_d" 32
  let cnt_d := makeIndexedWires "cnt_d" 5
  let busy_d := Wire.mk "busy_d"
  let tag_d := makeIndexedWires "tag_d" 6
  let op_d := makeIndexedWires "op_d" 3
  let a_neg_d := Wire.mk "a_neg_d"
  let b_neg_d := Wire.mk "b_neg_d"

  -- ══════════════════════════════════════════════
  -- Control signals (combinational)
  -- ══════════════════════════════════════════════
  let not_busy := Wire.mk "not_busy"
  let start_and_not_busy := Wire.mk "start_and_not_busy"   -- latch new inputs
  let cnt_is_31 := Wire.mk "cnt_is_31"                     -- counter == 31
  let done := Wire.mk "done"                                -- busy && cnt_is_31
  let not_done := Wire.mk "not_done"
  let busy_and_not_done := Wire.mk "busy_and_not_done"     -- continue iterating

  let ctrl_gates := [
    -- not_busy = !busy_q
    Gate.mkNOT busy_q not_busy,
    -- start_and_not_busy = start && !busy_q
    Gate.mkAND start not_busy start_and_not_busy,
    -- cnt_is_31: counter[4:0] == 5'b11111
    -- All 5 counter bits must be 1
    Gate.mkAND (cnt_q[0]!) (cnt_q[1]!) (Wire.mk "cnt_01"),
    Gate.mkAND (cnt_q[2]!) (cnt_q[3]!) (Wire.mk "cnt_23"),
    Gate.mkAND (Wire.mk "cnt_01") (Wire.mk "cnt_23") (Wire.mk "cnt_0123"),
    Gate.mkAND (Wire.mk "cnt_0123") (cnt_q[4]!) cnt_is_31,
    -- done = busy_q && cnt_is_31
    Gate.mkAND busy_q cnt_is_31 done,
    -- not_done = !done
    Gate.mkNOT done not_done,
    -- busy_and_not_done = busy_q && !done
    Gate.mkAND busy_q not_done busy_and_not_done
  ]

  -- ══════════════════════════════════════════════
  -- Busy flag next state
  -- ══════════════════════════════════════════════
  -- busy_d = start_and_not_busy || busy_and_not_done
  let busy_gates := [
    Gate.mkOR start_and_not_busy busy_and_not_done busy_d
  ]

  -- ══════════════════════════════════════════════
  -- Sign detection and input conditioning (for signed DIV/REM)
  -- is_signed = ~op_in[0] (DIV=4=100b, REM=6=110b have bit0=0)
  -- a_neg_start = a_in[31] & is_signed
  -- b_neg_start = b_in[31] & is_signed
  -- abs_a = a_neg_start ? -a_in : a_in
  -- abs_b = b_neg_start ? -b_in : b_in
  -- ══════════════════════════════════════════════
  let is_signed := Wire.mk "is_signed"
  let a_neg_start := Wire.mk "a_neg_start"
  let b_neg_start := Wire.mk "b_neg_start"

  let sign_detect_gates := [
    Gate.mkNOT (op_in[0]!) is_signed,
    Gate.mkAND (a_in[31]!) is_signed a_neg_start,
    Gate.mkAND (b_in[31]!) is_signed b_neg_start
  ]

  -- Conditional negation: abs = val XOR flag + flag (two's complement negate when flag=1)
  let abs_a := makeIndexedWires "abs_a" 32
  let abs_a_xor := makeIndexedWires "abs_a_xor" 32
  let abs_a_carry := makeIndexedWires "abs_a_carry" 33

  let abs_a_gates :=
    [Gate.mkBUF a_neg_start (abs_a_carry[0]!)] ++
    (List.range 32).flatMap (fun i =>
      [
        Gate.mkXOR (a_in[i]!) a_neg_start (abs_a_xor[i]!),
        Gate.mkXOR (abs_a_xor[i]!) (abs_a_carry[i]!) (abs_a[i]!),
        Gate.mkAND (abs_a_xor[i]!) (abs_a_carry[i]!) (abs_a_carry[i + 1]!)
      ]
    )

  let abs_b := makeIndexedWires "abs_b" 32
  let abs_b_xor := makeIndexedWires "abs_b_xor" 32
  let abs_b_carry := makeIndexedWires "abs_b_carry" 33

  let abs_b_gates :=
    [Gate.mkBUF b_neg_start (abs_b_carry[0]!)] ++
    (List.range 32).flatMap (fun i =>
      [
        Gate.mkXOR (b_in[i]!) b_neg_start (abs_b_xor[i]!),
        Gate.mkXOR (abs_b_xor[i]!) (abs_b_carry[i]!) (abs_b[i]!),
        Gate.mkAND (abs_b_xor[i]!) (abs_b_carry[i]!) (abs_b_carry[i + 1]!)
      ]
    )

  -- Sign register next-state: latch on start, hold otherwise
  let sign_mux_gates := [
    Gate.mkMUX a_neg_q a_neg_start start_and_not_busy a_neg_d,
    Gate.mkMUX b_neg_q b_neg_start start_and_not_busy b_neg_d
  ]

  -- ══════════════════════════════════════════════
  -- Shift logic: shifted_rem = rem_q << 1
  -- shifted_rem[0] = 0 (ground), shifted_rem[i] = rem_q[i-1] for i>0
  -- ══════════════════════════════════════════════
  let shifted_rem := makeIndexedWires "shifted_rem" 64

  -- shifted_rem[0] gets a constant 0. We use NOT(one) to produce 0.
  let zero_wire := Wire.mk "zero_from_one"
  let shift_gates :=
    [Gate.mkNOT one zero_wire,
     Gate.mkBUF zero_wire (shifted_rem[0]!)] ++
    -- shifted_rem[i] = rem_q[i-1] for i = 1..63
    (List.range 63).map (fun i =>
      Gate.mkBUF (rem_q[i]!) (shifted_rem[i + 1]!)
    )

  -- ══════════════════════════════════════════════
  -- Trial subtraction: trial = shifted_rem[63:32] - div_q
  -- Uses Subtractor32 instance
  -- ══════════════════════════════════════════════
  let trial_a := makeIndexedWires "trial_a" 32   -- upper 32 bits of shifted remainder
  let trial_diff := makeIndexedWires "trial_diff" 32
  let trial_borrow := Wire.mk "trial_borrow"

  -- Connect shifted_rem[63:32] to trial_a via BUF gates
  let trial_input_gates := (List.range 32).map (fun i =>
    Gate.mkBUF (shifted_rem[32 + i]!) (trial_a[i]!)
  )

  -- Subtractor32 instance: trial_diff = trial_a - div_q
  let sub_inst : CircuitInstance := {
    moduleName := "Subtractor32"
    instName := "u_trial_sub"
    portMap :=
      (trial_a.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (div_q.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("one", one)] ++
      (trial_diff.enum.map (fun ⟨i, w⟩ => (s!"diff_{i}", w))) ++
      [("borrow", trial_borrow)]
  }

  -- ══════════════════════════════════════════════
  -- Restore/Keep MUX for remainder update
  -- no_borrow = NOT(trial_borrow)
  -- When no borrow (trial >= 0): keep subtracted value
  -- When borrow (trial < 0): restore shifted value
  -- ══════════════════════════════════════════════
  let no_borrow := Wire.mk "no_borrow"
  let borrow_gates := [Gate.mkNOT trial_borrow no_borrow]

  -- Updated remainder when busy:
  -- new_rem[i] for i in 0..31 = shifted_rem[i] (lower 32 bits unchanged)
  -- new_rem[i] for i in 32..63 = MUX(shifted_rem[i], trial_diff[i-32], no_borrow)
  let new_rem := makeIndexedWires "new_rem" 64

  let rem_lower_gates := (List.range 32).map (fun i =>
    Gate.mkBUF (shifted_rem[i]!) (new_rem[i]!)
  )

  let rem_upper_mux_gates := (List.range 32).map (fun i =>
    -- MUX(in0=shifted_rem[32+i], in1=trial_diff[i], sel=no_borrow, out=new_rem[32+i])
    -- When no_borrow=1: out = trial_diff[i] (keep subtracted)
    -- When no_borrow=0: out = shifted_rem[32+i] (restore)
    Gate.mkMUX (shifted_rem[32 + i]!) (trial_diff[i]!) no_borrow (new_rem[32 + i]!)
  )

  -- ══════════════════════════════════════════════
  -- Quotient bit insertion
  -- When no_borrow: set quotient bit at position (31 - counter)
  -- This is complex in hardware; we use a simplified approach:
  -- For each quotient bit position i (0..31):
  --   quo_new[i] = quo_q[i] OR (no_borrow AND bit_select[i])
  -- where bit_select[i] = 1 iff (31 - counter) == i, i.e., counter == (31 - i)
  --
  -- To keep gate count manageable, we decode the counter to select which
  -- quotient bit to potentially set. We use a 5-to-32 decoder approach
  -- but implemented with AND gates for the specific bit positions.
  --
  -- Simplified approach: We generate the "counter matches position" signal
  -- for each bit by comparing counter to (31-i). Since counter is 5 bits,
  -- each comparison needs 5-input AND (with possibly inverted bits).
  -- ══════════════════════════════════════════════

  -- Generate counter bit and inverted counter bit wires
  let cnt_inv := makeIndexedWires "cnt_inv" 5
  let cnt_inv_gates := (List.range 5).map (fun i =>
    Gate.mkNOT (cnt_q[i]!) (cnt_inv[i]!)
  )

  -- For each quotient bit position i, decode whether counter == (31-i)
  -- counter value (31-i) in binary determines which cnt bits/inv to AND
  -- We need a 5-input AND for each position. Build with a tree of 2-input ANDs.
  let quo_new := makeIndexedWires "quo_new" 32

  -- Helper: select cnt_q[bit] or cnt_inv[bit] based on whether bit j of value v is 1
  let selectCntBit (v : Nat) (bit : Nat) : Wire :=
    if (v >>> bit) &&& 1 == 1 then cnt_q[bit]! else cnt_inv[bit]!

  -- Decode each position and update quotient
  let quo_decode_gates := (List.range 32).flatMap (fun i =>
    let target := 31 - i  -- counter value that selects this bit position
    -- 5-input AND via tree: ((b0 AND b1) AND (b2 AND b3)) AND b4
    let a01 := Wire.mk s!"qdec_{i}_01"
    let a23 := Wire.mk s!"qdec_{i}_23"
    let a0123 := Wire.mk s!"qdec_{i}_0123"
    let match_i := Wire.mk s!"qdec_{i}_match"
    let set_bit := Wire.mk s!"qset_{i}"
    [
      Gate.mkAND (selectCntBit target 0) (selectCntBit target 1) a01,
      Gate.mkAND (selectCntBit target 2) (selectCntBit target 3) a23,
      Gate.mkAND a01 a23 a0123,
      Gate.mkAND a0123 (selectCntBit target 4) match_i,
      -- set_bit = no_borrow AND match_i (set this quotient bit if trial succeeded)
      Gate.mkAND no_borrow match_i set_bit,
      -- quo_new[i] = quo_q[i] OR set_bit
      Gate.mkOR (quo_q[i]!) set_bit (quo_new[i]!)
    ]
  )

  -- ══════════════════════════════════════════════
  -- Counter increment logic
  -- ══════════════════════════════════════════════
  -- cnt_inc = cnt_q + 1 (5-bit increment)
  -- Simple ripple: each bit toggles when all lower bits are 1
  let cnt_inc := makeIndexedWires "cnt_inc" 5
  let cnt_carry := makeIndexedWires "cnt_carry" 6

  -- Use carry chain: carry[0] = 1 (always increment by 1)
  -- For each bit: sum[i] = cnt_q[i] XOR carry[i], carry[i+1] = cnt_q[i] AND carry[i]
  let cnt_inc_gates :=
    [Gate.mkBUF one (cnt_carry[0]!)] ++
    (List.range 5).flatMap (fun i =>
      [
        Gate.mkXOR (cnt_q[i]!) (cnt_carry[i]!) (cnt_inc[i]!),
        Gate.mkAND (cnt_q[i]!) (cnt_carry[i]!) (cnt_carry[i + 1]!)
      ]
    )

  -- ══════════════════════════════════════════════
  -- Next-state MUX logic for all state registers
  -- ══════════════════════════════════════════════

  -- Remainder next state:
  -- If start_and_not_busy: rem_d = {32'b0, a_in} (initialize with dividend)
  -- Else if busy_and_not_done: rem_d = new_rem (iteration result)
  -- Else: rem_d = rem_q (hold)
  --
  -- Two-level MUX:
  --   m1 = MUX(rem_q, new_rem, busy_and_not_done)    -- hold vs iterate
  --   rem_d = MUX(m1, init_val, start_and_not_busy)  -- iterate vs start

  -- Init remainder: lower 32 bits = abs_a (absolute value), upper 32 bits = 0
  let rem_init_lower := abs_a
  let rem_m1 := makeIndexedWires "rem_m1" 64

  let rem_mux_gates :=
    -- Lower 32 bits
    (List.range 32).flatMap (fun i => [
      -- m1[i] = MUX(rem_q[i], new_rem[i], busy_and_not_done)
      Gate.mkMUX (rem_q[i]!) (new_rem[i]!) busy_and_not_done (rem_m1[i]!),
      -- rem_d[i] = MUX(m1[i], abs_a[i], start_and_not_busy)
      Gate.mkMUX (rem_m1[i]!) (rem_init_lower[i]!) start_and_not_busy (rem_d[i]!)
    ]) ++
    -- Upper 32 bits (init to 0 on start, new_rem on iterate, hold otherwise)
    (List.range 32).flatMap (fun i => [
      -- m1[32+i] = MUX(rem_q[32+i], new_rem[32+i], busy_and_not_done)
      Gate.mkMUX (rem_q[32 + i]!) (new_rem[32 + i]!) busy_and_not_done (rem_m1[32 + i]!),
      -- rem_d[32+i] = MUX(m1[32+i], zero_wire, start_and_not_busy)
      -- upper bits init to 0
      Gate.mkMUX (rem_m1[32 + i]!) zero_wire start_and_not_busy (rem_d[32 + i]!)
    ])

  -- Divisor next state:
  -- If start_and_not_busy: div_d = abs_b (latch absolute value of divisor)
  -- Else: div_d = div_q (hold)
  let div_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (div_q[i]!) (abs_b[i]!) start_and_not_busy (div_d[i]!)
  )

  -- Quotient next state:
  -- If start_and_not_busy: quo_d = 0 (clear)
  -- Else if busy_and_not_done: quo_d = quo_new (with new bit set)
  -- Else: quo_d = quo_q (hold)
  let quo_m1 := makeIndexedWires "quo_m1" 32
  let quo_mux_gates := (List.range 32).flatMap (fun i => [
    Gate.mkMUX (quo_q[i]!) (quo_new[i]!) busy_and_not_done (quo_m1[i]!),
    Gate.mkMUX (quo_m1[i]!) zero_wire start_and_not_busy (quo_d[i]!)
  ])

  -- Counter next state:
  -- If start_and_not_busy: cnt_d = 0 (reset)
  -- Else if busy_and_not_done: cnt_d = cnt_inc (increment)
  -- Else: cnt_d = cnt_q (hold)
  let cnt_m1 := makeIndexedWires "cnt_m1" 5
  let cnt_mux_gates := (List.range 5).flatMap (fun i => [
    Gate.mkMUX (cnt_q[i]!) (cnt_inc[i]!) busy_and_not_done (cnt_m1[i]!),
    Gate.mkMUX (cnt_m1[i]!) zero_wire start_and_not_busy (cnt_d[i]!)
  ])

  -- Tag next state:
  -- If start_and_not_busy: tag_d = dest_tag (latch)
  -- Else: tag_d = tag_q (hold)
  let tag_mux_gates := (List.range 6).map (fun i =>
    Gate.mkMUX (tag_q[i]!) (dest_tag[i]!) start_and_not_busy (tag_d[i]!)
  )

  -- Op next state:
  -- If start_and_not_busy: op_d = op_in (latch)
  -- Else: op_d = op_q (hold)
  let op_mux_gates := (List.range 3).map (fun i =>
    Gate.mkMUX (op_q[i]!) (op_in[i]!) start_and_not_busy (op_d[i]!)
  )

  -- ══════════════════════════════════════════════
  -- DFF registers (all state elements)
  -- ══════════════════════════════════════════════
  let rem_dffs := (List.range 64).map (fun i =>
    Gate.mkDFF (rem_d[i]!) clock reset (rem_q[i]!)
  )
  let div_dffs := (List.range 32).map (fun i =>
    Gate.mkDFF (div_d[i]!) clock reset (div_q[i]!)
  )
  let quo_dffs := (List.range 32).map (fun i =>
    Gate.mkDFF (quo_d[i]!) clock reset (quo_q[i]!)
  )
  let cnt_dffs := (List.range 5).map (fun i =>
    Gate.mkDFF (cnt_d[i]!) clock reset (cnt_q[i]!)
  )
  let busy_dff := [Gate.mkDFF busy_d clock reset busy_q]
  let tag_dffs := (List.range 6).map (fun i =>
    Gate.mkDFF (tag_d[i]!) clock reset (tag_q[i]!)
  )
  let op_dffs := (List.range 3).map (fun i =>
    Gate.mkDFF (op_d[i]!) clock reset (op_q[i]!)
  )
  let sign_dffs := [
    Gate.mkDFF a_neg_d clock reset a_neg_q,
    Gate.mkDFF b_neg_d clock reset b_neg_q
  ]

  -- ══════════════════════════════════════════════
  -- Result selection MUX (raw, before sign correction)
  -- op_q[1] selects between quotient (op=4,5 -> bit1=0) and remainder (op=6,7 -> bit1=1)
  -- ══════════════════════════════════════════════
  let raw_result := makeIndexedWires "raw_result" 32
  let result_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (quo_q[i]!) (rem_q[32 + i]!) (op_q[1]!) (raw_result[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Result sign correction
  -- For signed ops (~op_q[0]):
  --   DIV (op_q[1]=0): negate if a_neg XOR b_neg
  --   REM (op_q[1]=1): negate if a_neg
  -- needs_negate = ~op_q[0] & (op_q[1] ? a_neg_q : (a_neg_q XOR b_neg_q))
  -- ══════════════════════════════════════════════
  let is_signed_op := Wire.mk "is_signed_op"
  let sign_xor := Wire.mk "sign_xor"       -- a_neg XOR b_neg (for DIV)
  let negate_sel := Wire.mk "negate_sel"    -- MUX(sign_xor, a_neg_q, op_q[1])
  let needs_negate := Wire.mk "needs_negate"

  let sign_correct_ctrl := [
    Gate.mkNOT (op_q[0]!) is_signed_op,
    Gate.mkXOR a_neg_q b_neg_q sign_xor,
    -- For DIV (bit1=0): use sign_xor. For REM (bit1=1): use a_neg_q
    Gate.mkMUX sign_xor a_neg_q (op_q[1]!) negate_sel,
    Gate.mkAND is_signed_op negate_sel needs_negate
  ]

  -- Conditional negation of raw_result: result = raw XOR flag + flag
  let res_xor := makeIndexedWires "res_xor" 32
  let res_carry := makeIndexedWires "res_carry" 33

  let sign_correct_gates :=
    [Gate.mkBUF needs_negate (res_carry[0]!)] ++
    (List.range 32).flatMap (fun i =>
      [
        Gate.mkXOR (raw_result[i]!) needs_negate (res_xor[i]!),
        Gate.mkXOR (res_xor[i]!) (res_carry[i]!) (result[i]!),
        Gate.mkAND (res_xor[i]!) (res_carry[i]!) (res_carry[i + 1]!)
      ]
    )

  -- ══════════════════════════════════════════════
  -- Output connections
  -- ══════════════════════════════════════════════

  -- tag_out = tag_q (pass through latched tag)
  let tag_out_gates := (List.range 6).map (fun i =>
    Gate.mkBUF (tag_q[i]!) (tag_out[i]!)
  )

  -- valid_out = done (result valid on the cycle counter hits 31)
  let valid_gate := [Gate.mkBUF done valid_out]

  -- busy output = busy_q
  let busy_gate := [Gate.mkBUF busy_q busy_out]

  -- ══════════════════════════════════════════════
  -- Assemble all gates
  -- ══════════════════════════════════════════════
  let all_gates :=
    ctrl_gates ++
    busy_gates ++
    sign_detect_gates ++
    abs_a_gates ++
    abs_b_gates ++
    sign_mux_gates ++
    shift_gates ++
    trial_input_gates ++
    borrow_gates ++
    rem_lower_gates ++
    rem_upper_mux_gates ++
    cnt_inv_gates ++
    quo_decode_gates ++
    cnt_inc_gates ++
    rem_mux_gates ++
    div_mux_gates ++
    quo_mux_gates ++
    cnt_mux_gates ++
    tag_mux_gates ++
    op_mux_gates ++
    rem_dffs ++
    div_dffs ++
    quo_dffs ++
    cnt_dffs ++
    busy_dff ++
    tag_dffs ++
    op_dffs ++
    sign_dffs ++
    result_mux_gates ++
    sign_correct_ctrl ++
    sign_correct_gates ++
    tag_out_gates ++
    valid_gate ++
    busy_gate

  { name := "Divider32"
    inputs := a_in ++ b_in ++ op_in ++ dest_tag ++ [start, clock, reset, one]
    outputs := result ++ tag_out ++ [valid_out, busy_out]
    gates := all_gates
    instances := [sub_inst]
    -- V2 codegen annotations
    signalGroups := [
      { name := "a", width := 32, wires := a_in },
      { name := "b", width := 32, wires := b_in },
      { name := "op", width := 3, wires := op_in },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 32, wires := result },
      { name := "tag_out", width := 6, wires := tag_out }
    ]
  }

/-- Convenience definition for the divider circuit. -/
def divider32Circuit : Circuit := mkDividerCircuit

end Shoumei.Circuits.Sequential

# Proof Strategies for Parameterized Circuits

## Problem Statement

Our DSL proofs fall into two categories:

1. **Concrete proofs** — fixed parameters (e.g., `mkRegister4`). These work with
   `native_decide` because LEAN can evaluate the entire circuit into a known
   boolean expression and brute-force check it.

2. **General proofs** — arbitrary parameters (e.g., `mkRegisterN n` for all `n`).
   `native_decide` cannot handle these because it needs to evaluate symbolic
   expressions. These are the proofs currently deferred with `sorry` or axioms.

This doc describes two approaches for closing the gap.

---

## Approach 1: Structural Induction + List Lemmas

### Idea

The register is N parallel DFFs built with `List.zipWith`. The evaluator
(`evalCycleSequential`) processes them with `foldl`, `filterMap`, and `find?`.
All of these are recursive list operations, so their properties follow by
induction on the list structure — no special solver needed.

### What Needs Proving

Take `registerN_reset` as the running example: "when reset is high, all output
bits become false."

The evaluation chain is:

```
mkRegisterN n
  → gates = List.zipWith mkDFF d_wires q_wires     -- N DFF gates
  → evalCycleSequential processes the gates:
      1. getDFFOutputs → filters for DFF gates, maps to .output
      2. mergeStateIntoEnv → makes previous state available
      3. foldl over gates → skips DFFs (sequential), evaluates combinational
      4. filterMap over gates → evaluates each DFF via evalDFF
      5. updateState → folds (wire, value) pairs into next state
```

To prove the final state has `q_i = false` for all `i < n`, we need a chain of
lemmas about how data flows through these list operations.

### Required Lemmas

#### L1: `makeIndexedWires` produces distinct wires

```lean
lemma makeIndexedWires_length (name : String) (n : Nat) :
    (makeIndexedWires name n).length = n := by
  simp [makeIndexedWires, List.length_map, List.length_range]

lemma makeIndexedWires_get (name : String) (n : Nat) (i : Nat) (hi : i < n) :
    (makeIndexedWires name n)[i]? = some (Wire.mk s!"{name}{i}") := by
  simp [makeIndexedWires, List.getElem?_map, List.getElem?_range, hi]

lemma makeIndexedWires_nodup (name : String) (n : Nat) :
    (makeIndexedWires name n).Nodup := by
  -- Requires: String.append is injective in the suffix,
  -- and Nat.repr (toString) is injective.
  -- Nat.repr injectivity: toString i = toString j → i = j
  sorry -- see "String Injectivity" section below
```

The `Nodup` lemma is the hardest piece. It reduces to proving that
`s!"{name}{i}" = s!"{name}{j}" → i = j`, which requires `Nat.repr` (or
`Nat.toDigits`) injectivity. This is true but may not exist as a ready-made
lemma in Lean 4 or Mathlib. Options:

- **Prove it directly.** `Nat.repr` produces decimal digit strings. Injectivity
  follows from the uniqueness of decimal representation. This is ~20-30 lines
  of proof about `Nat.toDigits`.
- **Use `Decidable` + `native_decide` for bounded cases.** If we only need
  `n ≤ 1024` or similar, we can sidestep full generality.
- **Assume it as an axiom** and move on (pragmatic, low risk).

#### L2: `zipWith` preserves length and element access

```lean
-- Already in Lean 4 stdlib (List.length_zipWith, List.getElem?_zipWith)
-- but worth stating for clarity:
lemma register_gates_length (n : Nat) :
    (mkRegisterN n).gates.length = n := by
  simp [mkRegisterN, List.length_zipWith, makeIndexedWires_length]

lemma register_gate_i (n : Nat) (i : Nat) (hi : i < n) :
    (mkRegisterN n).gates[i]? = some (Gate.mkDFF
      (Wire.mk s!"d{i}") (Wire.mk "clock") (Wire.mk "reset") (Wire.mk s!"q{i}")) := by
  simp [mkRegisterN, makeIndexedWires, List.getElem?_zipWith,
        List.getElem?_map, List.getElem?_range, hi]
```

#### L3: All gates are DFFs, so `filterMap` returns all of them

```lean
lemma register_all_dff (n : Nat) :
    ((mkRegisterN n).gates.filter (fun g => g.gateType == GateType.DFF)).length = n := by
  -- Every gate in the register is a DFF by construction (mkDFF sets gateType := .DFF)
  -- So filter keeps everything, length = n
  simp [mkRegisterN, makeIndexedWires]
  induction n with
  | zero => simp [List.zipWith, List.filter]
  | succ n ih => simp [List.range_succ, List.map, List.zipWith, List.filter, Gate.mkDFF, ih]
```

#### L4: `evalDFF` under reset returns `false`

```lean
lemma evalDFF_reset (g : Gate) (env : Env) (h : g.gateType = GateType.DFF)
    (d clk rst : Wire) (hinp : g.inputs = [d, clk, rst]) (hrst : env rst = true) :
    evalDFF g env = false := by
  simp [evalDFF, h, hinp, hrst]
```

This is trivial — it's just unfolding the `if env reset then false else env d`
branch.

#### L5: `updateState` with matching key returns the value

```lean
lemma updateState_found (state : State) (updates : List (Wire × Bool))
    (w : Wire) (v : Bool) (h : updates.find? (fun p => p.1 == w) = some (w, v)) :
    updateState state updates w = v := by
  simp [updateState, h]

lemma updateState_not_found (state : State) (updates : List (Wire × Bool))
    (w : Wire) (h : updates.find? (fun p => p.1 == w) = none) :
    updateState state updates w = state w := by
  simp [updateState, h]
```

The harder part: proving that `find?` *does* find `q_i` in the update list.
This connects back to `Nodup` — since the wire names are distinct, each `q_i`
appears exactly once in the filterMap output, so `find?` succeeds.

### Putting It Together

```lean
theorem registerN_reset (n : Nat) (d_vals : List Bool) (h : d_vals.length = n) :
    let env := makeRegisterEnv n d_vals true
    let (nextState, _) := evalCycleSequential (mkRegisterN n) initState env
    ∀ i, i < n → nextState (Wire.mk s!"q{i}") = false := by
  intro i hi
  simp [evalCycleSequential, mkRegisterN]
  -- 1. The combinational foldl is a no-op (all gates are DFFs, all skipped)
  -- 2. filterMap produces [(q_0, false), (q_1, false), ..., (q_{n-1}, false)]
  --    because evalDFF returns false under reset (L4)
  -- 3. updateState with these pairs: querying q_i finds (q_i, false)
  --    because q_i is in the list (L2) and names are distinct (L1)
  sorry -- placeholder for the assembled proof
```

### Effort Estimate

| Lemma | Difficulty | Lines (approx) |
|-------|-----------|----------------|
| `makeIndexedWires_length` | Easy | 2 |
| `makeIndexedWires_get` | Easy | 3 |
| `makeIndexedWires_nodup` | Medium-hard | 20-30 |
| `register_gates_length` | Easy | 3 |
| `register_gate_i` | Easy | 5 |
| `register_all_dff` | Easy (induction) | 8 |
| `evalDFF_reset` | Trivial | 2 |
| `updateState_found/not_found` | Easy | 5 |
| `find?` hits the right entry | Medium | 15-20 |
| **Main theorems** (reset, capture, independence) | Medium | 15-25 each |
| **Total** | | **~100-130 lines** |

The `makeIndexedWires_nodup` lemma (String/Nat injectivity) is the single
hardest piece. Everything else is standard list induction.

### What This Unlocks

Once the lemma library is in place, the same infrastructure proves:

- `registerN_reset` — reset zeroes all bits
- `registerN_capture` — each `q_i` captures `d_i` when reset is low
- `registerN_bit_independence` — changing `d_i` only affects `q_i`
- `registerWidth_correct` — `registerWidth (mkRegisterN n) = n`

And generalizes to other parameterized circuits built with `makeIndexedWires`
(QueueN, RAT, FreeList, etc.).

### Applicability to Other Deferred Proofs

The RenameStage axioms (`stall_proof`, `rat_forwarding_proof`, etc.) hit
recursion depth limits rather than the "arbitrary N" problem. Those are more
likely solvable by:

1. Manually unfolding the evaluation with `simp` + `split` instead of
   `native_decide`
2. Breaking the circuit into sub-lemmas (e.g., prove the free list check
   independently, then compose)
3. Increasing `maxRecDepth` further (brute force, but sometimes sufficient)

The list lemma library from this approach still helps — the same `updateState`,
`filterMap`, and `find?` reasoning appears everywhere.

---

## Approach 2: BitVec Semantic Bridge

### Idea

Lean 4 has built-in `BitVec n` types and two powerful decision procedures:

- **`bv_decide`** — a SAT-based bitblasting tactic that decides quantifier-free
  bitvector formulas. Handles arithmetic, bitwise ops, shifts, comparisons.
- **`bv_omega`** — linear arithmetic over bitvectors (extension of `omega` to
  fixed-width integers).

Our DSL currently represents everything as `Bool` and `List Bool`. A `BitVec`
bridge layer would let us state and prove theorems at the word level instead of
reasoning bit-by-bit.

### Architecture

```
Current DSL types              BitVec bridge               Theorems
──────────────────          ─────────────────────      ─────────────────
Wire → Bool (Env/State)  →  BitVec n interpretation  →  bv_decide proofs
List Bool (values)        →  BitVec n conversion      →  bv_omega proofs
Gate-level evaluation     →  Word-level semantics     →  Word-level properties
```

The bridge doesn't replace the gate-level DSL — it provides an alternative
semantic domain for stating and proving properties.

### Core Definitions

```lean
import Mathlib.Data.BitVec

-- Interpret N register outputs as a BitVec
def registerState_toBitVec (state : State) (n : Nat) : BitVec n :=
  BitVec.ofFn (fun (i : Fin n) => state (Wire.mk s!"q{i.val}"))

-- Interpret N input values as a BitVec
def inputList_toBitVec (vals : List Bool) (n : Nat) (h : vals.length = n) : BitVec n :=
  BitVec.ofFn (fun (i : Fin n) => vals[i.val]'(by omega))

-- Word-level register semantics (what the register "should" do)
def registerSemantics (d : BitVec n) (reset : Bool) : BitVec n :=
  if reset then 0#n else d
```

### Proof Structure

The proof works in two layers:

**Layer 1: Bridge correctness** — prove that the `BitVec` interpretation
faithfully reflects the gate-level evaluation.

```lean
-- "The BitVec interpretation of the register's next state equals
--  the word-level semantics applied to the BitVec interpretation of inputs"
theorem register_bitVec_correct (n : Nat) (d_vals : List Bool)
    (h : d_vals.length = n) (reset : Bool) :
    let env := makeRegisterEnv n d_vals reset
    let (nextState, _) := evalCycleSequential (mkRegisterN n) initState env
    registerState_toBitVec nextState n =
      registerSemantics (inputList_toBitVec d_vals n h) reset := by
  -- This proof still requires the list induction from Approach 1
  -- to connect gate-level eval to the BitVec interpretation.
  sorry
```

**Layer 2: Word-level properties** — once in `BitVec` land, properties become
trivial for `bv_decide`.

```lean
-- Reset produces zero
theorem register_reset_bv (d : BitVec n) :
    registerSemantics d true = 0#n := by
  simp [registerSemantics]

-- Capture preserves input
theorem register_capture_bv (d : BitVec n) :
    registerSemantics d false = d := by
  simp [registerSemantics]

-- ALU add is correct (this is where BitVec really shines)
theorem alu_add_correct (a b : BitVec 32) :
    aluSemantics .ADD a b = a + b := by
  bv_decide

-- Shift left by constant
theorem sll_correct (a : BitVec 32) (shamt : BitVec 5) :
    aluSemantics .SLL a (shamt.zeroExtend 32) = a <<< shamt.toNat := by
  bv_omega
```

### Honest Assessment

The bridge correctness proof (Layer 1) **still requires the list induction from
Approach 1**. You can't avoid reasoning about `filterMap`, `updateState`, and
`find?` to connect gate-level evaluation to the `BitVec` interpretation. The
bridge doesn't eliminate that work — it moves the payoff to Layer 2.

Where the BitVec approach pays for itself:

| Domain | Induction alone | With BitVec bridge |
|--------|----------------|--------------------|
| Register reset/capture | Provable | Provable (same effort for bridge, trivial for property) |
| Bit independence | Medium proof | Trivial: bit extraction from `BitVec` |
| ALU correctness | Very hard (32 parallel bit slices) | `bv_decide` handles it automatically |
| Adder carry propagation | Induction on bit position | `bv_omega` on `BitVec 32` addition |
| Shifter barrel logic | Complex case splits | `bv_decide` on shift operations |
| Comparator correctness | Induction on bit pairs | `bv_omega` on `BitVec` ordering |

The break-even point is around ALU/arithmetic proofs. For simple
reset/capture properties on registers, the bridge adds overhead without much
benefit. For proving that a 32-bit adder circuit actually computes `a + b`,
the bridge is dramatically easier.

### Required Infrastructure

1. **`BitVec.ofFn`** — construct a `BitVec n` from a function `Fin n → Bool`.
   Available in Mathlib.

2. **Interpretation functions** — `registerState_toBitVec`, `aluOutput_toBitVec`,
   etc. One per circuit type. Small definitions (~5 lines each).

3. **Bridge correctness theorems** — one per circuit type, connecting gate-level
   eval to word-level semantics. These are the hard proofs (requiring Approach 1
   lemmas).

4. **Word-level semantics** — `registerSemantics`, `aluSemantics`, etc.
   Clean functional definitions of what each circuit should do.

5. **Mathlib dependency** — `BitVec` and `bv_decide` are in Lean 4 core, but
   some convenience lemmas are in Mathlib. Adding Mathlib as a dependency
   increases build times significantly.

### Effort Estimate

| Component | Lines (approx) |
|-----------|----------------|
| Interpretation functions | 30-50 |
| Word-level semantics | 30-50 |
| Bridge correctness (register) | 40-60 (includes Approach 1 lemmas) |
| Bridge correctness (ALU) | 60-80 |
| Word-level property proofs | 5-10 each (often one-liners) |
| **Total for register + ALU** | **~200-300 lines** |

### What This Unlocks

Once the bridge exists for a circuit type, *all* word-level properties become
almost free. For ALU32 with 10 operations, that's potentially 10+ theorems
discharged by `bv_decide` with no manual proof effort.

The bridge also enables **compositional reasoning at the word level**: if the
register correctly captures a `BitVec 32`, and the ALU correctly computes
`a + b` as `BitVec 32`, then the datapath correctly computes
`reg_out = alu(reg_in_a, reg_in_b)` — all at the `BitVec` level without
touching individual bits.

---

## Recommendation

**Do Approach 1 first.** The list lemma library is needed regardless — even the
BitVec bridge depends on it. It unblocks the immediate `sorry` proofs in
`RegisterProofs.lean` and generalizes to QueueN, RAT, and other parameterized
circuits.

**Add the BitVec bridge later**, when tackling ALU/arithmetic correctness proofs
where `bv_decide` provides the most leverage. The register is not the best
motivating example for BitVec — the ALU is.

### Priority Order

1. `makeIndexedWires` lemmas (length, get, nodup)
2. `registerN_reset` and `registerN_capture` via induction
3. `registerWidth_correct` (easy corollary)
4. Apply same lemmas to QueueN proofs
5. BitVec bridge for ALU32 (where `bv_decide` saves the most work)
6. BitVec bridge for register (for compositional word-level reasoning)

---

## References

- [Lean 4 `BitVec` docs](https://leanprover-community.github.io/mathlib4_docs/Init/Data/BitVec/Basic.html)
- [`bv_decide` RFC and implementation](https://github.com/leanprover/lean4/pull/4along) — SAT-based bitblasting
- [`omega` and `bv_omega` in Lean 4](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Omega.html)
- [Mathlib `BitVec` extensions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/BitVec.html)

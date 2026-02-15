# Design: Verified Circuit-to-BitVec Compiler

## Status: Phase 1 & 3 (partial) complete
## Author: (generated)
## Date: 2025-02 (updated 2026-02)

---

## 1. Problem Statement

The Shoumei RTL project has a proof gap. There are three things defined in Lean:

1. **Behavioral models** -- pure functional specs (`aluSemantics`, `QueueState`, `fetchStep`)
2. **Structural circuits** -- `Circuit` values built from `Gate`, `Wire`, `CircuitInstance`
3. **Evaluation semantics** -- `evalCircuit`/`evalCycleSequential` in `Semantics.lean`

The evaluation semantics *can* connect (1) and (2): given a `Circuit` and inputs, `evalCircuit`
computes outputs by folding over the gate list. In principle, proving
`evalCircuit myCircuit inputs = expectedOutputs` proves the circuit implements the spec.

In practice, this works for the full adder (5 gates, 3 boolean inputs) via `native_decide`.
It does not work for anything larger. The ALU has ~1500 gates and 68 input bits. Lean's kernel
cannot reduce a 1500-step `List.foldl` of `updateEnv` calls into a closed-form expression in
reasonable time.

**Current state of the gap:**

| File | Axiom | What it claims |
|------|-------|----------------|
| `ALUBitVecBridge.lean` | `alu32_bridge` | `evalALU32 a b op = aluSemantics op a b` |
| `ALUBitVecBridge.lean` | `alu32_concrete_add` (+ 9 more) | `evalALU32 5 3 0x0 = 8` etc. |
| `FetchProofs.lean` | `mkFetchStage_implements_fetchStep` | Proves `True` (placeholder) |
| `CPUProofs.lean` | `mkCPU_RV32I_implements_cpuStep` | Circuit implements ISA step |
| `RegisterLemmas.lean` | `natToString_injective` | Wire name distinctness |
| `Compositional.lean` | `construction_deterministic` | `f n = f n` (trivially true) |
| `RenameStageProofs.lean` | 7 axioms | All prove `True` |
| `ReservationStation.lean` | 9 axioms | Behavioral RS properties |
| `Arbiter.lean` | 5 axioms | Priority encoder properties |

None of these axioms are proven. The actual verification comes from Yosys LEC (external SAT-based
equivalence checking between Lean-generated and Chisel-generated SystemVerilog).

**Goal of this workstream:** Eliminate axioms by building infrastructure that lets Lean prove
`evalCircuit c inputs = spec inputs` for circuits with hundreds to thousands of gates.

---

## 2. Why `evalCircuit` Doesn't Scale

```lean
def evalCircuit (c : Circuit) (inputEnv : Env) : Env :=
  c.gates.foldl (fun env gate =>
    let result := evalGate gate env
    updateEnv env gate.output result
  ) inputEnv
```

For a concrete circuit, `c.gates` is a literal `List Gate` with N elements.
`evalCircuit` unfolds to:

```
updateEnv (updateEnv (updateEnv inputEnv w0 v0) w1 v1) ... wN vN
```

Each `updateEnv` wraps a conditional: `fun w' => if w' == w then v else prev w'`.
After N gates, looking up any wire requires traversing N conditionals. The kernel
term for the full environment is O(N^2) in size.

For the ALU32 with ~1500 gates, this is ~2.25 million conditional branches in the
kernel term. `native_decide` tries to compile this to native code, which either
times out or exhausts memory.

**The problem is representation, not computation.** The actual circuit evaluation is
fast (microseconds in any real language). The problem is that Lean's kernel represents
intermediate environments as nested closures, and the term grows quadratically.

---

## 3. Proposed Solution: Compile Circuit to BitVec Expression

### Core Idea

Instead of *interpreting* a `Circuit` gate-by-gate through `evalCircuit` (building up
a huge `Env` closure), *compile* the circuit into a direct `BitVec` expression that
`bv_decide` can handle.

```
evalCircuit (concrete circuit) (concrete input encoding)
    ↓ reflection
BitVec expression over symbolic inputs
    ↓ bv_decide
Proven equal to spec
```

### What This Looks Like

Define a function `compileCircuit` that takes a `Circuit` and produces a function
from input `BitVec`s to output `BitVec`s, without going through `Env`:

```lean
-- Target: a pure BitVec function equivalent to evalCircuit
-- For a circuit with 32-bit inputs a, b and 4-bit opcode:
-- compileALU32 : BitVec 32 → BitVec 32 → BitVec 4 → BitVec 32

-- Then prove:
theorem alu32_compiled_correct (a b : BitVec 32) (op : BitVec 4) :
    compileALU32 a b op = aluSemantics (ALUOp.ofOpcode op) a b := by
  bv_decide  -- SAT bitblasting handles this
```

The key insight: `bv_decide` is *designed* for exactly this problem. It bitblasts
`BitVec` expressions into SAT and solves them. A 32-bit ALU with 68 input bits
produces a SAT problem with ~68 variables and ~1500 clauses -- trivial for any
modern SAT solver.

The hard part is building the compiler and proving it equivalent to `evalCircuit`.

---

## 4. Architecture

### 4.1 Compilation Strategy

The compiler operates on a `Circuit` value and produces `BitVec` expressions.
Internally, it maintains a map from `Wire` to `BitVec 1` expressions (single bits),
processing gates in order.

```
Input: Circuit { gates: [g0, g1, ..., gN], inputs: [...], outputs: [...] }

Step 1: Initialize wire map from circuit inputs
  "a_0" → a.getLsbD 0
  "a_1" → a.getLsbD 1
  ...
  "op_0" → op.getLsbD 0
  ...

Step 2: Process each gate, extending the wire map
  Gate.AND [w1, w2] out → wireMap[out] := wireMap[w1] && wireMap[w2]
  Gate.OR  [w1, w2] out → wireMap[out] := wireMap[w1] || wireMap[w2]
  Gate.NOT [w1]     out → wireMap[out] := !wireMap[w1]
  Gate.XOR [w1, w2] out → wireMap[out] := wireMap[w1] ^^ wireMap[w2]
  Gate.BUF [w1]     out → wireMap[out] := wireMap[w1]
  Gate.MUX [i0,i1,s] out → wireMap[out] := if wireMap[s] then wireMap[i1] else wireMap[i0]

Step 3: Read output wires and pack into BitVec
  result := BitVec.ofFn (fun i => wireMap["result_{i}"])
```

This is essentially what `evalCircuit` does, but instead of building up an `Env`
(function closure), it builds a `BitVec` expression tree. The expression tree is
what `bv_decide` consumes.

### 4.2 Components

```
┌─────────────────────────────────────────────────────────────────────┐
│                        Proof Infrastructure                         │
│                                                                     │
│  ┌──────────────┐    ┌──────────────────┐    ┌───────────────────┐  │
│  │  WireMap      │    │ compileGate      │    │ compileCircuit    │  │
│  │              │    │                  │    │                   │  │
│  │ Wire → Bool  │───▶│ Gate → WireMap   │───▶│ Circuit → BitVec  │  │
│  │ (HashMap or  │    │ → WireMap        │    │ function          │  │
│  │  assoc list) │    │                  │    │                   │  │
│  └──────────────┘    └──────────────────┘    └──────────────────-┘  │
│         │                     │                       │             │
│         ▼                     ▼                       ▼             │
│  ┌──────────────┐    ┌──────────────────┐    ┌───────────────────┐  │
│  │ Correctness  │    │ Gate-level       │    │ Circuit-level     │  │
│  │ of WireMap   │    │ correctness      │    │ correctness       │  │
│  │ operations   │    │ lemma            │    │ theorem           │  │
│  └──────────────┘    └──────────────────┘    └───────────────────┘  │
│                                                       │             │
│                                                       ▼             │
│                                              ┌───────────────────┐  │
│                                              │ Bridge theorem:   │  │
│                                              │ compileCircuit c  │  │
│                                              │ = evalCircuit c   │  │
│                                              └───────────────────┘  │
└─────────────────────────────────────────────────────────────────────┘
```

### 4.3 File Layout

```
lean/Shoumei/Reflection/
  WireMap.lean          -- Wire → Bool map with lookup/insert, correctness lemmas
  CompileGate.lean      -- Single gate compilation + correctness
  CompileCircuit.lean   -- Full circuit compilation via foldl + main theorem
  BitVecPacking.lean    -- BitVec ↔ wire bindings (generalize existing ALUBitVecBridge helpers)
  Automation.lean       -- (optional) Lean metaprogramming to auto-generate bridge theorems
```

---

## 5. Detailed Design

### 5.1 WireMap: A Proof-Friendly Wire-to-Bool Map

The existing `Env` type is `Wire → Bool` -- an opaque function. This is fine for
computation but terrible for proofs because Lean can't inspect the structure of a
function to determine what it maps.

We need a concrete map type that supports structural reasoning:

```lean
-- Option A: Association list (simple, proof-friendly)
abbrev WireMap := List (Wire × Bool)

def WireMap.lookup (m : WireMap) (w : Wire) : Bool :=
  match m.find? (fun p => p.1 == w) with
  | some (_, v) => v
  | none => false

def WireMap.insert (m : WireMap) (w : Wire) (v : Bool) : WireMap :=
  (w, v) :: m
```

```lean
-- Option B: Indexed array (faster computation, harder proofs)
-- Assign each wire an index during circuit construction, use Array Bool
structure IndexedWireMap where
  wires : Array (Wire × Bool)
  index : Wire → Option Nat  -- precomputed index lookup
```

**Recommendation: Option A.** Association lists are simple, and `List.find?` has
good lemma support in Lean 4's stdlib. The performance concern is irrelevant --
we're building proof terms, not running simulations. What matters is that we can
prove `lookup (insert m w v) w = v` and `lookup (insert m w v) w' = lookup m w'`
when `w ≠ w'`.

Key lemmas needed:

```lean
theorem WireMap.lookup_insert_eq (m : WireMap) (w : Wire) (v : Bool) :
    (m.insert w v).lookup w = v

theorem WireMap.lookup_insert_ne (m : WireMap) (w w' : Wire) (v : Bool) (h : w ≠ w') :
    (m.insert w v).lookup w' = m.lookup w'
```

These are standard association list lemmas. The `Wire` `BEq` instance plus
`DecidableEq` (derivable) make this straightforward.

### 5.2 Gate Compilation

```lean
def compileGate (m : WireMap) (g : Gate) : WireMap :=
  let result := match g.gateType with
  | .AND => match g.inputs with
    | [i0, i1] => m.lookup i0 && m.lookup i1
    | _ => false
  | .OR => match g.inputs with
    | [i0, i1] => m.lookup i0 || m.lookup i1
    | _ => false
  | .NOT => match g.inputs with
    | [i0] => !m.lookup i0
    | _ => false
  | .XOR => match g.inputs with
    | [i0, i1] => xor (m.lookup i0) (m.lookup i1)
    | _ => false
  | .BUF => match g.inputs with
    | [i0] => m.lookup i0
    | _ => false
  | .MUX => match g.inputs with
    | [in0, in1, sel] => if m.lookup sel then m.lookup in1 else m.lookup in0
    | _ => false
  | .DFF | .DFF_SET => false
  m.insert g.output result
```

This is structurally identical to `evalGate` + `updateEnv`, just operating on
`WireMap` instead of `Env`. The correctness lemma states this equivalence:

```lean
theorem compileGate_correct (m : WireMap) (g : Gate) (env : Env)
    (h_equiv : ∀ w, m.lookup w = env w) :
    ∀ w, (compileGate m g).lookup w = (updateEnv env g.output (evalGate g env)) w
```

This follows directly from `WireMap.lookup_insert_eq`, `WireMap.lookup_insert_ne`,
and the fact that `compileGate` and `evalGate` compute the same boolean expression
from the same inputs (by the equivalence hypothesis `h_equiv`).

### 5.3 Circuit Compilation

```lean
def compileCircuit (c : Circuit) (initMap : WireMap) : WireMap :=
  c.gates.foldl compileGate initMap
```

The main correctness theorem:

```lean
theorem compileCircuit_correct (c : Circuit) (initMap : WireMap) (inputEnv : Env)
    (h_equiv : ∀ w, initMap.lookup w = inputEnv w) :
    ∀ w, (compileCircuit c initMap).lookup w = evalCircuit c inputEnv w
```

**Proof sketch:** By induction on `c.gates` (it's a `List.foldl`). The base case
is `h_equiv`. The inductive step uses `compileGate_correct` to show that after
processing one gate, the equivalence still holds for the extended map/env.

This is the core theorem. Once proven, it says: *for any circuit, compiling it to
a WireMap gives the same results as interpreting it through evalCircuit.*

### 5.4 BitVec Packing/Unpacking

Generalize the existing helpers from `ALUBitVecBridge.lean`:

```lean
-- Create initial WireMap from BitVec inputs
def packInputs (names : List (String × Nat)) (inputs : List (Σ n, BitVec n)) : WireMap :=
  names.zip inputs |>.foldl (fun m ((name, width), ⟨_, bv⟩) =>
    List.range width |>.foldl (fun m' i =>
      m'.insert (Wire.mk s!"{name}_{i}") (bv.getLsbD i)
    ) m
  ) []

-- Read output BitVec from WireMap
def readOutput (m : WireMap) (name : String) (width : Nat) : BitVec width :=
  BitVec.ofFn (fun (i : Fin width) => m.lookup (Wire.mk s!"{name}_{i}"))
```

The naming convention `name_{i}` already exists throughout the codebase
(`makeIndexedWires` in `DSL/Interfaces.lean`), so this is compatible.

### 5.5 End-to-End Bridge Theorem (Example: ALU32)

```lean
-- Step 1: Define the compiled version
def alu32Compiled (a b : BitVec 32) (op : BitVec 4) : BitVec 32 :=
  let initMap := packInputs
    [("a", 32), ("b", 32), ("op", 4)]
    [⟨32, a⟩, ⟨32, b⟩, ⟨4, op⟩]
  let initMap' := initMap.insert (Wire.mk "zero") false
                               |>.insert (Wire.mk "one") true
  let resultMap := compileCircuit mkALU32 initMap'
  readOutput resultMap "result" 32

-- Step 2: Prove compiled version equals evalCircuit version
theorem alu32_compiled_eq_eval (a b : BitVec 32) (op : BitVec 4) :
    alu32Compiled a b op = evalALU32 a b op := by
  -- Follows from compileCircuit_correct + packing/unpacking correctness
  ...

-- Step 3: Prove compiled version equals spec (via bv_decide)
theorem alu32_compiled_eq_spec (a b : BitVec 32) (op : BitVec 4)
    (h : op.toNat < 10) :
    alu32Compiled a b op = aluSemantics (ALUOp.ofOpcode op) a b := by
  bv_decide  -- SAT solver handles this

-- Step 4: Compose to eliminate the axiom
theorem alu32_bridge_proven (op : ALUOp) (a b : BitVec 32) :
    evalALU32 a b op.toOpcode = aluSemantics op a b := by
  rw [← alu32_compiled_eq_eval]
  exact alu32_compiled_eq_spec a b op.toOpcode (by cases op <;> simp [ALUOp.toOpcode])
```

### 5.6 Handling Hierarchical Circuits (CircuitInstance)

The current `evalCircuit` ignores `CircuitInstance` entries -- it only processes
flat gates. Hierarchical circuits like the ALU32 have both gates (mux trees) and
instances (KoggeStoneAdder32, Subtractor32, etc.).

Two approaches:

**Option A: Flatten first.** Add a `Circuit.flatten` function that recursively
inlines all instances, replacing `CircuitInstance` with the gates of the referenced
circuit. The existing `Circuit.inline` function already does single-level inlining.
Then `compileCircuit` operates on the flattened gate list.

```lean
def Circuit.flatten (c : Circuit) (registry : String → Option Circuit) : Circuit :=
  { c with
    gates := c.instances.foldl (fun gates inst =>
      match registry inst.moduleName with
      | some sub => gates ++ (sub.flatten registry).inline inst.portMap
      | none => gates  -- unresolved instance
    ) c.gates
    instances := []
  }
```

Correctness: flattening preserves semantics if the registry maps each module name
to the correct circuit definition.

**Option B: Compositional compilation.** Compile each submodule separately into a
`BitVec → BitVec` function, then compose them. This mirrors the compositional
verification approach and scales better for very large circuits.

**Recommendation: Start with Option A** (flatten). It's simpler, requires no new
composition infrastructure, and handles the immediate goal (eliminating ALU32 axioms).
Option B becomes necessary only when circuits are too large to flatten (10k+ gates).

---

## 6. What This Eliminates

### Directly eliminable axioms (combinational circuits)

| Axiom | File | Gates | Status after this work |
|-------|------|-------|----------------------|
| `alu32_bridge` | ALUBitVecBridge.lean | ~1500 | Proven via `bv_decide` |
| `alu32_concrete_add` (+ 9 others) | ALUBitVecBridge.lean | ~1500 | Corollaries of bridge |
| `arbiter_onehot` (+ 4 others) | Arbiter.lean | varies | Provable via `bv_decide` |

### Indirectly enabled (sequential circuits, future work)

For sequential circuits, the approach extends to proving one-cycle combinational
logic correct, combined with DFF semantics (which are already proven for small cases
in `DFFProofs.lean`):

| Axiom | File | What's needed |
|-------|------|---------------|
| `mkFetchStage_implements_fetchStep` | FetchProofs.lean | Combinational mux logic + DFF |
| `mkCPU_RV32I_implements_cpuStep` | CPUProofs.lean | Full pipeline (large, needs Option B) |
| Rename stage axioms (7) | RenameStageProofs.lean | RAT + FreeList logic |
| RS axioms (9) | ReservationStation.lean | Behavioral model proofs |

### Not addressed by this work

| Axiom | Reason |
|-------|--------|
| `natToString_injective` | Pure math (Nat.repr injectivity), not circuit-related |
| `construction_deterministic` | Trivially true (`f n = f n`), should just be `rfl` |
| Decoupled interface axioms (10+) | Protocol-level properties, need different approach |
| `rv32i_instructions_unique` | Instruction encoding uniqueness, could use `native_decide` on bounded enum |

---

## 7. Feasibility Assessment

### Will `bv_decide` handle the ALU32?

The ALU32 compiled to a `BitVec` expression would be:
- 68 input bits (32 + 32 + 4)
- 32 output bits
- ~1500 boolean operations

This is a small SAT problem. Modern SAT solvers handle millions of variables.
The question is whether Lean's `bv_decide` implementation (which does bitblasting
inside the kernel) can handle ~1500 operations efficiently.

**Evidence it will work:** The existing `bv_decide` proofs in `ALUBitVecBridge.lean`
handle `BitVec 32` operations (commutativity, De Morgan's, distributivity) without
issue. These involve similar-complexity boolean reasoning. The difference is that
the compiled circuit would be a larger expression, but still well within SAT solver
capacity.

**Risk:** `bv_decide` might struggle not with the SAT problem itself, but with
constructing the proof certificate. Lean's `bv_decide` produces a kernel-checkable
proof term, and for very large circuits this could be slow. Mitigation: test with
progressively larger circuits (RippleCarryAdder32 at ~160 gates first, then
Subtractor32, then full ALU32).

### Can we prove the compiler correct?

The compiler correctness proof (`compileCircuit_correct`) is a straightforward
induction on the gate list. Each step is a simple case analysis on `GateType` plus
association list lemmas. This is standard Lean 4 proof engineering -- no exotic
tactics or deep math required.

**Estimated effort:** ~200-300 lines for the core infrastructure (WireMap + compiler
+ correctness theorem). This is a one-time investment.

### What about the WireMap approach vs. direct kernel reduction?

An alternative to this entire design would be to help Lean's kernel reduce
`evalCircuit` more efficiently -- for example, by using `HashMap` instead of
function closures for `Env`, or by providing reduction hints. This is theoretically
possible but would require modifying Lean 4's internals or writing a custom tactic.
The WireMap/compiler approach works entirely within Lean's existing proof framework.

---

## 8. Implementation Plan

### Phase 1: Core Infrastructure (~200-300 lines)

1. **`WireMap.lean`** -- Association list map with `lookup`, `insert`, correctness lemmas
2. **`CompileGate.lean`** -- Gate compilation + `compileGate_correct` theorem
3. **`CompileCircuit.lean`** -- Circuit compilation via foldl + `compileCircuit_correct` theorem
4. **`BitVecPacking.lean`** -- Generalized input/output packing (from ALUBitVecBridge helpers)

Validation: prove `compileCircuit_correct` for `fullAdderCircuit` (5 gates) using
the existing `AdderProofs.lean` as a cross-check.

### Phase 2: First Real Target -- RippleCarryAdder32 (~160 gates)

1. Flatten the RippleCarryAdder32 (it's already flat -- no instances)
2. Define `rca32Compiled : BitVec 32 → BitVec 32 → Bool → BitVec 32`
3. Prove `rca32Compiled a b cin = a + b + (if cin then 1 else 0)` via `bv_decide`
4. This validates the approach at realistic scale before tackling the ALU

### Phase 3: ALU32 Bridge Elimination (~100 lines)

1. Flatten ALU32 (resolve 5 `CircuitInstance` references into gates)
2. Define `alu32Compiled` using the compilation pipeline
3. Prove `alu32Compiled = aluSemantics` via `bv_decide`
4. Replace `axiom alu32_bridge` with a proven theorem
5. Derive all 10 concrete validation axioms as corollaries

### Phase 4: Generalize to Other Combinational Circuits

Apply the same pattern to:
- Comparator32
- LogicUnit32
- Shifter32
- Decoder, MuxTree, Subtractor32

Each should be ~20-30 lines of boilerplate (flatten, pack, compile, prove via `bv_decide`).

### Phase 5: Sequential Extension (Future)

Extend to one-cycle sequential reasoning:
1. Compile combinational logic within `evalCycleSequential`
2. DFF next-state is already simple (`if reset then 0 else d`)
3. Prove: `compileOneCycle c state inputs = evalCycleSequential c state inputs`
4. Use this to eliminate FetchStage and register file axioms

---

## 9. Risks and Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| `bv_decide` too slow for 1500-gate circuits | Low | High | Test incrementally; fall back to per-operation proofs |
| `bv_decide` proof term too large for kernel | Medium | Medium | Use `native_decide` as fallback for concrete cases |
| WireMap correctness proofs tedious | Low | Low | Standard assoc list lemmas, well-understood |
| Flattening hierarchical circuits introduces bugs | Low | Medium | Cross-check flattened gate count against known values |
| Wire naming conventions inconsistent across modules | Medium | Medium | Audit `makeIndexedWires` usage; add naming validation |
| `Circuit.inline` doesn't handle port remapping correctly | Low | High | Already used in RippleCarryAdder; test thoroughly |

---

## 10. Success Criteria

1. **Phase 1 done:** `compileCircuit_correct` proven for arbitrary circuits
2. **Phase 2 done:** RippleCarryAdder32 arithmetic correctness proven (no axioms)
3. **Phase 3 done:** `alu32_bridge` axiom replaced with proven theorem; all 10
   concrete validation axioms derived as corollaries
4. **Stretch:** 5+ combinational circuit modules have proven bridge theorems,
   eliminating their axioms

---

## 11. Alternatives Considered

### A. Per-operation structural unfolding

Instead of a generic compiler, manually prove each ALU operation by unfolding the
specific gates involved. For example, prove the ADD path by tracing signals through
the KoggeStoneAdder gates.

**Rejected because:** This requires understanding each circuit's internal structure
and writing custom proofs. The compiler approach is generic -- build it once, apply
to everything.

### B. Custom Lean tactic via metaprogramming

Write a Lean `macro` or `elab` that automates the circuit-to-BitVec compilation
at tactic time, rather than defining `compileCircuit` as a regular function.

**Deferred, not rejected:** This would be more ergonomic (just write `circuit_decide`
instead of manually setting up the compilation pipeline). But it requires Lean
metaprogramming expertise and is harder to debug. Build the non-meta version first,
then consider wrapping it in a tactic.

### C. External oracle (trust Yosys LEC results)

Import Yosys LEC results as Lean axioms via a verified log parser. The LEC already
runs and passes for all modules.

**Rejected because:** This just moves the axioms to a different place. The point is
to prove things in Lean, not to trust external tools. (Though LEC remains valuable
as an independent cross-check.)

### D. Certified code extraction

Instead of proving `evalCircuit = spec` in Lean, extract the circuit evaluator to
a verified language (e.g., OCaml with a proof-carrying certificate) and run it
externally.

**Rejected because:** This proves the evaluator is correct, not that the specific
circuit implements the spec. We need the latter.

---

## 12. Implementation Progress (2026-02)

### Completed

**Phase 1: Core Infrastructure** — All files created and proven correct.

| File | Status | Key content |
|------|--------|-------------|
| `Reflection/WireMap.lean` | Done | `WireMap` type, `lookup`/`insert`, `wire_beq_self`/`wire_beq_ne`, `lookup_insert_eq`/`lookup_insert_ne` |
| `Reflection/CompileGate.lean` | Done | `evalGateMap`, `compileGate`, `compileGate_correct` theorem |
| `Reflection/CompileCircuit.lean` | Done | `compileCircuit`, `compileCircuit_correct` theorem, `flattenAll`/`flattenAllFuel`, `compileCircuitHier` with `SubmoduleSpec` |
| `Reflection/BitVecPacking.lean` | Done | `bitVecToBindings`, `readWiresAsNatMap`, `readResultBitVecMap` |

**Phase 3 (partial): ALU32 concrete axioms eliminated.**

- Redefined `evalALU32` to use flattened circuit compilation (was broken: `evalCircuit` ignores `CircuitInstance`)
- All 10 concrete validation axioms replaced with `native_decide` proofs
- `alu32_bridge` (universal quantifier over all inputs) remains an axiom

**Foundational axioms proven:**

| Axiom | File | Approach |
|-------|------|----------|
| `not_involution` | `Theorems.lean` | `simp [Gate.mkNOT, evalGate, wire_beq_self, Bool.not_not]` |
| `wire_beq_eq` | `RegisterLemmas.lean` | String BEq roundtrip via `BEq.eq_of_beq` |

**Bug found: ALU opcode encoding.** The `ALUBitVecBridge.lean` opcode table had SLL=0x7, SRL=0x8, SRA=0x9, but the ALU MUX tree uses `op[3:2]` for category selection (00=arith, 01=logic, 10=shift). SLL at 0x7 (op[3:2]=01) was routed to the logic category. Fixed to SLL=0x8, SRL=0x9, SRA=0xB to match the RISCV execution unit encoding (which was already correct). LEC and cosim confirm the generated hardware was unaffected.

### Axiom scorecard

| Category | Before | After | Eliminated |
|----------|--------|-------|------------|
| ALU concrete tests | 10 axioms | 0 | 10 |
| ALU bridge | 1 axiom | 1 axiom | 0 |
| Foundational (`wire_beq_eq`, `not_involution`) | 2 axioms | 0 | 2 |
| Other (unchanged) | ~31 axioms | ~31 axioms | 0 |
| **Total** | **~44** | **~32** | **12** |

### Remaining challenge: `alu32_bridge`

The universal bridge `∀ op a b, evalALU32 a b op.toOpcode = aluSemantics op a b` could not be proven because:

1. `bv_decide` cannot unfold `evalALU32` — it treats `List.foldl` over the 2783-gate flat circuit as opaque
2. `native_decide` cannot handle the 68-bit universal quantification (2^68 cases)
3. The original design assumed `bv_decide` would see through `compileCircuit` to the underlying BitVec expression, but the `foldl` over a concrete gate list is not a BitVec expression — it's a general Lean computation

**Possible approaches for future work:**

- **Custom tactic**: A Lean metaprogram that symbolically evaluates `compileCircuit` step-by-step, building up a BitVec expression tree, then hands the result to `bv_decide`
- **Per-operation proofs**: Fix the opcode to a constant (e.g., `0x0` for ADD), which reduces the gate-level problem to ~500 relevant gates per operation path. This still requires symbolic `foldl` evaluation
- **Reflection via `Decidable`**: Define a `Decidable` instance for the bridge property that compiles to efficient native code, then use `decide`
- **AIG compilation**: Compile the circuit directly to an And-Inverter Graph, produce a DRAT proof of equivalence with the spec, and verify the DRAT certificate in Lean

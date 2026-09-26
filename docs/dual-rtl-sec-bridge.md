# Certified Dual-RTL SEC Bridge

Formal equivalence checking between human-written expressive SystemVerilog specifications and Shoumei's compiler-generated netlists, with SVA property inheritance in pure Lean 4.

## Problem

Shoumei defines hardware in an embedded Lean 4 DSL and emits SystemVerilog, ASIC netlists, and C++ simulators. This architecture leaves two verification gaps:

1. **Unverified Codegen**: A bug in the code generator (e.g. port transposition, bit-width truncation, inverted polarity) emits flawed RTL despite passing proofs on the high-level Lean model.
2. **Computational Reflection Overhead**: Verification of wide datapaths (e.g., `Queue1Bridge.lean` at $W=32$) required manual factoring into control and datapath slices evaluated via `native_decide` (unverified kernel evaluation).

## Architecture

The Certified Dual-RTL Bridge establishes a closed verification loop:

```
  [Expressive Human SV Spec + SVA]       [Shoumei Compiler Netlist]
          (Queue1_spec.sv)                      (Queue1_8.sv)
                 │                                   │
                 ▼                                   ▼
           Yosys SMT2                          Yosys SMT2
          (spec.smt2)                         (impl.smt2)
                 │                                   │
                 └───────────────┬───────────────────┘
                                 ▼
                     [lake exe smt2lean]  (Pure Lean 4, 0 Python)
                                 │
                      ┌──────────┴──────────┐
                      ▼                     ▼
             Bridge.Spec.step        Bridge.Impl.step
                      │                     │
                      ├────── bv_decide ────┤  ===> 1. Sequential Equivalence (SEC)
                      │   (Bisimulation)    │       (Netlist matches expressive spec)
                      ▼                     ▼
              [SVA Theorems] ──────► [Property Lift] ===> 2. Property Inheritance
           (Handshake, FIFO order)   (Netlist inherits SVA)
```

## Principles

### 1. Ingesting Without Python

Previous translation pipelines relied on Python scripts (`smt2lean.py`, `sva2lean.py`). The bridge introduces a native, self-contained Lean 4 tool (`lake exe smt2lean`):

- **Input**: SMT-LIB2 output from Yosys (`write_functional_smt2`).
- **Parser**: Native recursive-descent S-expression parser written in pure Lean 4.
- **Output**: Typed `BitVec` structures (`Inputs`, `Outputs`, `State`) and deterministic `step` function:
  ```lean
  def step (inputs : Inputs) (state : State) : Outputs × State
  ```

### 2. Expressive Specification vs Netlist Implementation

- **`Queue1_spec.sv`**: Written for human review and formal proof clarity. Uses high-level SystemVerilog constructs (`typedef enum logic { EMPTY, FULL } state_e;`, behavioral `push`/`pop` branching, and inline SVA assertions).
- **`Queue1_8.sv`**: Emitted by Shoumei's compiler (`mkQueue1StructuralComplete 8`). Structural gate-level netlist with decomposed combinational logic gates and DFF primitives.

### 3. Push-Button Sequential Equivalence (SEC)

The state equivalence theorem maps implementation registers to specification state fields:

```lean
def absState (s : Bridge.Impl.State) : Bridge.Spec.State where
  v_auto_ff_cc_337_slice_25 := s.v_procdff_14         -- valid bit
  v_auto_ff_cc_337_slice_28 := s.v_auto_ff_cc_337_slice_15 -- data register

theorem queue1_sec (i : Bridge.Impl.Inputs) (s : Bridge.Impl.State) :
    let imp := Bridge.Impl.step i s
    let spc := Bridge.Spec.step (absInputs i) (absState s)
    imp.1.enq_ready = spc.1.enq_ready ∧
    imp.1.valid = spc.1.valid ∧
    imp.1.data_reg = spc.1.data_reg ∧
    absState imp.2 = spc.2 := by
  obtain ⟨enq_d, enq_v, deq_r, clk, rst⟩ := i
  obtain ⟨d, v⟩ := s
  simp only [Bridge.Impl.step, Bridge.Spec.step, absState, absInputs, Bridge.Spec.State.mk.injEq]
  bv_decide
```

Discharged by `bv_decide` in $<0.5$ s using verified LRAT proof certificates with 0 custom axioms.

### 4. SVA Property Lifting

Any temporal assertion stated in `Queue1_spec.sv` is lifted directly to the compiled gate netlist `Bridge.Impl`:

1. **Ready-Valid Contract**: `enq_ready = !valid`
2. **Handshake Stability**: Data and valid signals hold invariant across stalled cycles (`valid && !deq_ready |=> valid && $stable(data_reg)`)
3. **Enqueue Effect**: Enqueue into an empty queue stores the operand and asserts valid on the subsequent cycle (`!valid && enq_valid |=> valid && data_reg == $past(enq_data)`)

## Verification Commands

```bash
# Run full dual-RTL bridge verification
make sec-bridge

# Build standalone Lean SMT ingester
lake build smt2lean
```

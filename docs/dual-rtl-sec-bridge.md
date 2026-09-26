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
   verification/specs/*.sv                output/sv-from-lean/*.sv
                 │                                   │
                 ▼                                   ▼
           Yosys SMT2                          Yosys SMT2
   verification/bridge/*_spec.smt2     verification/bridge/*_impl.smt2
                 │                                   │
                 └───────────────┬───────────────────┘
                                 ▼
                     [lake exe smt2lean]  (Pure Lean 4, 0 Python)
                                 │
                                 ▼
                 output/sec-bridge/ShoumeiSec/   (generated, gitignored)
                      ├── Bridge/<Mod>Spec.lean  -> ShoumeiSec.Bridge.<Mod>Spec
                      ├── Bridge/<Mod>Impl.lean  -> ShoumeiSec.Bridge.<Mod>Impl
                      └── Bridge<Mod>.lean       -> ShoumeiSec.Bridge<Mod> (SEC proof)
                                 │
                                 ▼
                  lake build ShoumeiSec   (separate Lake library)
                                 │
                      ┌──────────┴──────────┐
                      ▼                     ▼
              <Mod>Spec.step          <Mod>Impl.step
                      │                     │
                      ├────── bv_decide ────┤  ===> 1. Sequential Equivalence (SEC)
                      │   (Bisimulation)    │       (Netlist matches expressive spec)
                      ▼                     ▼
              [SVA Theorems] ──────► [Property Lift] ===> 2. Property Inheritance
           (Handshake, FIFO order)   (Netlist inherits SVA)
```

### Artifact layout

Two Lean libraries keep generated proof material out of the hand-written tree:

| Library | Source root | Tracked in git | Contents |
|---|---|---|---|
| `Shoumei` | `lean/` | yes | DSL, circuits, proofs, registry (`Shoumei.Verification.DualRTL`, `Shoumei.All`) |
| `ShoumeiSec` | `output/sec-bridge/` | no (`.gitignore`) | SMT2-derived `Spec`/`Impl` models and SEC proofs |

`Shoumei.All` therefore imports only human-authored modules; the bridge models are
rebuilt on demand by `make sec-bridge` and never appear in `git status`.

## Principles

### 1. Ingesting Without Python

The bridge introduces a native, self-contained Lean 4 tool (`lake exe smt2lean`,
source `Smt2Lean.lean`); no Python is in the loop:

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
def absState (s : Bridge.Queue1Flow_39Impl.State) : Bridge.Queue1Flow_39Spec.State where
  v_auto_ff_cc_337_slice_37 := s.v_auto_ff_cc_337_slice_22      -- data register
  v_procdff_33 := s.v_procdff_18                                -- valid bit

theorem queue1flow_39_sec (i : Bridge.Queue1Flow_39Impl.Inputs)
    (s : Bridge.Queue1Flow_39Impl.State) :
    let imp := Bridge.Queue1Flow_39Impl.step i s
    let spc := Bridge.Queue1Flow_39Spec.step (absInputs i) (absState s)
    imp.1.enq_ready = spc.1.enq_ready ∧
    imp.1.deq_valid = spc.1.deq_valid ∧
    imp.1.deq_data = spc.1.deq_data ∧
    absState imp.2 = spc.2 := by
  obtain ⟨ed, ev, dr, clk, rst⟩ := i
  obtain ⟨d, v⟩ := s
  simp only [Bridge.Queue1Flow_39Impl.step, Bridge.Queue1Flow_39Spec.step,
             absInputs, absState, Bridge.Queue1Flow_39Spec.State.mk.injEq]
  bv_decide
```

Discharged by `bv_decide` in $<0.5$ s using verified LRAT proof certificates with 0 custom axioms.

`scripts/gen-bridges.py` emits these modules from three inputs: the parameterized
spec, the emitted netlist, and a per-family recipe that states the port/state
correspondence.  Where a design flattens into several identical state fields
(`Queue16x32_DualPort`'s 16 entries), the correspondence is derived by probing each
field through a read port and is recorded as a table in the script.

#### Parameterized specification families

One spec file covers every width/topology variant of a family; Yosys `chparam`
instantiates it for each instance:

| Spec (tracked) | Circuits covered |
|---|---|
| `Register_spec.sv`, `RegisterEn_spec.sv`, `Decoder_spec.sv` | Register1..64, RegisterEn1..64, Decoder2..6 |
| `Adder_spec.sv`, `AdderNoCin_spec.sv`, `AdderWithCin1_spec.sv` | 46 prefix adders across 6 topologies x {32, 64, 106} |
| `Subtractor_spec.sv`, `Comparator_spec.sv`, `EqualityComparator_spec.sv` | Subtractor32/64, Comparator4..64, EqualityComparator6..64 |
| `Mux4/8/16/32/64_spec.sv`, `LogicUnit_spec.sv`, `Shifter_spec.sv`, `PCIncrementer_spec.sv` | mux trees, ALU leaves, shifters, PC incrementers |
| `Queue1_spec.sv`, `Queue1Flow_spec.sv` | Queue1_1, Queue1_8, Queue1Flow x10 |
| `PriorityArbiter_spec.sv`, `OneHotEncoder_spec.sv`, `Popcount_spec.sv` | PriorityArbiter2/8/64, OneHotEncoder64, Popcount8 |
| `QueuePointer_spec.sv`, `QueuePointerLoadable_spec.sv`, `QueueCounterLoadable_spec.sv` | pointer/counter primitives |
| `Queue16x32_DualPort_spec.sv` | 16x32 dual-write dual-read register file |

#### Combinational-loop hazard in the SMT functional backend

Yosys' `write_functional_smt2` rejects designs where its signal-group heuristics
bundle unrelated scalar carry/prefix nets into a bus whose bit assignments then
appear self-referential.  Prefix adders, Kogge-Stone stages, the priority-arbiter
mask chain, the one-hot encoder OR chain, and queue-pointer carry chains therefore
name those nets as scalars (`pxa_l{li}g{i}`, `ksag{stride}x{i}`, `pamask{i}x{j}`,
`paorx{i}`, `encor{b}x{idx}`, `qpc{i}`, `qccp{i}`, `qccm{i}`) rather than
`_<index>` buses.

### 4. SVA Property Translation (`sva2lean`)

The assertions a specification writes about itself are translated into Lean
theorems by `lake exe sva2lean` (source `Sva2Lean.lean`), which reads the spec's
`` `ifdef FORMAL `` block together with the Lean model of that same
specification:

```
  spec.sv  --yosys + smt2lean-->  Model.step        the body
  spec.sv  --sva2lean---------->  theorem          the claims
  netlist  --SEC bridge-------->  netlist == Model  the lift
```

So a claim proven of the specification body holds of the emitted netlist
through the SEC theorem, and each specification becomes self-checking: its SV
body must satisfy the SV properties it declares.

Supported subset, and nothing outside it is accepted silently:

| Form | Meaning |
|---|---|
| `assert (e);` | invariant over the model's combinational outputs |
| `assert property (e);` | invariant |
| `assert property (a \|-> c);` | same-cycle implication |
| `assert property (a \|=> c);` | next-cycle implication |
| `default clocking @(posedge clk);` | clocking (implied by the model) |
| `default disable iff (r);` | hypotheses `i*.r = 0#1` on each sampled cycle |
| `@(posedge clk) disable iff (1'b0)` | per-property opt-out of the default disable |
| `$past(x[, n])`, `$stable(x)` | resampled against previous quantified cycles |
| `$onehot(x)`, `x[k]`, `P'(e)`, `'0`, `4'd3` | power-of-two, constant bit select, parameter cast, literals |
| `! ~ && \|\| == != < > <= >= + - & \| ^` | operators |

Two failure modes are hard errors rather than silent weakenings:

- **Unparsed trailing tokens.** An operand that fails to parse leaves the rest
  of the property unconsumed; the tool refuses it. (The first draft of this
  tool silently truncated `a_handshake_stable` to its first conjunct.)
- **Vacuous assertions.** A property disabled on `r` whose antecedent assumes
  `r` can never fail. `Register_spec.sv` and `RegisterEn_spec.sv` both declared
  `a_reset_clears: assert property (reset |=> (q == '0))` under
  `default disable iff (reset)`; both are now written with an explicit
  `disable iff (1'b0)`, which is what makes the claim mean something.

Coverage: every specification that declares an assertion is covered -- 107
theorems across 47 generated modules, from 11 specs (`Adder_spec`,
`AdderNoCin_spec`, `AdderWithCin1_spec`, `Comparator_spec`, `Decoder_spec`,
`EqualityComparator_spec`, `Mux4_spec`, `Queue1_spec`, `Register_spec`,
`RegisterEn_spec`, `Subtractor_spec`).

One module is emitted per `(spec, width)`, not per circuit: six adder topologies
share a single `Adder_spec` instantiation, so the first circuit seen at a given
`(spec, width)` supplies the model and the rest reuse its theorems.  Steps that
made the remaining specs tractable:

- the assertion is located by its `assert` token, so an `if (guard)` is read as
  a same-cycle implication rather than mistaken for the argument of `assert`
- variable bit selects (`out[in]`, used by `Decoder_spec`) render as a mux chain
  over the bus width, with out-of-range indices reading as zero as in SV
- model field names are unquoted on read (`smt2lean` writes reserved words as
  `«out»`), so a spec identifier resolves to its field
- `EqualityComparator6_spec.sv` was deleted: it was referenced only by the
  registry, while the SEC proof for `EqualityComparator6` actually verifies
  `EqualityComparator_spec.sv` at width 6.  The registry now names that spec.

History note: this replaced a hand-transcribed file,
`verification/specs/BridgeQueue1Properties.lean`, which carried three of
`Queue1_spec`'s four properties -- `a_pop_effect` had been dropped without
notice, and a later edit to the spec dropped its whole `` `ifdef FORMAL `` block.
Both losses were silent, which is the whole argument for translating instead of
transcribing.

### 5. Scaling Limits and Tiering (`bv_decide`)

The BitVec solver (`bv_decide`) bit-blasts formulas into CNF and dispatches to an
integrated CDCL/CaDiCaL SAT solver with LRAT proof checking. Performance scales
differently across circuit topologies:

- **Adders, MUX trees, Shifters, Decoders, Queues**: Scale cleanly up to 106 bits
  (e.g. `KoggeStoneAdder106` proves in 2.8s; `Mux64x64` in 4.4s).
- **Multiplier probe (`Mul32x32To64`)**: Evaluated against an expressive SV
  spec (`assign product = 64'(a) * 64'(b)`).
  - Spec-side SVA properties (`a_zero_mul`, `a_identity_mul`) prove in 0.67s via
    `sva2lean` and `bv_decide`.
  - Full netlist SEC (Wallace/Dadda tree with 32 partial products, 8 CSA stages,
    and `MulFinalAdder64`) **times out in SAT solving** (>60s, 99% CPU, 824 MB RSS).

#### Implications for Remaining Circuits

1. **Arithmetic Datapaths (Multipliers, Dividers, FP)**: Monolithic `bv_decide`
   cannot discharge non-linear arithmetic against pure bit-blasted products without
   algebraic rewriting. Verification for these units follows two distinct paths:
   - Compositional verification (proving partial products, CSA compressors via
     lemmas, and the final adder independently).
   - Lock-step architectural co-simulation against Spike (`make -C testbench cosim`).
2. **Tiered Coverage Strategy**:
   - **Tier A (Registers, Buffers, Gates)**: Direct SEC via parameterized specs (130 circuits verified).
   - **Tier B/C (ALUs, PLRU, Small Core Sequencers)**: Tractable via `bv_decide`.
   - **Tier D (Multipliers, Dividers, FP, OoO Core)**: Compositional certificates or cosimulation.
## Verification Commands

```bash
# Run full dual-RTL bridge verification (generates output/sec-bridge/, then
# builds the ShoumeiSec library: 130 circuits + 107 spec assertions, 0 axioms)
make sec-bridge

# Coverage manifest: verified / spec-only / missing across all 237 circuits
make sec-manifest

# Regenerate only the generated models and proofs
python3 scripts/gen-bridges.py

# Build standalone Lean SMT ingester
lake build smt2lean

# Hand-written gates that must stay green
lake build Shoumei.All                     # human-authored modules only
python3 scripts/gen-lean-root.py --check   # Shoumei.All is current
```

## Coverage

| Metric | Count |
|---|---|
| Circuits in the emitted universe | 237 |
| Families with a human-authored spec | 130 (54%) |
| Verified with `bv_decide` (0 axioms) | 130 |
| Spec-only (no proof yet) | 0 |
| Missing | 107 |

Tracked verification surface:

| Path | Tracked | Role |
|---|---|---|
| `verification/specs/*.sv` | yes | human-authored reference models |
| `Sva2Lean.lean` | yes | SVA assertion -> Lean theorem translator (`lake exe sva2lean`) |
| `output/sec-bridge/ShoumeiSec/Bridge*Props.lean` | no | generated per-spec assertion theorems |
| `scripts/gen-bridges.py` | yes | per-family SEC recipes and state-correspondence tables |
| `lean/Shoumei/Verification/DualRTL.lean` | yes | registry mapping circuit -> spec -> proof |
| `output/sec-bridge/**` | no | generated `Spec`/`Impl` models and SEC proofs |
| `verification/bridge/*.smt2` | no | intermediate Yosys SMT2 |

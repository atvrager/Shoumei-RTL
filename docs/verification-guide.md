# Verification Guide

How equivalence checking works in Shoumei RTL, including direct LEC, compositional verification, and troubleshooting.

## Verification Architecture

The verification pipeline has two complementary methods:

1. **Direct LEC** -- Yosys compares Lean SV vs Chisel SV at the gate level
2. **Compositional Verification** -- Lean proofs + verified building blocks

Both feed into the same script (`verification/run-lec.sh`) which reports unified coverage.

```
                         run-lec.sh
                             |
              +--------------+--------------+
              |                             |
        Direct LEC                   Compositional
    (Yosys SAT/induction)         (Lean certificates)
              |                             |
    +---------+---------+          +--------+--------+
    |                   |          |                 |
Combinational      Sequential   Check deps       Lean proof
  (CEC)              (SEC)      all verified     reference
    |                   |          |
  miter +          equiv_make +   dependency
  SAT solve        equiv_induct   verification
```

## Work at the netlist level

When a verification problem looks hard, ask **what yosys would do**, and do that.
yosys does not reason about RTL.  It elaborates every module down to a netlist of
cells and wires, then reasons *structurally*: `equiv_make` matches wires and
instances, `equiv_simple` propagates known-equal values through the structure,
and only the leftover cones are handed to SAT or induction.

The same bias belongs in this project:

- **Prefer structural checks to semantic ones.** "Same instance tree, same cell
  types, same connectivity" is O(size) and exact; SAT is exponential and
  approximate.  Reach for the solver only where structure genuinely differs.
- **Compare hierarchies as trees, not as flattened blobs.** Flattening converts a
  linear structure into a quadratic one.  Inlining the full hierarchy produced an
  **8.7 MB** netlist for `PhysRegFile_64x32` (from ~260 KB) and would produce
  hundreds of megabytes for the CPU; keep module boundaries, because they *are*
  the composition boundaries.
- **Emit machine-checkable netlists**, not more RTL, when a second artifact is
  wanted: JSON via `write_json`, btor2, aiger.  Netlists are the common language
  of the tools, and text-level RTL differences are noise that must be normalised
  away before anything can be compared.
- **Treat routine escalation as a structural smell.** If a check needs induction
  or SAT to pass every time, the structure has drifted.  Fix the structure, not
  the solver budget.

Corollary for the Chisel question: the replacement for a second *RTL* artifact is
not another RTL emitter.  It is a **netlist-level comparison** -- either between
the emitted design and the `Circuit` it came from, or between two emitted
netlists.

## The proof ladder

**Every proof must be small and finish fast; bigger results come from composing
them.** A single long-running proof is a liability: it hides regressions behind
a timeout, cannot be parallelised, and sits on the critical path of every
commit. Treat sub-modules as already-proven theorems and prove only the few new
facts each level adds.

| Level | What is proven | Cost | Mechanism |
| :--- | :--- | :--- | :--- |
| Leaf behaviour | module meets its spec | < 1 s | Lean theorem (`native_decide`, `simp`) |
| Leaf translation | Lean SV == Chisel SV | seconds, cached | LEC, reads scoped to the leaf + transitive deps |
| Composition | parent correct given children | seconds | Lean `CompositionalCert`, or LEC congruence |
| Smoke | integration sanity | < 2 s | parallel sim / Spike cosim sweep |

Rules that keep the ladder intact:

1. **Prove against the spec, not against another implementation.** A leaf proof
   that inspects emitted RTL is a translation check masquerading as a theorem;
   it will be re-run forever and never composes.
2. **Compose, do not re-flatten.** A composite module is discharged in one of
   two ways, in order of preference:
   - a **Lean composition proof** — the parent's spec follows from the
     children's theorems plus glue reasoning (`CompositionalCert`;
     see [Compositional Verification](#compositional-verification)); this is the
     axiom/theorem ladder, and the leaf theorems are the axioms;
   - **LEC congruence** — both netlists are emitted from the same `Circuit`, so
     they are structurally identical modulo leaves. `equiv_simple` then
     discharges the miter by structural hashing, with no induction and no SAT,
     *because* the leaves are already proven. This is the two-tier pass in
     `run-lec.sh`.
3. **Escalation is the exception, not the default.** `equiv_induct` / `sat` run
   only on points the structural pass leaves unproven. If they fire often, the
   composition is drifting from the children's interfaces — fix that instead of
   widening the timeout.
4. **Tier the work.** Commit and PR gates run leaves + congruence + a
   simulation/cosim smoke. A heavyweight sweep belongs in a nightly job, never
   on the commit path.
5. **Budget every proof.** If one module's check dominates the run, decompose
   it. A check that cannot finish in seconds is a decomposition bug.

### Shredding further: what atoms are still missing

The ladder is only as granular as its atoms.  Today a module contributes a
behavioural model, a structural `Circuit`, a handful of `native_decide`
structural facts, and one LEC translation check -- and the *join* between
behaviour and structure is asserted in prose.  `CompositionalCert.proofReference`
is a `String`; `run-lec.sh` checks only that the dependencies were verified, so a
cert can name a proof that does not exist or no longer holds.

In order of leverage, the missing atoms are:

1. **`Circuit` satisfies `Behavior` (per module).** There is no circuit
   semantics in Lean, so nothing connects the structural `Circuit` to the
   behavioural model (`CPUBehavioral.cpuStep` and friends).  LEC relates Lean SV
   to Chisel SV; the theorems talk about the model; the two never meet.  Add an
   evaluator (`eval : Circuit -> Wire -> Value`, gate by gate) and one
   refinement theorem per leaf.  This is the atom that closes the gap.
2. **One generic composition lemma.** Given `eval child = childBehavior` for
   every child, a parent built from `CircuitInstance`s satisfies
   `eval parent = parentBehavior`.  Prove this *once* over the hierarchical
   evaluator; afterwards every parent's atom is a one-line instantiation of its
   children's atoms.  This is what replaces flattened SAT/induction.
3. **Per-building-block semantic lemmas.** `mkRippleCarryAdder n`,
   `mkMuxTree k w`, `mkRegisterN n`, `mkComparatorN n` should each carry a
   semantic lemma (`eval (rca n) a b = a + b`).  Then adder -> ALU -> datapath is
   a chain of one-liners instead of a per-instance decision procedure.
4. **Machine-checked certificates.** Generate `CompositionalCert` entries *from*
   the composition-lemma instantiations, so a certificate exists only if its
   theorem type-checks.  `export_verification_certs` then cannot emit a dangling
   reference.
5. **Per-instruction ISA atoms.** Decoder proofs give coverage and non-overlap;
   add one semantic atom per opcode (`decode w = .X -> exec X s = spec X s`).
   An extension then arrives as N small atoms -- exactly the shape wanted for
   reviewing a new extension quickly.

Antipatterns:

- **A cert with no proof.** A `CompositionalCert` is a *reference to* a Lean
  proof. Adding one to silence a slow module, without that proof existing,
  converts a slow check into an unchecked assumption.
- **Deepening the induction.** Raising `equiv_induct -seq N` until a
  hierarchical module passes usually means the parent no longer matches the
  proven child interfaces.
- **A mtime-based cache.** Fresh checkouts and CI artifact downloads give every
  file a new timestamp, so mtime stamps (and mtime "staleness" checks) silently
  disable caching. Key on content.
- **Reading the whole tree per module.** Every module re-parsing every file is
  quadratic in the design size; scope reads to the module and its dependencies.

Measured on this repository (6-core workstation): scoping LEC reads removed
seconds of parsing per leaf module; the cache is content-addressed so unchanged
modules are skipped across CI runs; and the 111-test simulation suite dropped
from ~50 s to ~2 s under the parallel driver.

## Replacing the Chisel cross-check

Chisel is not how the design is verified.  It is the **second artifact** in a
translation check: `LEC(Lean SV, Chisel SV)` catches bugs in the *emitters*.
Design correctness comes from the Lean proofs, and it always did.  So Chisel can
be removed iff two properties survive:

1. an **independent second lowering** of every `Circuit`, and
2. an independent check that the DSL's meaning is what we think it is.

### Step 1 -- second lowering: use the Lean flat netlist

`output/sv-netlist/` is already a second emitter of the same `Circuit`
(`SystemVerilogNetlist.lean`), written in a completely different style: it inlines
every instance down to gates instead of emitting a hierarchy.  It costs nothing
extra to emit and needs no JVM.

Feasibility is established: `LEC(ALU32 hierarchical, ALU32 netlist)` reports
`SAT proof finished - no model found: SUCCESS` in ~3 s.

Required work before it can replace Chisel for **all** modules:

- **State completeness.** The netlist emitter is currently combinational-only:
  `output/sv-netlist/RenameStage_W2.sv` contains zero `always` blocks and no
  `clock`/`reset` ports -- DFF gates are dropped.  It must emit sequential state
  (`always_ff`, or instances of a `DFlipFlop` module) and keep clock/reset in the
  port list.
- **Port identity.** The two emitters must agree on the port set, including bus
  grouping (`rd_data3` vs `rd_data3_0..31`), so `equiv_make` can match ports by
  name.

Once those hold, `LEC(Lean SV, Lean netlist)` replaces `LEC(Lean SV, Chisel SV)`
in every target.

### Step 2 -- recover front-end independence

Two Lean emitters share the Lean front-end, so a bug in `Circuit` construction is
invisible to both.  Chisel's unique contribution was a *whole different
toolchain's* reading of the DSL.  Recover that independence from:

- **`Circuit` satisfies `Behavior` refinement atoms** (see *Shredding further*
  above).  This is the check that the DSL's meaning is what we believe; LEC never
  provided it.
- **Differential simulation across independent engines**: Verilator (Lean SV),
  Arcilator (a CIRCT lowering of the same Lean SV), and the generated C++ model,
  all driven by the same ELF and compared on the retired trace and `tohost`.
- **Independent parsers**: `read_slang` and `read_verilog -sv` on the same Lean
  SV -- cheap, and it catches SV that is legal under only one reading.

### Step 3 -- delete the pipeline

Drop `make chisel`, the `scala-build` CI job, the `scalafmt` gate, the Chisel
branch of `run-lec.sh`, and the `.scala` outputs.  Keep the Chisel generator
reachable behind a flag for one release so any disagreement can be arbitrated
before it goes away for good.

### Interim

`lake exe generate_all --no-chisel` skips the backend for day-to-day iteration
(the RTL simulation, cosim and LEC paths all read the Lean SV).  The incremental
cache is salted by the emitted format set, so a `--no-chisel` run can never be
mistaken for a full one.

## Direct LEC

### How it works

The LEC script reads both SV files, builds an equivalence circuit, and uses a SAT solver to prove they produce identical outputs for all inputs.

### Combinational Equivalence Checking (CEC)

For circuits without registers (no `always @` blocks):

```
read_verilog -sv <lean SV>          # Read gold (Lean) design
hierarchy -check -top <module>
proc; opt; memory; opt; flatten
rename <module> gold

read_verilog -sv <chisel SV>        # Read gate (Chisel) design
hierarchy -check -top <module>
proc; opt; memory; opt; flatten
rename <module> gate

miter -equiv -flatten gold gate miter   # Build miter circuit
sat -verify -prove-asserts miter        # SAT solve
```

**Success:** `SAT proof finished - no model found: SUCCESS`
**Failure:** SAT finds a counterexample (input values where outputs differ)

### Sequential Equivalence Checking (SEC)

For circuits with registers (`always @` blocks detected):

```
# Same read + flatten steps, then:
equiv_make gold gate equiv      # Build equivalence circuit
prep -top equiv
async2sync

equiv_simple -undef             # Structural optimization
equiv_induct -undef             # Induction proof
equiv_status -assert            # Assert all equivalences hold
```

For hierarchical sequential circuits, a bounded induction depth is used:
```
equiv_induct -undef -seq 3      # 3-step induction
```

**Success:** `Equivalence successfully proven`
**Failure:** Unproven equivalence points remain

## Compositional Verification

### When to use

Use compositional verification when direct LEC fails or is impractical:

- **Structural mismatch:** Lean generates register arrays differently from Chisel
- **Large state space:** Too many registers for induction to converge
- **Hierarchical modules:** Built from verified submodules with known behavior

### How it works

1. All leaf submodules are verified by direct LEC (CEC or SEC)
2. A Lean proof establishes that the composition of verified submodules implements the specified behavior
3. A `CompositionalCert` in Lean declares the module, its dependencies, and the proof reference
4. The LEC script loads certificates, verifies all dependencies are already proven, and accepts the compositional result

### Certificate structure

Defined in `lean/Shoumei/Verification/Compositional.lean`:

```lean
structure CompositionalCert where
  moduleName : String              -- Module being verified
  dependencies : List String       -- Submodules that must be LEC-verified first
  proofReference : String          -- Lean namespace containing the composition proof
```

### Certificate registry

All certificates live in `lean/Shoumei/Verification/CompositionalCerts.lean`:

```lean
def register91_cert : CompositionalCert := {
  moduleName := "Register91"
  dependencies := ["Register64", "Register16", "Register8", "Register2", "Register1"]
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

def allCerts : List CompositionalCert := [
  register91_cert,
  queue64_32_cert,
  ...
]
```

### Export mechanism

`ExportVerificationCerts.lean` exports certificates in `module|dep1,dep2,...|proof_ref` format:

```bash
$ lake exe export_verification_certs
Register91|Register64,Register16,Register8,Register2,Register1|Shoumei.Circuits.Sequential.RegisterProofs
Queue64_32|QueueRAM_64x32,QueuePointer_6,QueueCounterUpDown_7|Shoumei.Circuits.Sequential.QueueProofs
...
```

The LEC script calls this and parses the output into a bash associative array.

### Current compositional modules

| Module | Dependencies | Proof |
|--------|-------------|-------|
| Register91 | Register64, Register16, Register8, Register2, Register1 | RegisterProofs |
| Queue64_32 | QueueRAM_64x32, QueuePointer_6, QueueCounterUpDown_7 | QueueProofs |
| Queue64_6 | QueueRAM_64x6, QueuePointer_6, QueueCounterUpDown_7 | QueueProofs |
| QueueRAM_64x32 | Register32, Decoder6, Mux64x32 | QueueProofs |
| QueueRAM_64x6 | Register6, Decoder6, Mux64x6 | QueueProofs |
| PhysRegFile_64x32 | Decoder6, Mux64x32 | PhysRegFileProofs |
| RAT_32x6 | Decoder5, Mux32x6 | RATProofs |
| FreeList_64 | QueueRAM_64x6, QueuePointer_6, QueueCounterUpDown_7, Decoder6, Mux64x6 | FreeListProofs |
| ReservationStation4 | Register2, Register91, Comparator6, Mux4x6, Mux4x32, Decoder2, PriorityArbiter4 | ReservationStationProofs |

## Topological Sorting

The LEC script processes modules in dependency order. This is critical because compositional certificates require all dependencies to be verified first.

### How it works

1. Build a dependency graph from compositional certificates
2. Pipe through `awk` to generate `tsort`-compatible pairs
3. `tsort` produces a topological ordering
4. Modules without dependencies come first, then dependent modules

Example ordering:
```
Register1          # No dependencies, verified first
Register2
Register8
Register16
Register64
Register91         # Depends on Register{1,2,8,16,64}
Decoder6
Mux64x32
QueuePointer_6
QueueCounterUpDown_7
QueueRAM_64x32     # Depends on Register32, Decoder6, Mux64x32
Queue64_32         # Depends on QueueRAM_64x32, QueuePointer_6, QueueCounterUpDown_7
```

## Chisel Cleaning

Before LEC, Chisel output is cleaned for Yosys compatibility:

1. **Remove CIRCT verification blocks:** Everything after `// ----- 8< -----`
2. **Convert automatic variables:** `automatic logic x = y;` -> `logic x; x = y;`
3. **Remove `automatic` keyword:** Yosys doesn't support it

This happens automatically in `run-lec.sh` and writes to a temp directory.

## Troubleshooting

### LEC says "VERIFICATION INCOMPLETE"

**Possible causes:**
- Yosys couldn't read one of the SV files (syntax error)
- Induction didn't converge (increase depth or use compositional)
- Port name mismatch between Lean and Chisel output

**Debug steps:**
1. Check the Yosys output (last 20 lines are printed)
2. Try reading each SV file individually:
   ```bash
   yosys -p "read_verilog -sv output/sv-from-lean/MyModule.sv"
   yosys -p "read_verilog -sv output/sv-from-chisel/MyModule.sv"
   ```
3. Compare port lists:
   ```bash
   grep "input\|output" output/sv-from-lean/MyModule.sv
   grep "input\|output" output/sv-from-chisel/MyModule.sv
   ```

### LEC says "NOT EQUIVALENT"

**This means the two generators produce different logic.** This is a real bug.

**Debug steps:**
1. The SAT solver found a counterexample -- check the failing assertions
2. Diff the two SV files to find structural differences
3. Common causes:
   - Off-by-one in wire indexing
   - Different reset behavior
   - Missing or extra gates in one generator
   - Clock/reset handling differences (check `findClockWires`/`findResetWires`)

### Compositional verification says "INCOMPLETE"

**Means one or more dependencies aren't verified yet.**

**Debug steps:**
1. Check which dependencies are missing (printed in output)
2. Ensure the dependency modules exist in both `output/sv-from-lean/` and `output/sv-from-chisel/`
3. Verify the dependency modules pass LEC individually
4. Check topological ordering -- the dependency should come before the dependent module

### Chisel compilation fails before LEC

See the "Common Chisel compilation issues" table in [docs/adding-a-module.md](adding-a-module.md).

The most common issue is `IndexOutOfBoundsException` from incorrect input indexing, caused by clock/reset not being filtered. Fix: ensure `findClockWires` and `findResetWires` in `Common.lean` detect your module's clock/reset wires (from both DFF gates and instance connections).

## Running Verification

### Full LEC (all modules)

```bash
./verification/run-lec.sh
```

### Smoke test (CI pipeline)

```bash
./verification/smoke-test.sh
```

Tests: Lean build, formal proofs, code generation, Chisel compilation, port validation, LEC.

### Via Make

```bash
make lec              # Just LEC
make verify           # LEC + EQY
make smoke-test       # Full CI pipeline
make all              # Build + codegen + chisel + LEC
```

## Adding a New Compositional Certificate

1. Verify all building blocks pass direct LEC
2. Write the composition proof in Lean (or reference existing proofs)
3. Add `CompositionalCert` to `CompositionalCerts.lean`
4. Add to `allCerts` list
5. Run `lake build` to ensure it compiles
6. Run `./verification/run-lec.sh` to see the module verified compositionally

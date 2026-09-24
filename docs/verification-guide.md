# Verification Guide

How Shoumei RTL convinces itself the design is correct: Lean proofs, the compositional
certificate registry, and the elaboration and simulation checks that run on the emitted
SystemVerilog.

## Verification Architecture

Design correctness comes from the Lean proofs. The emitted SystemVerilog is one
translation of the proven `Circuit`, so there is no second RTL design to compare
against; what is checked is that the translation elaborates and runs.

| Layer | What it establishes | Mechanism |
| :--- | :--- | :--- |
| Leaf behaviour | module meets its spec | Lean theorem (`native_decide`, `simp`) |
| Composition | parent correct given children | Lean `CompositionalCert` |
| Equivalence (SEC) | alternative implementations preserve trace semantics | Lean bisimulation & SAT/LEC miters ([SEC Guide](proof-strategies/sequential-equivalence-checking.md)) |
| Formal Properties (SVA) | temporal assertion contracts hold on RTL | IEEE 1800 SVA FPV ([SVA Guide](proof-strategies/sva-formal-verification.md)) |
| Registry | every certificate matches an emitted circuit | `lake exe generate_all --export-certs` |
| Elaboration | the emitted SV is legal IEEE 1800-2017 SV | `python3 verification/slang-lint.py`, `make systemverilog` (Yosys read/hierarchy) |
| Dynamic Simulation | RTL executes cycles correctly & assertions active | Verilator `--assert`, C++ cycle-accurate model |
| Co-simulation | retired instruction trace matches Spike reference | Spike lock-step cosimulation (`make -C testbench cosim`) |
| Compliance | RISC-V architectural compliance | 107/107 `riscv-arch-test` pass |

```
                      ┌──────────────────────────────────────┐
                      │    Lean 4 Mathematical Proofs        │
                      │  - L0 Structural Pinning             │
                      │  - L1 Functional Step Theorems       │
                      │  - L2 Inductive State Invariants     │
                      │  - L3 Temporal Refinement (Bisim)    │
                      └──────────────────┬───────────────────┘
                                         │ lake exe generate_all
                                         ▼
                      ┌──────────────────────────────────────┐
                      │      Emitted Hardware Artifacts      │
                      │  - Hierarchical SystemVerilog        │
                      │  - Flat Netlist SystemVerilog        │
                      │  - ASAP7 / GF180 Tech-Mapped Gates   │
                      │  - Cycle-Accurate C++ Simulation     │
                      │  - Embedded SVA Formal Assertions    │
                      │  - Auto-Generated SEC Miters         │
                      └──────────────────┬───────────────────┘
                                         │
         ┌───────────────────────────────┼───────────────────────────────┐
         │                               │                               │
         ▼                               ▼                               ▼
 ┌───────────────┐               ┌───────────────┐               ┌───────────────┐
 │ Static Lint & │               │ Dynamic Sim & │               │ Formal Verification│
 │  Elaboration  │               │   Cosim       │               │   & Equivalence │
 ├───────────────┤               ├───────────────┤               ├───────────────┤
 │ slang (IEEE)  │               │ Verilator sim │               │ SVA FPV (vcf) │
 │ Yosys read    │               │ Spike cosim   │               │ Formality LEC │
 │ Netlist check │               │ C++ cycle-sim │               │ Yosys SAT SEC │
 └───────────────┘               └───────────────┘               └───────────────┘
```

## Work at the netlist level

When an elaboration or simulation problem looks hard, ask **what the tool sees**, and
work at that level. Slang and Yosys do not reason about intent: they parse the emitted
text, build a netlist of cells and wires, and report on *that* structure.

- **Prefer structural checks to semantic ones.** "Same instance tree, same cell types,
  same connectivity" is O(size) and exact; a simulation that only sometimes catches a
  mismatch is weaker evidence than a structural check that always does.
- **Compare hierarchies as trees, not as flattened blobs.** Flattening converts a
  linear structure into a quadratic one; keep module boundaries, because they *are*
  the composition boundaries.
- **Treat routine escalation as a structural smell.** If an elaboration or a simulation
  needs special handling for one module, its structure has drifted; fix the structure,
  not the tool invocation.

## The proof ladder

**Every proof must be small and finish fast; bigger results come from composing
them.** A single long-running proof is a liability: it hides regressions behind a
timeout, cannot be parallelised, and sits on the critical path of every commit. Treat
sub-modules as already-proven theorems and prove only the few new facts each level
adds.

| Level | What is proven | Cost | Mechanism |
| :--- | :--- | :--- | :--- |
| Leaf behaviour | module meets its spec | < 1 s | Lean theorem (`native_decide`, `simp`) |
| Composition | parent correct given children | seconds | Lean `CompositionalCert` |
| Registry | certificates match the emitted circuits | instant | `lake exe generate_all --export-certs` |
| Smoke | integration sanity | < 2 s | parallel sim / Spike cosim sweep |

Rules that keep the ladder intact:

1. **Prove against the spec, not against another implementation.** A proof that
   inspects emitted RTL is a translation check masquerading as a theorem; it will be
   re-run forever and never composes.
2. **Compose, do not re-flatten.** A composite module is discharged by a **Lean
   composition proof**: the parent's spec follows from the children's theorems plus
   glue reasoning (`CompositionalCert`; see
   [Compositional Verification](#compositional-verification)). This is the
   axiom/theorem ladder, and the leaf theorems are the axioms.
3. **Keep the registry honest.** A `CompositionalCert` is only meaningful for a
   circuit that is actually emitted; `lake exe generate_all --export-certs` derives the
   dependencies from the circuit's instances and rejects a certificate that names a
   module the generator does not emit.
4. **Tier the work.** Commit and PR gates run the proofs, the registry check and a
   simulation/cosim smoke. A heavyweight sweep belongs in a nightly job, never on the
   commit path.
5. **Budget every proof.** If one module's proof dominates the build, decompose it. A
   proof that cannot finish in seconds is a decomposition bug.

### Shredding further: what atoms are still missing

The ladder is only as granular as its atoms. Today a module contributes a behavioural
model, a structural `Circuit`, and a handful of `native_decide` structural facts --
and the *join* between behaviour and structure is asserted in prose.
`CompositionalCert.proofReference` is a `String`, and the registry export checks only
that the named module is emitted, so a certificate can name a proof that does not exist
or no longer holds.

In order of leverage, the missing atoms are:

1. **`Circuit` satisfies `Behavior` (per module).** There is no circuit semantics in
   Lean, so nothing connects the structural `Circuit` to the behavioural model
   (`CPUBehavioral.cpuStep` and friends); the theorems talk about the model and the
   emitted RTL about the structure, and the two never meet. Add an evaluator
   (`eval : Circuit -> Wire -> Value`, gate by gate) and one refinement theorem per
   leaf. This is the atom that closes the gap.
2. **One generic composition lemma.** Given `eval child = childBehavior` for every
   child, a parent built from `CircuitInstance`s satisfies
   `eval parent = parentBehavior`. Prove this *once* over the hierarchical evaluator;
   afterwards every parent's atom is a one-line instantiation of its children's atoms.
   This is what makes an external equivalence check unnecessary.
3. **Per-building-block semantic lemmas.** `mkRippleCarryAdder n`, `mkMuxTree k w`,
   `mkRegisterN n`, `mkComparatorN n` should each carry a semantic lemma
   (`eval (rca n) a b = a + b`). Then adder -> ALU -> datapath is a chain of one-liners
   instead of a per-instance decision procedure.
4. **Machine-checked certificates.** Generate `CompositionalCert` entries *from* the
   composition-lemma instantiations, so a certificate exists only if its theorem
   type-checks and the registry cannot emit a dangling reference.
5. **Per-instruction ISA atoms.** Decoder proofs give coverage and non-overlap; add
   one semantic atom per opcode (`decode w = .X -> exec X s = spec X s`). An extension
   then arrives as N small atoms -- exactly the shape wanted for reviewing a new
   extension quickly.

Antipattern:

- **A cert with no proof.** A `CompositionalCert` is a *reference to* a Lean proof.
  Adding one to silence a hard module, without that proof existing, converts work into
  an unchecked assumption.

## The Chisel cross-check: removed

There is no cross-check any more. The Chisel backend and the Lean-vs-Chisel logical
equivalence check were removed, so there is no second RTL artifact to compare against.
What compensates is the Lean proofs (leaf behaviour and composition, per the ladder
above) plus the checks that run on the one emitted design: slang and Yosys elaboration,
Verilator simulation, and lock-step cosimulation against Spike.

## Compositional Verification

### When to use

Use a certificate when a module's correctness is easier to establish from its
sub-modules than in one step:

- **Large modules:** too much state to prove in a single theorem
- **Parametric construction:** the instances already carry their own proofs
- **Thin glue:** the parent is wiring and control around proven leaves

### How it works

1. Leaves carry their own Lean theorems.
2. The parent's spec is proven from the children's theorems plus glue reasoning, and
   the Lean namespace holding that proof is recorded in the certificate.
3. `lake exe generate_all --export-certs` derives the certificate's dependencies from
   the circuit's `instances` and rejects the registry if it is inconsistent with the
   emitted circuits.

### Certificate structure

Defined in `lean/Shoumei/Verification/Compositional.lean`:

```lean
structure CompositionalCert where
  moduleName : String              -- Module being verified
  proofReference : String          -- Lean namespace containing the composition proof
```

### Certificate registry

All certificates live in `lean/Shoumei/Verification/CompositionalCerts.lean`:

```lean
def register24_cert : CompositionalCert := {
  moduleName := "Register24"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

def allCerts : List CompositionalCert := [
  register24_cert,
  queue64_32_cert,
  ...
]
```

### Export mechanism

`ExportCerts.lean` prints one `module|deps|proofReference` line per certificate.
The dependency list is derived from the circuit's instances, not written by hand:

```bash
$ lake exe generate_all --export-certs
Mux64x32|Mux8x32|Shoumei.Circuits.Combinational.MuxTreeProofs
Register24|Register16,Register8|Shoumei.Circuits.Sequential.RegisterProofs
```

`make codegen` runs this after generating, so an inconsistent registry fails the run
instead of degrading verification quietly. The lines are also written to
`verification/compositional-certs.txt`.

## Module Ordering

`allCircuits` in `GenerateAll.lean` is in topological order (leaves first), so
dependency-aware hashes can be computed in a single pass and every sub-module is
emitted before the module that instantiates it.

## Troubleshooting

### slang reports errors on the emitted SV

The emitted text is not legal SystemVerilog. Fix the generator
(`lean/Shoumei/Codegen/`), not the emitted file -- `output/` is regenerated on every
run.

### Yosys `make systemverilog` fails

- A module is instantiated but absent from `allCircuits` in `GenerateAll.lean`
- Instance port names do not match the target module's ports exactly
- Clock/reset are not detected: check `findClockWires`/`findResetWires` in
  `Common.lean`, which look at DFF gates and instance connections

### The certificate registry fails to validate

The message names the module. Either delete the stale certificate or point it at the
circuit's current name; a certificate must name an emitted circuit, and every module
that circuit instantiates must be emitted too.

### Simulation diverges from Spike

Start with the cosimulation trace (see *Debugging RTL* in [CLAUDE.md](../CLAUDE.md)):
`MISMATCH` lines give the first diverging instruction, and `make -C testbench sim-trace`
plus `./scripts/fst_inspect` show the signal path that produced the wrong value.

## Running Verification

```bash
lake build                                                # Lean proofs
./verification/proof-coverage.sh                          # Proof coverage report
lake exe generate_all --export-certs                      # Validate + print the certificate registry
python3 verification/slang-lint.py output/sv-from-lean    # slang elaboration
make systemverilog                                        # Yosys read/hierarchy check
make sva                                                  # SVA formal/simulation checks (slang + Verilator)
make sec                                                  # Sequential Equivalence Checking (Yosys SAT)
./verification/sva-verify.sh --remote <host>              # Synopsys VC Formal FPV (industrial model checking)
./verification/sec-verify.sh --remote <host>              # Synopsys Formality LEC (industrial equivalence)
make -C testbench sim && make -C testbench run-all-tests  # Verilator simulation
make -C testbench cosim && make -C testbench run-cosim    # RTL vs Spike lock-step
./verification/smoke-test.sh                              # CI smoke tests
```

`run-cosim` sweeps the same ELF set as `run-all-tests` plus the generated
benchmark programs (`testbench/tests/generated/bench/*.elf`, built by the
`bench` dependency): the ISA suites, the hand-written custom tests, and every
benchmark body, all compared retirement-by-retirement against Spike.  A
benchmark that silently executes the wrong instruction stream therefore fails
cosim even when its own region check still passes.

### Benchmark numbers: peak vs whole-program IPC

Two different IPC numbers are reported per benchmark; do not compare them
with each other:

- **Peak IPC** (`BENCH <name> <thr> <lat>` lines, `output/bench/bench-metrics.csv`,
  published on the Pages `benchmarks.html`): in-program `1000*minstret/mcycle`
  over the throughput region only (e.g. `add` = 1.933).
- **Whole-program IPC** (`PASS add.elf (cycles, retired, IPC)` lines,
  `output/bench/bench-results-rtl.csv`): total retired over total cycles for
  the whole ELF, including the latency region, setup and IO (e.g. `add` = 1.578).

### Performance regression gate

`scripts/bench_regression.py` compares fresh metrics against the checked-in
`verification/bench-baseline.csv` (like with like: peak vs peak, dependent vs
dependent) and fails on any drop beyond 5% relative + 10 milli absolute. The
simulator is deterministic, so a failure is always a real RTL or benchmark
program change:

```bash
make -C testbench run-benchmarks   # full suite (main-branch benchmarks job)
make -C testbench bench-regression # 8-instr subset, one per execution path (PRs)
python3 scripts/bench_regression.py --metrics output/bench/bench-metrics.csv
```

To affirm an intended delta, merge the new numbers into the baseline and
commit it in the same PR that changes the microarchitecture:

```bash
python3 scripts/bench_regression.py --metrics output/bench/bench-metrics.csv \
    --baseline verification/bench-baseline.csv --update-baseline
```

### Via Make

```bash
make lean             # Lean build
make codegen          # generate_all + certificate registry export
make sva              # SVA verification (slang + Verilator --assert)
make sec              # Sequential Equivalence Checking (Yosys SAT miter)
make systemverilog    # Yosys read/hierarchy check
make cppsim           # compile the C++ simulation
make smoke-test       # codegen + smoke tests
make all              # the whole pipeline
```

## Adding a New Compositional Certificate

1. Write the composition proof in Lean (or point at existing proofs)
2. Add the `CompositionalCert` to `CompositionalCerts.lean`
3. Add it to `allCerts`
4. Run `lake build` to ensure it compiles
5. Run `lake exe generate_all --export-certs` to see it validate and print

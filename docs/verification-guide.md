# Verification guide

How Shoumei RTL convinces itself the design is correct: Lean proofs, the compositional
certificate registry, and the elaboration and simulation checks that run on the emitted
SystemVerilog.

## Verification architecture

Design correctness comes from the Lean proofs. The emitted SystemVerilog is one
translation of the proven `Circuit`, so no second RTL design exists to compare
against. The checks only confirm that the translation elaborates and runs.

| Layer | What it establishes | Mechanism |
| :--- | :--- | :--- |
| Leaf behaviour | module meets its spec | Lean theorem (`native_decide`, `simp`) |
| Composition | parent correct given children | Lean `CompositionalCert` |
| Equivalence (SEC) | alternative implementations preserve trace semantics | Lean bisimulation & SAT/LEC miters ([SEC Guide](proof-strategies/sequential-equivalence-checking.md)) |
| Formal Properties (SVA) | temporal assertion contracts hold on RTL | IEEE 1800 SVA FPV ([SVA Guide](proof-strategies/sva-formal-verification.md)) |
| Registry | every certificate matches an emitted circuit | `bazel run //generators:generate_all -- --export-certs` |
| Elaboration | the emitted SV is legal IEEE 1800-2017 SV | `bazel test //verification:slang_lint_test`, `bazel test //verification:yosys_validate_test` |
| Dynamic Simulation | RTL executes cycles correctly & assertions active | Verilator `--assert` (`bazel test //testbench/tests:all_sim`) |
| Co-simulation | retired instruction trace matches Spike reference | Spike lock-step cosimulation (`bazel test //testbench/tests:all_cosim`) |
| Compliance | RISC-V architectural compliance | 107/107 `riscv-arch-test` pass |

```
                      ┌──────────────────────────────────────┐
                      │    Lean 4 Mathematical Proofs        │
                      │  - L0 Structural Pinning             │
                      │  - L1 Functional Step Theorems       │
                      │  - L2 Inductive State Invariants     │
                      │  - L3 Temporal Refinement (Bisim)    │
                      └──────────────────┬───────────────────┘
                                         │ bazel build //:rtl
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
  same connectivity" is O(size) and exact. A simulation that only sometimes catches a
  mismatch is weaker evidence than a structural check that always does.
- **Compare hierarchies as trees, not as flattened blobs.** Flattening converts a
  linear structure into a quadratic one. Keep module boundaries, because they *are*
  the composition boundaries.
- **Treat routine escalation as a structural smell.** If an elaboration or a simulation
  needs special handling for one module, its structure has drifted. Fix the structure,
  not the tool invocation.

## The proof ladder

**Every proof must be small and finish fast. Bigger results come from composing
them.** A single long-running proof is a liability. It hides regressions behind a
timeout, cannot run in parallel, and sits on the critical path of every commit. Treat
sub-modules as already-proven theorems and prove only the few new facts each level
adds.

| Level | What it proves | Cost | Mechanism |
| :--- | :--- | :--- | :--- |
| Leaf behaviour | module meets its spec | < 1 s | Lean theorem (`native_decide`, `simp`) |
| Composition | parent correct given children | seconds | Lean `CompositionalCert` |
| Registry | certificates match the emitted circuits | instant | `bazel run //generators:generate_all -- --export-certs` |
| Smoke | integration sanity | < 2 s | parallel sim / Spike cosim sweep |

Rules that keep the ladder intact:

1. **Prove against the spec.** Do not prove against another implementation. A proof
   that inspects emitted RTL is a translation check, not a theorem. It will be
   re-run forever and never composes.
2. **Compose, do not re-flatten.** A **Lean composition proof** discharges a composite
   module: the parent's spec follows from the children's theorems plus
   glue reasoning (`CompositionalCert`, see
   [Compositional Verification](#compositional-verification)). This is the
   axiom/theorem ladder, and the leaf theorems are the axioms.
3. **Keep the registry honest.** A `CompositionalCert` is only meaningful for a
   circuit that the generator actually emits. `bazel run //generators:generate_all -- --export-certs` derives the
   dependencies from the circuit's instances and rejects a certificate that names a
   module the generator does not emit.
4. **Tier the work.** Commit and PR gates run the proofs, the registry check and a
   simulation/cosim smoke. A heavyweight sweep belongs in a nightly job, never on the
   commit path.
5. **Budget every proof.** If one module's proof dominates the build, decompose it. A
   proof that cannot finish in seconds is a decomposition bug.

### Shredding further: what atoms are still missing

The ladder is only as granular as its atoms. Today a module contributes a behavioural
model, a structural `Circuit`, and a handful of `native_decide` structural facts, and
the *join* between behaviour and structure rests only on prose.
`CompositionalCert.proofReference` is a `String`, and the registry export checks only
that the generator emits the named module. A certificate can therefore name a proof
that does not exist or no longer holds.

The verification ladder builds from verified leaf atoms to composed pipelines:

1. **`Circuit` satisfies `Behavior` (per module).** Circuit semantics (`Semantics.lean`,
   `Semantics/Hierarchical.lean`) and refinement relations (`Verification/Implements.lean`)
   connect structural `Circuit`s to behavioural models. The typed refinement registry
   (`Verification/Refinements.lean`) records `RefinementAtom` entries (pilot atoms cover
   `FullAdder`, `LogicUnit4`, `Mux4x1`, `Mux4x32`, `Mux8x32`, `RippleCarryAdder4`,
   `Comparator4`, `Popcount8`, `ALU32`, `DFlipFlop`, `Register160`, and `Queue1_1`).
2. **Generic composition lemmas.** `implements_compose` and
   `implementsComb_compose` in `Verification/Implements.lean` prove these. Given
   refinements for every child, a parent built from `CircuitInstance`s inherits its
   refinement. It needs no re-flattening or re-verification from scratch (demonstrated
   on `Mux8x32` and `Register160`).
3. **Per-building-block semantic lemmas.** `mkRippleCarryAdder n`, `mkMuxTree k w`,
   `mkRegisterN n`, `mkComparatorN n` carry semantic evaluation lemmas
   (`rca4_arithmetic_correct`, `evalGates_mux2Bit_result`, and more), allowing composition
   chains instead of per-instance decision procedures.
4. **Machine-checked refinement registry.** `RefinementAtom` entries require both a proof term and a *non-vacuity* proof at construction time (`bazel run //generators:generate_all -- --export-refinements`). That witness is a `NonVacuousBehavior` / `NonVacuousCombBehavior` proof that the behavioural model produces distinct outputs. This prevents dangling references, unproven claims, and tautological/constant specifications from registering.
5. **Per-instruction ISA atoms.** Decoder proofs give coverage and non-overlap. The
   `ALU32` atom covers all 10 RV32I opcodes over all inputs. Expanding to remaining
   instruction classes connects execution units directly to the ISA specification.

Antipattern:

- **A cert with no proof.** A `CompositionalCert` is a *reference to* a Lean proof.
  Adding one to silence a hard module, without that proof existing, converts work into
  an unchecked assumption.

## The Chisel cross-check: removed

No cross-check remains. This repository dropped the Chisel backend and the
Lean-against-Chisel logical equivalence check, so no second RTL artifact exists
to compare against.
The Lean proofs compensate (leaf behaviour and composition, per the ladder above).
The checks that run on the one emitted design compensate too: slang and Yosys
elaboration, Verilator simulation, and lock-step cosimulation against Spike.

## Compositional verification

### When to use

Use a certificate when a module's correctness is easier to establish from its
sub-modules than in one step:

- **Large modules:** too much state to prove in a single theorem
- **Parametric construction:** the instances already carry their own proofs
- **Thin glue:** the parent is wiring and control around proven leaves

### How it works

1. Leaves carry their own Lean theorems.
2. The children's theorems plus glue reasoning prove the parent's spec. The
   certificate records the Lean namespace holding that proof.
3. `bazel run //generators:generate_all -- --export-certs` derives the certificate's dependencies from
   the circuit's `instances` and rejects the registry if it is inconsistent with the
   emitted circuits.

### Certificate structure

`lean/Shoumei/Verification/Compositional.lean` defines it:

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
The tool derives the dependency list from the circuit's instances, not by hand:

```bash
$ bazel run //generators:generate_all -- --export-certs
Mux64x32|Mux8x32|Shoumei.Circuits.Combinational.MuxTreeProofs
Register24|Register16,Register8|Shoumei.Circuits.Sequential.RegisterProofs
```

`bazel build //:rtl` runs this validation, so an inconsistent registry fails the build
instead of degrading verification quietly. The lines are also written to
`verification/compositional-certs.txt`.

## Module ordering

`allCircuits` in `GenerateAll.lean` is in topological order (leaves first). The
generator can therefore compute dependency-aware hashes in a single pass. It emits
every sub-module before the module that instantiates it.

## Troubleshooting

### slang reports errors on the emitted SV

The emitted text is not legal SystemVerilog. Fix the generator
(`lean/Shoumei/Codegen/`), not the emitted file. The build regenerates `output/` on every
run.

### Yosys `bazel test //verification:yosys_validate_test` fails

- The design instantiates a module that `allCircuits` in `GenerateAll.lean` does not list
- Instance port names do not match the target module's ports exactly
- Clock/reset are not detected: check `findClockWires`/`findResetWires` in
  `Common.lean`, which look at DFF gates and instance connections

### The certificate registry fails to validate

The message names the module. Either delete the stale certificate or point it at the
circuit's current name. A certificate must name an emitted circuit, and the generator
must emit every module that circuit instantiates too.

### Simulation diverges from Spike

Start with the cosimulation trace (see *Debugging RTL* in [AGENTS.md](../AGENTS.md)).
`MISMATCH` lines give the first diverging instruction. `bazel run //testbench:sim_shoumei_trace`
plus `bazel run //tools:fst_inspect` show the signal path that produced the wrong value.

## Running verification

```bash
bazel build //lean:shoumei                                # Lean proofs
bazel run //generators:generate_all -- --export-certs               # Validate + print certificate registry
bazel test //verification:linters                         # slang, shellcheck, python, cppcheck
bazel test //verification:formal                          # SVA formal, SEC miter, bridge validation
bazel test //testbench:all_tests                          # Verilator simulation, Spike cosim, spec tests
bazel test //:presubmit                                   # Full presubmit suite (311 tests)
```

`//testbench:cosim_tests` sweeps the test programs and generated benchmarks, comparing execution retirement-by-retirement against Spike.

### Benchmark numbers: peak vs whole-program IPC

Benchmarks report two different IPC numbers. Do not compare them with each other:

- **Peak IPC** (`BENCH <name> <thr> <lat>` lines,
  published on the Pages `benchmarks.html`): in-program `1000*minstret/mcycle`
  over the throughput region only (for example `add` = 1.933).
- **Whole-program IPC** (`PASS add.elf (cycles, retired, IPC)` lines):
  total retired over total cycles for the whole ELF, including latency region,
  setup, and IO.

### Performance regression gate

`//testbench/benchmarks` gates the 8-path instruction subset against `verification/bench-baseline.csv`:

```bash
bazel test //testbench/benchmarks
```

## Adding a new compositional certificate

1. Write the composition proof in Lean (or point at existing proofs)
2. Add the `CompositionalCert` to `CompositionalCerts.lean`
3. Add it to `allCerts`
4. Run `bazel build //lean:shoumei` to ensure it compiles
5. Run `bazel run //generators:generate_all -- --export-certs` to see it validate and print

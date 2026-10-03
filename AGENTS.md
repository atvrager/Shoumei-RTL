Communicate only in Simplified Technical English (ASD-STE100).

# Development Context

> **Start here:** [docs/project-map.md](docs/project-map.md) comes from the
> source tree (`bazel run //generators:generate_all -- --project-map`). It shows the subsystem
> composition graph, per-circuit coverage (certificate / proofs / doc comment),
> and the mechanical gaps. Re-run the generator after adding a module.
>
> This file is the single source of truth for agent guidance. `GEMINI.md` and
> `agent.md` are symlinks to it, so only one copy needs maintenance.

Instructions and procedures for working on the Shoumei RTL project.

## Project summary

"Formally verified" hardware design. Circuits live in a Lean 4 DSL, and dependent types prove the properties. Code generators emit SystemVerilog, a flat netlist, ASAP7 tech-mapped gates and a cycle-accurate C++ model from the same proven source.

**Current state:** 87 modules, complete `RV64IMAFD_Zicsr_Zifencei` (RV64G)
Out-of-Order (OoO) CPU (microcoded TrapSequencer, LR/SC/AMO, double-precision FPU,
107/107 architectural compliance pass, 0 axioms). ASIC flows for
GF180MCU (64 MHz) and ASAP7 (1.0 GHz). See [docs/ROADMAP.md](docs/ROADMAP.md).

## Key toolchain versions

- **Bazel:** 8.x / Bazelisk (single entry point for all builds, tests, and generation)
- **Lean 4:** v4.34.1 (controlled by `lean-toolchain`, built through `@rules_lean`)
- **Yosys:** 0.68 (`@yosys`, built from source in the sandbox)
- **Verilator:** 5.046 (`@verilator`, built from source in the sandbox)
- **RISC-V GCC:** xpack `riscv-none-elf` 15.2.0 (`@riscv_gcc`)
- **slang:** `pyslang` 12.0.0 (`@pip`), used by `verification/slang-lint.py`

Bazel fetches these tools from a pinned URL or builds them from a pinned
source. No script probes the host PATH. See [docs/host-tools.md](docs/host-tools.md)
for the scripts that still need a host tool.

## Build commands

```bash
bazel build //lean:shoumei               # Build Lean proofs
bazel build //generators:generate_all              # Build native code generator binary
bazel build //:rtl                       # Generate SV + netlist + ASAP7 + C++ Sim + testbenches
bazel test //:presubmit                  # Run complete presubmit test suite (311 tests)

# Targeted test suites
bazel test //testbench:sim_tests         # Verilator standalone simulations
bazel test //testbench:cosim_tests       # RTL vs Spike lockstep cosimulations
bazel test //testbench:spec_tests        # Specification reference simulations
bazel test //testbench:all_tests         # All simulation suites combined
bazel test //testbench/coverage_test     # Hardware line coverage test
bazel test //verification:linters        # Slang, shellcheck, python, types, buildifier, prose, lean lint
bazel test //verification:formal         # Formal verification & SEC
bazel test //verification:synthesis      # Yosys ASAP7 & GF180MCU synthesis
bazel test //testbench/benchmarks        # Benchmark IPC regression test
```

## Procedure: Adding a new module

This is the core workflow. Every module follows the same pattern. See [docs/adding-a-module.md](docs/adding-a-module.md) for the full walkthrough.

For adding an **ISA extension** (new opcodes: decode, classify, execute, verify),
see [docs/adding-an-extension.md](docs/adding-an-extension.md).

### Summary

1. **Behavioral model:** Define state type + operations in Lean
2. **Structural circuit:** Build `Circuit` from gates and/or `CircuitInstance` submodules
3. **Proofs:** Structural (`native_decide`) and behavioral (`simp`, manual tactics)
4. **Code generation:** Add to the `generators/GenerateAll.lean` circuit list, then `bazel build //:rtl`
5. **Compositional cert** (if needed): Add to `CompositionalCerts.lean`. `bazel run //generators:generate_all -- --export-certs` checks the registry
6. **Simulation:** `bazel test //testbench/tests:all_sim`, or `bazel test //testbench/tests:all_cosim` for CPU-level changes

### Where files go

| Component | Location |
|-----------|----------|
| Combinational circuits | `lean/Shoumei/Circuits/Combinational/` |
| Sequential circuits | `lean/Shoumei/Circuits/Sequential/` |
| RISC-V components | `lean/Shoumei/RISCV/` (with subdirs `Execution/`, `Renaming/`) |
| Proofs | Same directory as circuit, with `Proofs` suffix |
| Codegen wrappers | Same directory as circuit, with `Codegen` suffix |
| Compositional certs | `lean/Shoumei/Verification/CompositionalCerts.lean` |

## Procedure: Verification

See [docs/verification-guide.md](docs/verification-guide.md) for full details.

Lean establishes correctness. The emitted SystemVerilog is a translation of
the proven `Circuit`. The checks below confirm that this translation elaborates
and runs. No second RTL design exists to compare against.

- **Lean proofs:** structural and behavioral theorems live next to each circuit.
  `bazel build //lean:shoumei` checks them, and `bazel test //verification:proof_coverage_test` reports coverage.
- **Compositional certificate registry:** a `CompositionalCert` names a module, its
  dependencies and its composition proof. `bazel run //generators:generate_all -- --export-certs`
  derives each certificate's dependencies from the circuit's instances. It fails if a
  certificate names a module the generator does not emit.
- **slang elaboration:** `bazel test //verification:slang_lint_test`
  parses and elaborates every emitted SV file (IEEE 1800-2017). `bazel test //verification:yosys_validate_test`
  runs the equivalent Yosys read/hierarchy check.
- **Verilator simulation:** `bazel test //testbench/tests:all_sim` runs the standalone RTL simulation.
- **RISC-V cosimulation:** `bazel test //testbench/tests:all_cosim` compares the RTL
  against Spike lockstep on the retired RVVI trace.

### Compositional certificates (large sequential modules)

For a module too large to discharge in one step, justify it from its building blocks:

1. Define a `CompositionalCert` in `lean/Shoumei/Verification/CompositionalCerts.lean`
2. Add it to `allCerts`
3. `bazel run //generators:generate_all -- --export-certs` validates the registry against the emitted
   circuits and prints one `Module|deps|proofReference` line per certificate

The dependencies are not written by hand. They are the modules the circuit
instantiates, so a certificate cannot rest on an incomplete premise or name a
module that is no longer emitted.

A certificate in `allCerts` covers a module that is too large to discharge in
one step. Codegen validates the registry.

### Running verification

```bash
bazel test //verification:linters        # Slang, shellcheck, python, types, buildifier, prose, lean lint
bazel test //verification:formal         # Formal proofs and SEC
bazel test //testbench:all_tests         # Verilator simulation, cosim, and spec tests
bazel test //verification:synthesis      # Yosys ASAP7 and GF180MCU synthesis
bazel test //:presubmit                  # Complete presubmit suite
python3 verification/ste-lint.py --all   # ASD-STE100 prose lint
```

### Continuous integration

`.github/workflows/ci.yml` runs one job per slice of `//:presubmit`, so the
slices use separate runners. The `warm` job builds the Lean library and the
code generators first. The other jobs restore the Bazel action cache and
repository cache that `warm` saved. Each job then runs only its own slice.

Run `bazel test //:presubmit` before a push to run every slice on one machine.

### Prose lint (ASD-STE100)

`verification/ste-lint.py` checks human prose against mechanical Simplified
Technical English rules. The tool has no approved-word list, so it runs
offline: every rule is a regex or a length limit. It reads markdown,
code comments, and commit messages.

Rules: sentence length, semicolons, contractions, Latin abbreviations,
wordy phrases, praise and filler, passive voice, long paragraphs, and
`there is/are` (STE001-STE009). `--strict` turns warnings into errors.

`githooks/pre-commit` lints the lines a commit adds, and `githooks/commit-msg`
lints the message. Both install with `scripts/install-githooks.sh`. Set
`STE_LINT_DISABLE=1` to skip them. Write `ste-lint: ignore` in a line to
exclude text that is data, not prose.

`bazel test //verification:ste_lint_test` runs the rule tests and lints the
Markdown tree.

### Bazel file format

`buildifier` checks every BUILD and .bzl file.

```bash
bazel run //:buildifier       # Format the tree in place
bazel test //:buildifier_test # Fail on an unformatted file
```

The pre-commit hook runs the same check on the staged Bazel files. Rule files
live in `rules/`.

## DSL core types

Defined in `lean/Shoumei/DSL.lean`:

```lean
structure Wire where name : String
inductive GateType where | AND | OR | NOT | XOR | BUF | MUX | DFF
structure Gate where gateType : GateType; inputs : List Wire; output : Wire
structure CircuitInstance where moduleName : String; instName : String; portMap : List (String × Wire)
structure Circuit where name : String; inputs : List Wire; outputs : List Wire;
                        gates : List Gate; instances : List CircuitInstance
```

**Two ways to build circuits:**
- **Flat:** Direct gate lists (good for small combinational circuits)
- **Hierarchical:** `CircuitInstance` references to other verified modules (good for large/sequential)

## Code generation architecture

The generators in `lean/Shoumei/Codegen/`, driven by `Unified.lean`:

| Generator | File | Output |
|-----------|------|--------|
| SystemVerilog | `SystemVerilog.lean` | `output/sv-from-lean/*.sv` (hierarchical) |
| SystemVerilog Netlist | `SystemVerilogNetlist.lean` | `output/sv-netlist/*.sv` (flat) |
| ASAP7 tech mapping | `ASAP7.lean` | `output/sv-asap7/*.sv` |
| C++ Simulation | `CppSim.lean` | `output/cpp_sim/*.{h,cpp}` |
| Testbench | `Testbench.lean` | `testbench/generated/` |

Shared utilities in `Common.lean`:
- `findClockWires` / `findResetWires`: detect clock/reset from DFF gates AND instance connections
- Signal group detection and bus reconstruction (data_0..data_31 to logic [31:0])
- Wire-to-index mapping for typed signals

### Adding a circuit to code generation

In `generators/GenerateAll.lean`, add to the `allCircuits` list:

```lean
def allCircuits : List Circuit := [
  fullAdderCircuit,
  yourNewCircuit,
  ...
]
```

The centralized codegen emits everything in the list:
- SystemVerilog (hierarchical)
- SystemVerilog netlist (flat)
- ASAP7 tech-mapped SV
- C++ Simulation (.h + .cpp)
- Testbenches

## Proof patterns

### Structural proofs (concrete circuits)

```lean
theorem myCircuit_gate_count : myCircuit.gates.length = 42 := by native_decide
theorem myCircuit_ports : myCircuit.inputs.length = 5 := by native_decide
```

### Behavioral proofs (state machines)

```lean
-- For small state spaces, native_decide works
theorem queue_fifo : enqueue_then_dequeue preserves_order := by native_decide

-- For generic proofs, use simp + manual tactics
theorem prf_read_after_write (tag : Fin n) (val : UInt32) :
    (state.write tag val).read tag = val := by simp [write, read]
```

### Proof strategies for parameterized circuits

See [docs/proof-strategies.md](docs/proof-strategies.md) for two approaches:
1. **Structural induction + list lemmas:** works for all parameterized circuits
2. **BitVec semantic bridge:** uses `bv_decide` for arithmetic proofs

### Interactive proof development with Lean LSP

See [docs/lean-lsp-guide.md](docs/lean-lsp-guide.md) for a guide to the Lean LSP tools:
- **`lean_multi_attempt`:** test multiple tactics without editing files
- **`lean_goal`:** inspect proof states and goal transformations
- **`lean_run_code`:** execute standalone code snippets
- **Search tools:** find lemmas in Mathlib (leansearch, loogle, leanfinder)
- **`lean_profile_proof`:** performance analysis of proofs
- Error diagnosis and debugging workflows

## Architecture decisions

### Why generate the RTL from Lean?

- **SystemVerilog from Lean:** one direct translation of the proven `Circuit`, so no second design needs to stay in sync
- **The Lean theorems are the correctness argument:** structural proofs pin the circuit, behavioral proofs pin the model
- **Tests check the emitted RTL:** slang elaboration, Verilator simulation, and lock-step cosimulation against Spike

### Why hierarchical circuits with instances?

Build large sequential modules (Register91, Queue64, PhysRegFile) from verified leaves with `CircuitInstance` instead of one flat gate list.
- each module stays small enough to prove and to read
- module boundaries survive into the emitted SV and drive the ASAP7 tech mapping
- a composition too large to discharge in one step gets a `CompositionalCert` whose dependencies are the circuit's instances

### Module ordering

`allCircuits` in `generators/GenerateAll.lean` is in topological order (leaves first), so the generator can compute dependency-aware hashes in a single pass.

## Agent guidance and code quality rules

Adapted from [Fabien Sanglard's agent.md](https://fabiensanglard.net/agent.md/):

### Interaction and communication
- **Brevity:** When writing something intended for human consumption (comments, commit messages, replies to prompts), use as few words as possible. Pick every word meticulously to reduce the volume to a strict minimum. Be down to the point. Less is more.
- **Directness:** Avoid superlatives and praise. Give the cold, hard truth without sugarcoating.
- **No ANSI formatting:** Always run tools without ANSI escape codes (for example, `lake --no-ansi`, `NO_COLOR=1`). This prevents terminal log pollution and keeps transcripts machine- and human-readable. All Lake invocations must explicitly use `lake --no-ansi`, and a wrapper enforces `--no-ansi` automatically.

### Code style and architecture
- **No magic numbers or strings:** Extract recurring or meaningful values into descriptive constants (`const`/`def`) or enums/inductives. Keep self-explanatory, one-off values inline to avoid clutter. If a value comes from a spec (for example, RISC-V opcodes, funct fields), use a constant regardless.
- **Flatten control flow:** Reduce code indentation. Avoid the Arrow Anti-Pattern. Use early returns and pattern matching.
- **Function naming:** Keep function names short (< 30 characters).
- **Type safety:** Use enums/inductives instead of booleans for function parameters.
- **Readability:** Let the reader of the code breathe. Add empty lines between logical blocks of code.
- **Intentional comments:** Add small, to-the-point comments explaining *what* the block does and *why*. Use examples when possible. Propose ASCII drawings to explain complex systems.
- **Levels of abstraction:** Put lower-level mechanics in a dedicated driver/abstraction layer. Raw hardware I/O, sector parsing and direct socket streams are examples. Expose clean, high-level APIs to the rest of the application. Then calling code works with domain concepts, not raw implementation details.
- **Layered boundaries:** Adhere to the layered boundary hierarchy: each layer communicates only with its immediate neighbor directly below it. Never "punch holes" through layers. For example, controllers or UI components must never directly call database queries, raw hardware drivers, or low-level network clients. Always route through the intermediate service/abstraction layer.
- **Minimal diffs:** Do not touch blocks of code unrelated to the feature you implement. Minimize changed lines.
- **Explicit blocks:** Always use explicit block delimiters (for example, `{}` in C/C++/Scala), even on a one-line `if` statement.

### Bug fixing workflow
- If fixing a bug, do NOT write the fix right away. First write the test. Observe it failing. Then write the fix, and observe the test passing.

### Commit messages
When writing a commit message, follow these 7 rules.
- **Rule 1:** Separate the subject line from the body with a single blank line.
- **Rule 2:** Limit the subject line to 50 characters (72 is the absolute hard limit).
- **Rule 3:** Capitalize the first letter of the subject line.
- **Rule 4:** Do not end the subject line with a period.
- **Rule 5:** Use the imperative mood in the subject line (for example, "Fix bug," "Add feature," not "Fixed" or "Adds"). Test formula: It must complete the sentence: "If applied, this commit will [your subject line here]".
- **Rule 6:** Wrap the body text manually at 72 characters to prevent Git formatting issues.
- **Rule 7:** Use the body to explain what and why, not how. Assume the code explains how. The message must explain the context and reasoning.

## Code style and quality

### Lean

- Follow [Lean 4 style guide](https://github.com/leanprover/lean4/blob/master/doc/style.md)
- No `sorry` in production code (treat as a bug)
- Use `native_decide` for concrete proofs, `simp` + tactics for generic proofs
- Keep circuits and proofs in separate files (`Foo.lean` + `FooProofs.lean`)

`bazel test //verification:lean_lint_test` runs the style linter
(`lean/Shoumei/Lint/`).

```bash
bazel run //generators:lean_lint                    # Report every finding
bazel run //generators:lean_lint -- --print-fix FILE  # Show the reflow, write nothing
bazel run //generators:lean_lint -- --fix           # Reflow the long lines
```

It reports an error for `sorry` or `admit` in the code, an `axiom` or
`constant` declaration, a `#eval`/`#check`/`#print`/`#reduce` command left in
the source, trailing whitespace, and a tab character.

The line-width rule (LEAN006) is a ratchet. `lean-lint-baseline.txt` records
how many lines of code over 100 columns each file carries, and the count may
only fall. `--fix` reflows a line at the last space that keeps the first part
inside the limit, and never breaks a string literal, because that would change
the value. Run `--update-baseline` after a fix to record the lower count. Use
the marker `lean-lint: ignore` on a line that a rule cannot settle.

`--fix` rewrites files in place. It refuses to run if git shows a changed,
staged or untracked `.lean` file under the paths. Commit first, so that
`git checkout` can undo a bad reflow. Build the result before you commit it.

### Python

`ruff` checks lint and format. `ty` checks types.

```bash
bazel test //tools:ruff_test   # ruff check and ruff format --check
bazel test //tools:ty_test     # ty check
```

Both tools are pinned prebuilt binaries (`rules/lint_tools.bzl`), so nothing
is installed on the host. Annotate every function, arguments and return type.
Line length is 100 and the formatter owns it.

### Shell scripts

All shell scripts must pass shellcheck:
```bash
shellcheck verification/smoke-test.sh
```

### SystemVerilog

IEEE 1800-2017 compliant, synthesizable subset only.

## Debugging RTL

### Cosimulation (primary debugging tool)

The cosimulation compares the RTL against the Spike reference model in lock-step. It shows the exact instruction where the RTL diverges:

```bash
bazel run //testbench:sim_shoumei_cosim -- +elf=path/to/failing_test.elf
```

Output format: `DBG ret#N cyC: PC=0x... insn=0x... rd=xR(wr) data=0x... | Spike: ...`
- `MISMATCH` lines pinpoint the first divergence
- Check the `data` field for wrong register values (for example, a load returning 0 instead of the expected value)

### FST waveform traces

```bash
bazel run //testbench:sim_shoumei_trace -- +trace +elf=path/to/test.elf
bazel run //tools:fst_inspect -- shoumei_cpu.fst --list
bazel run //tools:fst_inspect -- shoumei_cpu.fst --cycles 60-100 --signals "rvvi_valid,rvvi_pc_rdata"
```

Key signals for memory path debugging:
- `load_fwd_valid` / `load_no_fwd`: which path a load takes (SB fwd or DMEM)
- `lsu_sb_fwd_hit`: store buffer forwarding hit
- `lsu_valid` / `lsu_fifo_enq_ready`: FIFO enqueue handshake
- `pipeline_flush_comb`: pipeline flush events

### Debugging workflow

1. Run cosim to find the diverging instruction and wrong data value
2. Use FST trace to inspect the signal path that produced the wrong value
3. Check timing of store-buffer commits against load dispatches for memory ordering issues

## Important notes

- **NEVER edit files in `output/` or `testbench/generated/`.** `bazel build //:rtl` generates these, and every regeneration overwrites them. All changes must go in the Lean source files under `lean/`. If the generated output is wrong, fix the code generator (`lean/Shoumei/Codegen/`), not the generated file.
- **origin/main has no pre-existing test failures.** GitHub branch protection requires CI to pass before merging. If tests fail on your branch, you introduced the regression. Do not assume failures are pre-existing.
- Always read existing Lean files before modifying
- `hasSequentialElements` checks DFF gates only, NOT instances. Use `findClockWires`/`findResetWires`, which check both
- The `generate_all` executable is the recommended codegen entry point (does SV + netlist + ASAP7 + C++ Sim + testbenches)

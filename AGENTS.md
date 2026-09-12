# Claude Development Context

> **Start here:** [docs/project-map.md](docs/project-map.md) is generated from
> the source tree (`scripts/gen-project-map.py`) and shows the subsystem
> composition graph, per-circuit coverage (certificate / proofs / doc comment),
> and the mechanical gaps.  Re-run the generator after adding a module.
>
> This file is the single source of truth for agent guidance.  `CLAUDE.md`,
> `GEMINI.md`, and `agent.md` are symlinks to it, so there is one copy to keep current.


Instructions and procedures for working on the Shoumei RTL project.

## Project Summary

Formally verified hardware design: circuits defined in Lean 4 DSL, properties proven with dependent types, dual code generators produce SystemVerilog + Chisel, Yosys LEC verifies equivalence.

**Current state:** 89 modules, 100% LEC coverage, complete `RV32IMAF_Zicsr_Zifencei`
Tomasulo CPU (A extension: `LR.W`/`SC.W`/`AMO*.W`). See
[RISCV_TOMASULO_PLAN.md](RISCV_TOMASULO_PLAN.md) for roadmap.

## Key Toolchain Versions

- **Lean 4:** v4.27.0 (controlled by `lean-toolchain`)
- **Chisel:** 7.7.0 (in `chisel/build.sbt`)
- **Scala:** 2.13.18 (required for Chisel 7.x)
- **Yosys:** system package (for LEC)
- **CIRCT/firtool:** 1.140.0 (for arcilator simulation backend; install via `scripts/install-circt.sh`)
- **RISC-V GCC:** `riscv32-unknown-elf-gcc` at `~/.local/riscv32-elf/bin/` (add to PATH for test compilation)

## Build Commands

```bash
lake --no-ansi build                # Build Lean proofs + code generators
lake --no-ansi exe generate_all     # Generate SV + Chisel + C++ Sim for all modules
cd chisel && sbt run && cd ..       # Compile Chisel -> SV via CIRCT
./verification/run-lec.sh           # Verify Lean SV == Chisel SV
make all                            # Run entire pipeline

# RISC-V test compilation and simulation
export PATH="$HOME/.local/riscv32-elf/bin:$PATH"
make -C testbench/tests             # Compile C tests -> ELF binaries
make -C testbench sim               # Build Verilator simulation (X-prop on by default)
make -C testbench run-all-tests     # Run all ELF tests (Verilator)
make -C testbench cosim       # Build Verilator cosim (auto-builds Spike)
make -C testbench run-cosim   # RTL vs Spike lock-step cosim (Verilator)

# Arcilator simulation (CIRCT/MLIR/LLVM-based, requires scripts/install-circt.sh)
scripts/install-circt.sh            # Install CIRCT 1.140.0 (firtool, arcilator, circt-verilog)
make -C testbench sim-arc           # Build Arcilator simulation
make -C testbench run-all-tests-arc # Run all ELF tests (Arcilator)
make -C testbench cosim-arc         # Build Arcilator cosim
make -C testbench run-cosim-arc     # RTL vs Spike lock-step cosim (Arcilator)
```

## Procedure: Adding a New Module

This is the core workflow. Every module follows the same pattern. See [docs/adding-a-module.md](docs/adding-a-module.md) for the full walkthrough.

For adding an **ISA extension** (new opcodes: decode -> classify -> execute -> verify),
see [docs/adding-an-extension.md](docs/adding-an-extension.md).

### Summary

1. **Behavioral model** -- Define state type + operations in Lean
2. **Structural circuit** -- Build `Circuit` from gates and/or `CircuitInstance` submodules
3. **Proofs** -- Structural (`native_decide`) and behavioral (`simp`, manual tactics)
4. **Code generation** -- Add to `GenerateAll.lean` circuit list
5. **Chisel compilation** -- `cd chisel && sbt run` (auto-discovers new modules)
6. **LEC verification** -- `./verification/run-lec.sh`
7. **Compositional cert** (if needed) -- Add to `CompositionalCerts.lean` + `ExportVerificationCerts.lean`

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

### Direct LEC (most modules)

Yosys compares Lean-generated SV against Chisel-generated SV:
- **Combinational:** SAT-based miter circuit
- **Sequential:** Induction-based equivalence (`equiv_make` / `equiv_induct`)
- Auto-detected by checking for `always @` blocks

### Compositional Verification (large sequential modules)

For modules too large or structurally different for direct SEC:
1. LEC-verify all building block submodules
2. Define a `CompositionalCert` in Lean with module name, dependencies, proof reference
3. Export via `lake exe export_verification_certs`
4. LEC script loads certs, checks all deps are verified, accepts compositional proof

Currently 9 modules use compositional verification:
Register91, Queue64_32, Queue64_6, QueueRAM_64x32, QueueRAM_64x6,
PhysRegFile_64x32, RAT_32x6, FreeList_64, ReservationStation4

### Running verification

```bash
./verification/run-lec.sh                              # All modules
./verification/smoke-test.sh                           # Full CI pipeline
```

## DSL Core Types

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

## Code Generation Architecture

Four code generators in `lean/Shoumei/Codegen/`:

| Generator | File | Output |
|-----------|------|--------|
| SystemVerilog | `SystemVerilog.lean` | `output/sv-from-lean/*.sv` (hierarchical) |
| SystemVerilog Netlist | `SystemVerilogNetlist.lean` | `output/sv-netlist/*.sv` (flat) |
| Chisel | `Chisel.lean` | `chisel/src/main/scala/generated/*.scala` |
| C++ Simulation | `CppSim.lean` | `output/cpp_sim/*.{h,cpp}` |

Shared utilities in `Common.lean`:
- `findClockWires` / `findResetWires` -- detect clock/reset from DFF gates AND instance connections
- Signal group detection and bus reconstruction (data_0..data_31 → logic [31:0])
- Wire-to-index mapping for typed signals

### Adding a circuit to code generation

In `GenerateAll.lean`, add to the `allCircuits` list:

```lean
def allCircuits : List Circuit := [
  fullAdderCircuit,
  yourNewCircuit,
  ...
]
```

The centralized codegen generates all 4 outputs for everything in the list:
- SystemVerilog (hierarchical)
- SystemVerilog netlist (flat)
- Chisel → SystemVerilog via CIRCT
- C++ Simulation (.h + .cpp)

## Proof Patterns

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
1. **Structural induction + list lemmas** -- works for all parameterized circuits
2. **BitVec semantic bridge** -- uses `bv_decide` for arithmetic proofs

### Interactive Proof Development with Lean LSP

See [docs/lean-lsp-guide.md](docs/lean-lsp-guide.md) for comprehensive guide to Lean LSP tools:
- **`lean_multi_attempt`** -- test multiple tactics without editing files
- **`lean_goal`** -- inspect proof states and goal transformations
- **`lean_run_code`** -- execute standalone code snippets
- **Search tools** -- find lemmas in Mathlib (leansearch, loogle, leanfinder)
- **`lean_profile_proof`** -- performance analysis of proofs
- Error diagnosis and debugging workflows

## Architecture Decisions

### Why dual generation (SV + Chisel)?

- **SystemVerilog from Lean:** Direct translation, proves semantics are correct
- **Chisel from Lean:** Leverages mature FIRRTL/CIRCT toolchain, more optimized output
- **LEC between them:** Validates both generators produce equivalent circuits
- LEC is a sanity check; the real proof is in Lean

### Why hierarchical circuits with instances?

Large sequential modules (Register91, Queue64, PhysRegFile) have structural differences between Lean SV and Chisel SV that make direct SEC fail. Hierarchical composition with `CircuitInstance` solves this:
- LEC verifies leaf modules directly
- Lean proves the composition is correct
- Compositional certificates connect the two

### Topological sorting in LEC

The LEC script processes modules in dependency order (using `tsort`). This ensures building blocks are verified before the modules that depend on them, so compositional certificates can check their dependency requirements.

## Agent Guidance & Code Quality Rules

Adapted from [Fabien Sanglard's agent.md](https://fabiensanglard.net/agent.md/):

### Interaction & Communication
- **Brevity:** When writing something intended for human consumption (comments, commit messages, replies to prompts), use as few words as possible. Pick every word meticulously to reduce the volume to a strict minimum. Be down to the point. Less is more.
- **Directness:** Avoid superlatives and praise. Give the cold, hard truth without sugarcoating.
- **No ANSI formatting:** Always run tools without ANSI escape codes (e.g., `lake --no-ansi`, `NO_COLOR=1`) to prevent terminal log pollution and keep transcripts machine- and human-readable.

### Code Style & Architecture
- **No magic numbers or strings:** Extract recurring or meaningful values into descriptive constants (`const`/`def`) or enums/inductives. Keep self-explanatory, one-off values inline to avoid clutter. If a value comes from a spec (e.g. RISC-V opcodes, funct fields), use a constant regardless.
- **Flatten control flow:** Reduce code indentation. Avoid the Arrow Anti-Pattern. Leverage early returns and pattern matching.
- **Function naming:** Keep function names short (< 30 characters).
- **Type safety:** Use enums/inductives instead of booleans for function parameters.
- **Readability:** Let the reader of the code breathe. Add empty lines between logical blocks of code.
- **Intentional comments:** Add small, to-the-point comments explaining *what* the block does and *why*. Use examples when possible. Propose ASCII drawings to explain complex systems.
- **Encapsulation:** Treat member visibility changes as a breaking design shift. Keep all fields and functions private unless external access is strictly required by the design. Prompt the user for explicit approval before changing any access modifier from private to internal or public.
- **Levels of abstraction:** Lower-level mechanics (e.g., raw hardware I/O, sector parsing, direct socket streams) must be encapsulated in a dedicated driver/abstraction layer. Expose clean, high-level APIs to the rest of the application so calling code works with domain concepts, not raw implementation details.
- **Layered boundaries:** Strictly adhere to the layered boundary hierarchy: each layer may only communicate with its immediate neighbor directly below it. Never "punch holes" through layers (e.g., controllers or UI components must never directly call database queries, raw hardware drivers, or low-level network clients; always route through the intermediate service/abstraction layer).
- **Minimal diffs:** Don't touch blocks of code unrelated to the feature you implement. Minimize changed lines.
- **Explicit blocks:** Always use explicit block delimiters (e.g. `{}` in C/C++/Scala), even on a one-line `if` statement.

### Bug Fixing Workflow
- If fixing a bug, do NOT write the fix right away. First write the test. Observe it failing. Then write the fix, and observe the test passing.

### Commit Messages
When writing a commit message, follow these 7 rules:
- **Rule 1:** Separate the subject line from the body with a single blank line.
- **Rule 2:** Limit the subject line to 50 characters (72 is the absolute hard limit).
- **Rule 3:** Capitalize the first letter of the subject line.
- **Rule 4:** Do not end the subject line with a period.
- **Rule 5:** Use the imperative mood in the subject line (e.g., "Fix bug," "Add feature," not "Fixed" or "Adds"). Test formula: It must complete the sentence: "If applied, this commit will [your subject line here]".
- **Rule 6:** Wrap the body text manually at 72 characters to prevent Git formatting issues.
- **Rule 7:** Use the body to explain what and why vs. how. Assume the code explains the how; the message must explain the context and reasoning.

## Code Style and Quality

### Lean

- Follow [Lean 4 style guide](https://github.com/leanprover/lean4/blob/master/doc/style.md)
- No `sorry` in production code (treat as a bug)
- Use `native_decide` for concrete proofs, `simp` + tactics for generic proofs
- Keep circuits and proofs in separate files (`Foo.lean` + `FooProofs.lean`)

### Scala/Chisel

All generated Scala code must be formatted before committing:
```bash
cd chisel && sbt scalafmt
```
Config: `.scalafmt.conf` (Scala 2.13 dialect, 100 column max)

### Shell scripts

All shell scripts must pass shellcheck:
```bash
shellcheck verification/run-lec.sh
```

### SystemVerilog

IEEE 1800-2017 compliant, synthesizable subset only.

## Debugging RTL

### Cosimulation (primary debugging tool)

Lock-step comparison of RTL vs Spike reference model. Shows exact instruction where RTL diverges:

```bash
make -C testbench cosim && ./build-sim/cosim_shoumei +elf=testbench/tests/failing_test.elf
```

Output format: `DBG ret#N cyC: PC=0x... insn=0x... rd=xR(wr) data=0x... | Spike: ...`
- `MISMATCH` lines pinpoint the first divergence
- Check `data` field for wrong register values (e.g., load returning 0 instead of expected value)

### FST Waveform Traces

```bash
make -C testbench sim-trace                                    # Build with FST trace support
./build-sim/sim_shoumei_trace +trace +elf=testbench/tests/test.elf  # Run with FST
./scripts/fst_inspect shoumei_cpu.fst --list                   # List all signals
./scripts/fst_inspect shoumei_cpu.fst --cycles 60-100 --signals "rvvi_valid,rvvi_pc_rdata"
```

Key signals for memory path debugging:
- `load_fwd_valid` / `load_no_fwd` — which path a load takes (SB fwd vs DMEM)
- `lsu_sb_fwd_hit` — store buffer forwarding hit
- `lsu_valid` / `lsu_fifo_enq_ready` — FIFO enqueue handshake
- `pipeline_flush_comb` — pipeline flush events

### Debugging workflow

1. Run cosim to find the diverging instruction and wrong data value
2. Use FST trace to inspect the signal path that produced the wrong value
3. Check timing of store-buffer commits vs load dispatches for memory ordering issues

## Important Notes

- **NEVER edit files in `output/`, `testbench/generated/`, or `chisel/src/main/scala/generated/`.** These are generated by `lake exe generate_all` and will be overwritten on every regeneration. All changes must go in the Lean source files under `lean/`. If the generated output is wrong, fix the code generator (`lean/Shoumei/Codegen/`), not the generated file.
- **origin/main has no pre-existing test failures.** GitHub branch protection requires CI to pass before merging. If tests fail on your branch, you introduced the regression -- do not assume failures are pre-existing.
- Always read existing Lean files before modifying
- LEC failures indicate bugs in code generators, not the DSL
- Clock and reset are implicit in Chisel (Clock/AsyncReset types) -- the codegen handles filtering them from explicit inputs
- `hasSequentialElements` checks DFF gates only, NOT instances -- use `findClockWires`/`findResetWires` which check both
- The `generate_all` executable is the recommended codegen entry point (does SV + Chisel + C++ Sim)
- Chisel `Main.scala` auto-discovers all modules in `generated/` directory

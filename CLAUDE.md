# Claude Development Context

Instructions and procedures for working on the Shoumei RTL project.

## Project Summary

Formally verified hardware design: circuits defined in Lean 4 DSL, properties proven with dependent types, dual code generators produce SystemVerilog + Chisel, Yosys LEC verifies equivalence.

**Current state:** 89 modules, 100% LEC coverage, complete RV32IM Tomasulo CPU. See [RISCV_TOMASULO_PLAN.md](RISCV_TOMASULO_PLAN.md) for roadmap.

## Key Toolchain Versions

- **Lean 4:** v4.27.0 (controlled by `lean-toolchain`)
- **Chisel:** 7.7.0 (in `chisel/build.sbt`)
- **Scala:** 2.13.18 (required for Chisel 7.x)
- **Yosys:** system package (for LEC)
- **CIRCT/firtool:** 1.140.0 (for arcilator simulation backend; install via `scripts/install-circt.sh`)
- **RISC-V GCC:** `riscv32-unknown-elf-gcc` at `~/.local/riscv32-elf/bin/` (add to PATH for test compilation)

## Build Commands

```bash
lake build                          # Build Lean proofs + code generators
lake exe generate_all               # Generate SV + Chisel + C++ Sim for all modules
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

- **origin/main has no pre-existing test failures.** GitHub branch protection requires CI to pass before merging. If tests fail on your branch, you introduced the regression -- do not assume failures are pre-existing.
- Always read existing Lean files before modifying
- LEC failures indicate bugs in code generators, not the DSL
- Clock and reset are implicit in Chisel (Clock/AsyncReset types) -- the codegen handles filtering them from explicit inputs
- `hasSequentialElements` checks DFF gates only, NOT instances -- use `findClockWires`/`findResetWires` which check both
- The `generate_all` executable is the recommended codegen entry point (does SV + Chisel + C++ Sim)
- Chisel `Main.scala` auto-discovers all modules in `generated/` directory

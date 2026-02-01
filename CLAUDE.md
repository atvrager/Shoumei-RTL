# Claude Development Context

This file contains development context, architecture decisions, and implementation notes for Claude Code when working on the Shoumei RTL project.

## Project Vision

Build a formally verified hardware design flow where:
- Hardware circuits are defined in a LEAN4-embedded DSL
- Properties are proven about circuits using theorem proving
- Code generators produce both SystemVerilog and Chisel from the same proven source
- Chisel is compiled to SystemVerilog via the standard toolchain (FIRRTL → CIRCT → SystemVerilog)
- Logical Equivalence Checking (LEC) verifies both SystemVerilog outputs are identical

This provides **mathematical proof** that our DSL semantics are correctly implemented in both code generators.

## Architecture Decisions

### Why LEAN4?

- Modern theorem prover with dependent types
- Lake build system integrated (as of 2026)
- FFI support for integration with external tools
- Strong metaprogramming capabilities for DSL embedding
- Growing ecosystem and active development (see [LEAN FRO Year 3 Roadmap](https://lean-lang.org/fro/roadmap/y3/))

### Why Dual Generation (SystemVerilog + Chisel)?

1. **SystemVerilog from LEAN**: Direct path, proves our semantics are correct
2. **Chisel from LEAN**: Leverages mature Chisel/FIRRTL/CIRCT toolchain, more optimized output
3. **LEC between them**: Validates both generators produce equivalent circuits

### Build System Strategy

**Three-tier approach:**

1. **LEAN4/Lake** - Primary build system for theorem proving and code generation
   - **elan** - LEAN toolchain manager (like rustup for Rust)
     - Manages LEAN installations (`~/.elan/bin/`)
     - Controlled by `lean-toolchain` file (currently: v4.15.0)
     - No sudo/system packages required
     - Installation: `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh`
   - Lake is now merged into Lean 4 itself
   - FFI capabilities for Scala/JVM integration if needed
   - Configuration in `lakefile.lean`

2. **Scala/sbt** - Chisel compilation to SystemVerilog
   - Standard Chisel workflow: Chisel → FIRRTL → firtool → SystemVerilog
   - Chisel 6.0+ auto-manages firtool binary
   - Configuration in `build.sbt`

3. **Top-level orchestration** - TBD (Make, Just, or custom Lake targets)
   - Coordinates LEAN4 → Chisel generation → sbt build → LEC
   - Could potentially use Lake's FFI to invoke sbt directly

### Equivalence Checking Tool Choice

**Initial: ABC (open-source)**
- Supports both combinational (CEC) and sequential (SEC) equivalence
- Free and scriptable
- Good for development and CI

**Future: Commercial tools**
- Synopsys Formality (industry standard for LEC)
- Cadence Conformal AI (AI-enhanced LEC)
- Siemens Questa SLEC (sequential equivalence)

## Implementation Phases

### Phase 1: Foundation ✅ COMPLETE
- [x] Project structure setup
- [x] Basic LEAN4 DSL for combinational circuits (gates, wires, circuits)
- [x] Operational semantics in LEAN
- [x] Basic theorem proving infrastructure
- [x] Dual code generators (SystemVerilog + Chisel)
- [x] Building blocks library:
  - FullAdder, RippleCarryAdder (4/8/32-bit)
  - Subtractor (4/8/32-bit)
  - Comparator (4/8/32-bit)
  - LogicUnit (4/8/32-bit)
  - Shifter (4/32-bit)
  - ALU32 (10 operations)
- [x] Sequential circuits: DFlipFlop, Queue (1-element FIFO)

### Phase 2: RISC-V Decoder Integration ✅ COMPLETE
- [x] Lake build configuration with code generation targets
- [x] sbt configuration for Chisel compilation
- [x] Yosys/ABC integration scripts for LEC
- [x] End-to-end workflow automation
- [x] RV32I instruction decoder:
  - 40 RISC-V base integer instructions
  - Automated parsing from riscv-opcodes
  - Mask/match pattern decoding
  - Immediate value extraction (I/S/B/U/J formats)
- [x] LEC verification: All 20 modules proven equivalent
  - LEAN SV ≡ Chisel SV (via Yosys SAT solver)
- [ ] CI pipeline (GitHub Actions)

### Phase 3: DSL Expansion (Next)
- [ ] More sequential circuits (counters, state machines)
- [ ] Parameterized circuits with dependent types
- [ ] Module hierarchy and composition
- [ ] Correctness theorems (timing, safety properties)
- [ ] RISC-V CPU datapath integration

### Phase 4: Advanced Features (Future)
- [ ] Optimization passes with correctness proofs
- [ ] Clock domain crossing primitives
- [ ] Memory models (SRAM, BRAM)
- [ ] Pipeline verification
- [ ] Industrial-scale examples

## Technical Challenges

### Challenge 1: LEAN4 → Chisel Code Generation

Chisel is Scala-based. Options:
- Generate Chisel Scala source files (easiest, what we should do initially)
- Use LEAN4 FFI to invoke Scala/JVM directly (more complex)
- Generate FIRRTL directly, bypass Chisel (loses Chisel's optimizations)

**Decision**: Generate Chisel Scala source, compile with sbt. Clean separation of concerns.

### Challenge 2: Semantic Equivalence

We need to prove that:
```
⟦ DSL Circuit ⟧ ≡ SystemVerilog Semantics ≡ Chisel Semantics
```

This requires:
- Formal semantics for our DSL in LEAN
- Verified code generators with correctness proofs
- LEC only checks the generated outputs match (not the full proof chain)

LEC is a sanity check; the real proof is in LEAN.

### Challenge 3: FFI and Build System Integration

LEAN4 FFI examples (from research):
- [LEAN4 FFI Programming Tutorial with GLFW](https://github.com/DSLstandard/Lean4-FFI-Programming-Tutorial-GLFW)
- [lean4-alloy: Write C shims from within Lean](https://github.com/tydeu/lean4-alloy)

For Scala/JVM integration:
- Could use Lean FFI → C → JNI → Scala (complex)
- Or just generate .scala files and shell out to sbt (simple, recommended)

**Decision**: Keep it simple - generate source files, use shell commands.

## Code Organization

### LEAN4 Module Structure

```
Shoumei/
├── DSL.lean              -- Core DSL types (Wire, Gate, Circuit, etc.)
├── Semantics.lean        -- Operational semantics (evaluation functions)
├── Theorems.lean         -- General theorems about DSL
├── Codegen/
│   ├── Common.lean       -- Shared codegen utilities
│   ├── SystemVerilog.lean -- SV generator with correctness proof
│   └── Chisel.lean       -- Chisel generator with correctness proof
├── Circuits/
│   ├── Combinational.lean -- Combinational circuit library
│   └── Sequential.lean    -- Sequential circuit library (future)
└── Examples/
    ├── Adder.lean
    ├── Mux.lean
    └── ALU.lean          -- (future)
```

### Chisel Runtime Support

The `chisel/` directory contains:
- Generated Chisel code from LEAN (in `chisel/src/main/scala/generated/`)
- Runtime support code if needed (wrapper classes, utilities)
- sbt build configuration

## Testing Strategy

1. **LEAN Proofs** - Theorems about circuit behavior
2. **Unit Tests** - Test individual code generation functions
3. **Integration Tests** - Full DSL → SV + Chisel → LEC pipeline
4. **Property Tests** - Randomized circuit generation + LEC

## Resources

### LEAN4
- [Lean 4 Language](https://lean-lang.org/)
- [Lake README](https://github.com/leanprover/lean4/blob/master/src/lake/README.md)
- [LEAN4 FFI Documentation](https://github.com/leanprover/lean4/blob/master/doc/dev/ffi.md)
- [LEAN FRO Year 3 Roadmap](https://lean-lang.org/fro/roadmap/y3/)

### Chisel/FIRRTL
- [Chisel GitHub](https://github.com/chipsalliance/chisel)
- [Chisel Documentation](https://www.chisel-lang.org/)
- [CIRCT Project](https://circt.llvm.org/)

### Formal Verification
- [Formal Verification Overview](https://verificationacademy.com/topics/formal-verification/)
- [Equivalence Checking (Synopsys)](https://www.synopsys.com/glossary/what-is-equivalence-checking.html)
- [Cadence Logic Equivalence Checking](https://www.cadence.com/en_US/home/tools/digital-design-and-signoff/logic-equivalence-checking.html)
- [ABC: System for Sequential Synthesis and Verification](https://github.com/ElNiak/awesome-formal-verification)

### Related Projects
- [sv2chisel: SystemVerilog to Chisel translator](https://github.com/ovh/sv2chisel) (interesting for comparison)

## Development Guidelines

### When Adding New DSL Constructs

1. Define syntax in `DSL.lean`
2. Define semantics in `Semantics.lean`
3. Prove key properties in `Theorems.lean`
4. Implement code generators in `Codegen/SystemVerilog.lean` and `Codegen/Chisel.lean`
5. Prove code generator correctness (output matches semantics)
6. Add examples and tests

### When Extending Build System

- Keep Lake as the primary entry point
- Use Lake's extern_lib and FFI features sparingly
- Document any sbt invocations clearly
- Ensure all generated artifacts are in `output/` directory

### Style Conventions

- LEAN: Follow [Lean 4 style guide](https://github.com/leanprover/lean4/blob/master/doc/style.md)
- Scala/Chisel: Follow Scala style guide with scalafmt enforcement
- SystemVerilog: IEEE 1800-2017 compliant, synthesizable subset only

### Scala Code Formatting with scalafmt

**IMPORTANT**: All Scala code must be formatted with scalafmt before committing.

**Pre-commit checklist for Scala code:**
```bash
# Format all Scala files
cd chisel && sbt scalafmt

# Check formatting without making changes
cd chisel && sbt scalafmtCheck
```

**Configuration:** `.scalafmt.conf` in chisel/ directory
- Version: 3.8.3
- Style: defaultWithAlign
- Max column: 100
- Scala dialect: 2.13

**CI enforcement:** GitHub Actions automatically checks that all Scala code is properly formatted.

**Install scalafmt locally (optional):**
```bash
# Using coursier
cs install scalafmt

# Or use sbt (automatic via plugin)
cd chisel && sbt scalafmt
```

### Shell Script Quality

**IMPORTANT**: All shell scripts must pass shellcheck before committing.

**Pre-commit checklist for shell scripts:**
```bash
# Run shellcheck on all shell scripts
find . -name "*.sh" -type f -exec shellcheck {} +

# Or check a specific script
shellcheck verification/run-lec.sh
```

**Common shellcheck rules to follow:**
- **SC2064**: Use single quotes in traps: `trap 'rm -rf "$TMPDIR"' EXIT` (not `trap "rm -rf $TMPDIR" EXIT`)
- **SC2034**: Remove unused variables or export them if used externally
- **SC2086**: Quote variables to prevent word splitting: `"$variable"` (not `$variable`)
- **SC2046**: Quote command substitutions: `"$(command)"` (not `$(command)`)

**Install shellcheck:**
```bash
# Ubuntu/Debian
sudo apt-get install shellcheck

# Arch Linux
sudo pacman -S shellcheck

# macOS
brew install shellcheck
```

CI will automatically run shellcheck on all `.sh` files and fail if issues are found.

## Notes for Claude

- Always read existing LEAN files before modifying
- Maintain proof integrity - don't skip proofs with `sorry`
- Code generation should be as simple as possible while remaining correct
- When in doubt about LEAN syntax, check the official docs
- LEC failures indicate bugs in code generators, not the DSL
- This is research-level work - novel integration, expect challenges

## Future Directions

- Integration with formal verification tools like SymbiYosys
- Support for property specifications (SVA-like)
- Proof automation using tactics
- Integration with physical design tools
- Proof-carrying code generation
- Verified optimization passes

## Changelog

- 2026-01-31: Initial project setup, research phase complete

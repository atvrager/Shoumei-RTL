# 証明 Shoumei RTL

[![CI](https://github.com/atvrager/Shoumei-RTL/actions/workflows/ci.yml/badge.svg)](https://github.com/atvrager/Shoumei-RTL/actions/workflows/ci.yml) [![Full Verification](https://github.com/atvrager/Shoumei-RTL/actions/workflows/verify.yml/badge.svg)](https://github.com/atvrager/Shoumei-RTL/actions/workflows/verify.yml) [![Smoke Tests](https://github.com/atvrager/Shoumei-RTL/actions/workflows/smoke-test.yml/badge.svg)](https://github.com/atvrager/Shoumei-RTL/actions/workflows/smoke-test.yml) [![LEC](https://github.com/atvrager/Shoumei-RTL/actions/workflows/lec.yml/badge.svg)](https://github.com/atvrager/Shoumei-RTL/actions/workflows/lec.yml)

**Formally Verified Hardware Design with LEAN4**

A theorem-proving based hardware design framework that generates provably correct circuits in SystemVerilog and Chisel, with automated logical equivalence checking.

> 証明 (しょうめい, *shōmei*) — Japanese for "proof"

## 📋 Overview

This project bridges formal verification and hardware design by:

1. 🔷 **DSL Definition in LEAN4** — Define hardware circuits in a custom DSL embedded in LEAN4
2. ✓ **Theorem Proving** — Prove properties about circuits using LEAN4's dependent type system
3. ⚡ **Dual Code Generation** — Generate both SystemVerilog and Chisel from the proven DSL
4. 🔧 **Chisel Compilation** — Compile Chisel to SystemVerilog via FIRRTL/CIRCT
5. ⚖️  **Equivalence Checking** — Verify that both SystemVerilog outputs are logically equivalent

## 🏗️ Architecture

```
┌─────────────────────────────────────────────────┐
│           LEAN4 Hardware DSL                    │
│        (Theorems + Proofs)                      │
└─────────────────┬───────────────────────────────┘
                  │
         ┌────────┴─────────┐
         │                  │
         ▼                  ▼
┌─────────────────┐  ┌─────────────────┐
│  SystemVerilog  │  │     Chisel      │
│   Generator     │  │   Generator     │
└────────┬────────┘  └────────┬────────┘
         │                    │
         │                    ▼
         │           ┌─────────────────┐
         │           │ FIRRTL + CIRCT  │
         │           │   (firtool)     │
         │           └────────┬────────┘
         │                    │
         ▼                    ▼
┌─────────────────┐  ┌─────────────────┐
│ SystemVerilog   │  │ SystemVerilog   │
│  (from LEAN)    │  │ (from Chisel)   │
└────────┬────────┘  └────────┬────────┘
         │                    │
         └────────┬───────────┘
                  ▼
         ┌─────────────────┐
         │   Equivalence   │
         │    Checking     │
         │  (ABC/Formal)   │
         └─────────────────┘
```

## Technology Stack

### Core Languages
- **LEAN4** - Theorem proving and DSL host language
- **Scala 3** - For Chisel (hardware construction language)
- **SystemVerilog** - Target HDL for synthesis

### Build Systems
- **Lake** - LEAN4 build system and package manager (merged into Lean 4)
- **sbt** - Scala Build Tool for Chisel components
- **Make/Just** - Top-level orchestration (TBD)

### Toolchain Components
- **FIRRTL** - Flexible Intermediate Representation for RTL
- **CIRCT** - Circuit IR Compilers and Tools (LLVM-based, includes firtool)
- **ABC** - Open-source logic synthesis and verification (for equivalence checking)

### Alternative LEC Tools (Commercial)
- Synopsys Formality
- Cadence Conformal
- Siemens Questa SLEC

## Project Structure

```
proven-rtl/
├── lean/                   # LEAN4 source code
│   ├── ProvenRTL/         # Main DSL and theorem library
│   │   ├── DSL.lean       # Hardware DSL definitions
│   │   ├── Semantics.lean # Operational semantics
│   │   ├── Theorems.lean  # Proven properties
│   │   └── Codegen/       # Code generation
│   │       ├── SystemVerilog.lean
│   │       └── Chisel.lean
│   └── lakefile.lean      # Lake build configuration
├── chisel/                # Chisel code (generated + runtime)
│   ├── src/main/scala/    # Chisel source
│   └── build.sbt          # sbt configuration
├── output/                # Generated artifacts
│   ├── sv-from-lean/      # SystemVerilog from LEAN
│   └── sv-from-chisel/    # SystemVerilog from Chisel
├── verification/          # Equivalence checking scripts
└── examples/              # Example circuits
```

## Build Workflow

1. **Define Circuit in LEAN DSL**
   ```bash
   lake build
   ```

2. **Generate SystemVerilog + Chisel**
   ```bash
   lake exe codegen examples/adder.lean
   ```

3. **Compile Chisel to SystemVerilog**
   ```bash
   cd chisel && sbt "run --target-dir ../output/sv-from-chisel"
   ```

4. **Run Equivalence Check**
   ```bash
   ./verification/run-lec.sh output/sv-from-lean output/sv-from-chisel
   ```

## Current Status

**Project Phase:** Initial Setup

See [CLAUDE.md](CLAUDE.md) for development context and implementation notes.

## Dependencies

### LEAN4
- Lean 4 (latest stable)
- Lake (bundled with Lean 4)

### Chisel/Scala
- Scala 3.x
- sbt 1.9+
- Chisel 6.x
- firtool (automatically managed by Chisel 6.0+)

### Verification
- ABC (open-source)
- Or commercial tools (Synopsys Formality, Cadence Conformal)

## 🚀 Installation

**No system packages or sudo required!** Everything installs to your home directory.

```bash
# Clone the repository
git clone https://github.com/yourusername/Shoumei-RTL.git
cd Shoumei-RTL

# Run automated setup (installs elan, lake, coursier, sbt to ~/.local and ~/.elan)
make setup
# or directly: python3 bootstrap.py

# Restart shell or source your rc file
source ~/.bashrc  # or ~/.zshrc

# Build the project
make all
```

The bootstrap script installs:
- **elan** (LEAN toolchain manager) → `~/.elan/bin`
- **lake** (LEAN build system) → via elan
- **coursier** (Scala toolchain manager) → `~/.local/bin`
- **sbt** (Scala build tool) → `~/.local/share/coursier/bin`
- **scala** and **scalac** → via coursier

Optional (for equivalence checking):
```bash
# Install ABC - see: https://github.com/berkeley-abc/abc
# On macOS: brew install berkeley-abc
# On Ubuntu: sudo apt-get install abc (or build from source)
```

## References

- [LEAN4 Documentation](https://lean-lang.org/)
- [Chisel Documentation](https://www.chisel-lang.org/)
- [FIRRTL/CIRCT](https://circt.llvm.org/)
- [ABC: A System for Sequential Synthesis and Verification](https://people.eecs.berkeley.edu/~alanmi/abc/)

## License

TBD

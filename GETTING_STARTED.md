# Getting Started with Shoumei RTL

This guide will help you set up and start using the Shoumei RTL framework.

## What We've Built

A **complete build infrastructure scaffold** for formally verified hardware design:

✅ **LEAN 4 Project** - DSL, semantics, theorems, and code generators (stubbed)
✅ **Chisel 7.x Project** - Scala build configuration with modern Chisel
✅ **Bootstrap Script** - Automatic installation of elan, LEAN, and dependencies
✅ **Build Orchestration** - Makefile for end-to-end pipeline
✅ **Verification Infrastructure** - LEC script (stubbed, waiting for ABC)
✅ **Example Circuit** - Full adder defined in DSL

## Quick Start

### 1. Bootstrap the Environment

```bash
make setup
```

Or directly:
```bash
python3 bootstrap.py
```

This will (all without requiring sudo/system packages):
- Verify Python 3.11+
- Install `uv` (Python package manager) to `~/.local/bin`
- Install `elan` (LEAN toolchain manager) to `~/.elan/bin`
- Install LEAN 4.15.0 via elan
- Install `coursier` (Scala toolchain manager) to `~/.local/bin`
- Install `sbt` and Scala toolchain to `~/.local/share/coursier/bin`

### 2. Build the LEAN Code

```bash
make lean
# or directly: lake build
```

Expected output: Build succeeds with warnings about `sorry` (stubbed proofs).

**Note:** The Makefile now checks for required tools and provides helpful error messages if they're missing.

### 3. View the Project Structure

```
provable-rtl/
├── bootstrap.py              # Environment setup script
├── lean-toolchain            # LEAN version (v4.15.0)
├── lakefile.lean             # Lake build configuration
├── Makefile                  # Top-level build orchestration
│
├── lean/Shoumei/           # LEAN source code
│   ├── DSL.lean              # Hardware DSL (Wire, Gate, Circuit)
│   ├── Semantics.lean        # Operational semantics (stubbed)
│   ├── Theorems.lean         # Proven properties (stubbed)
│   ├── Codegen/
│   │   ├── Common.lean       # Shared utilities
│   │   ├── SystemVerilog.lean # SV generator (stubbed)
│   │   └── Chisel.lean       # Chisel generator (stubbed)
│   └── Examples/
│       └── Adder.lean        # Full adder circuit
│
├── chisel/                   # Chisel/Scala project
│   ├── build.sbt             # sbt configuration (Chisel 7.0.0)
│   ├── project/
│   │   └── build.properties  # sbt version (1.10.5)
│   └── src/main/scala/
│       ├── Main.scala        # Entry point for compilation
│       └── generated/        # Generated Chisel code goes here
│
├── output/                   # Generated artifacts
│   ├── sv-from-lean/         # SystemVerilog from LEAN
│   └── sv-from-chisel/       # SystemVerilog from Chisel
│
├── verification/
│   └── run-lec.sh            # Equivalence checking script
│
└── examples/
    └── adder/
        └── README.md         # Full adder documentation
```

## Build Targets

```bash
# Build LEAN code
make lean

# Generate code (TODO: not yet implemented)
make codegen

# Compile Chisel to SystemVerilog
make chisel

# Run logical equivalence checking
make lec

# Run entire pipeline
make all

# Clean all generated files
make clean

# Show help
make help
```

## Current Status: Scaffolded and Ready

### ✅ What Works

1. **LEAN build system** - All modules compile successfully
2. **Bootstrap script** - Automates environment setup
3. **Project structure** - Complete directory layout
4. **Build orchestration** - Makefile coordinates all steps
5. **Verification scaffold** - LEC script ready (waiting for ABC)

### 🚧 What's Stubbed (Ready to Implement)

1. **DSL Semantics** (`Semantics.lean`)
   - `evalGate` - Evaluate individual gates
   - `evalCircuit` - Evaluate complete circuits
   - Currently use `sorry` placeholders

2. **Code Generators** (`Codegen/SystemVerilog.lean`, `Codegen/Chisel.lean`)
   - Generate from circuit structure (currently hardcoded templates)
   - Need to traverse gates and produce actual code

3. **Theorems** (`Theorems.lean`)
   - Commutativity, associativity proofs
   - Code generator correctness proofs
   - Currently use `sorry` placeholders

4. **Code Generation Executable**
   - Need to add Lake executable target
   - Wire up code generators to file I/O
   - Generate actual .sv and .scala files

5. **Logical Equivalence Checking**
   - Install ABC: `yay -S abc-git` (Arch) or build from source
   - Implement actual miter and SAT checking

## Next Steps (Bottom-Up Development)

### Step 1: Implement Gate Evaluation (15-30 min)

File: `lean/Shoumei/Semantics.lean`

Replace `sorry` in `evalGate`:
```lean
def evalGate (g : Gate) (env : Env) : Bool :=
  match g.gateType with
  | GateType.AND =>
      (env g.inputs[0]!) && (env g.inputs[1]!)
  | GateType.OR =>
      (env g.inputs[0]!) || (env g.inputs[1]!)
  | GateType.NOT =>
      !(env g.inputs[0]!)
  | GateType.XOR =>
      (env g.inputs[0]!) != (env g.inputs[1]!)
```

### Step 2: Implement Circuit Evaluation (30-60 min)

File: `lean/Shoumei/Semantics.lean`

Implement topological evaluation in `evalCircuit`.

### Step 3: Implement SystemVerilog Generator (1-2 hours)

File: `lean/Shoumei/Codegen/SystemVerilog.lean`

Generate actual Verilog from circuit structure instead of hardcoded template.

### Step 4: Implement Chisel Generator (1-2 hours)

File: `lean/Shoumei/Codegen/Chisel.lean`

Generate actual Chisel from circuit structure.

### Step 5: Add Code Generation Executable (30 min)

File: `lakefile.lean`

Add:
```lean
lean_exe codegen where
  root := `Shoumei.Examples.Adder
  supportInterpreter := true
```

Then create IO functions to write generated code to files.

### Step 6: Install sbt and Test Chisel (30 min)

```bash
# Arch Linux
sudo pacman -S sbt

# Then test
cd chisel && sbt compile
cd chisel && sbt run
```

### Step 7: Install ABC and Test LEC (30 min)

```bash
# Arch Linux
yay -S abc-git

# Then test
./verification/run-lec.sh output/sv-from-lean output/sv-from-chisel
```

### Step 8: Prove Theorems (Ongoing)

File: `lean/Shoumei/Theorems.lean`

Replace `sorry` with actual proofs.

## Example: Full Adder

The full adder circuit is defined in `lean/Shoumei/Examples/Adder.lean`:

```lean
def fullAdderCircuit : Circuit :=
  { name := "FullAdder"
    inputs := [a, b, cin]
    outputs := [sum, cout]
    gates := [
      Gate.mkXOR a b ab_xor,
      Gate.mkXOR ab_xor cin sum,
      Gate.mkAND a b ab_and,
      Gate.mkAND cin ab_xor cin_ab,
      Gate.mkOR ab_and cin_ab cout
    ]
  }
```

See `examples/adder/README.md` for full documentation.

## Dependencies

### Required

- **Python 3.11+** - For bootstrap script
- **elan** - LEAN toolchain manager (installed by bootstrap.py)
- **LEAN 4.15.0** - Installed via elan

### Optional (for full pipeline)

- **sbt 1.10+** - For Chisel compilation
- **Scala 3.3.4** - Installed automatically by sbt
- **ABC** - For logical equivalence checking
- **Chisel 7.0.0** - Installed automatically by sbt

## Troubleshooting

### "lake: command not found"

```bash
# Add elan to PATH
export PATH="$HOME/.elan/bin:$PATH"

# Or restart your shell after running bootstrap.py
```

### "sbt: command not found"

Install sbt manually:
- Arch: `sudo pacman -S sbt`
- Ubuntu: https://www.scala-sbt.org/download.html

### Build warnings about 'sorry'

Expected! These are stubbed proofs. Replace with actual implementations.

### "unused variable" warnings

Expected! These are in stubbed code generators that will use variables later.

## Resources

- [LEAN 4 Documentation](https://lean-lang.org/)
- [Chisel Documentation](https://www.chisel-lang.org/)
- [Lake Build System](https://github.com/leanprover/lean4/blob/master/src/lake/README.md)
- [ABC Verification Tool](https://github.com/berkeley-abc/abc)

## Contributing

The scaffold is complete and ready for development. Pick any stubbed component and start implementing!

Priority areas:
1. Semantics (enables testing)
2. Code generators (enables verification)
3. Theorems (proves correctness)

## License

See LICENSE file.

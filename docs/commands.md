# Command Reference Guide

Quick reference for working with Shoumei RTL. This guide assumes you're in the project root directory.

## Table of Contents

- [Quick Start](#quick-start)
- [Lake (LEAN Build System)](#lake-lean-build-system)
- [Make Targets](#make-targets)
- [Git Workflows](#git-workflows)
- [Verification](#verification)
- [Troubleshooting](#troubleshooting)

---

## Quick Start

```bash
# Initial setup (run once)
make setup         # Runs bootstrap.py to install elan, lake, and the build dependencies

# Build everything
make all           # Automatically checks for required tools

# Or step by step:
make lean          # Build LEAN code
make codegen       # Run code generators + export the compositional certificate registry
make systemverilog # Yosys read/hierarchy check of the generated SystemVerilog
make cppsim        # Compile the C++ simulation

# If make setup fails, you can run bootstrap directly:
python3 bootstrap.py
```

---

## Lake (LEAN Build System)

Lake is LEAN's built-in build system (like Make or Cargo). It's configured in `lakefile.lean`.

### Basic Commands

```bash
# Build the project
lake build

# Build and show detailed output
lake build -v

# Clean build artifacts
lake clean

# Update dependencies
lake update

# Run executable (once we add one)
lake exe <executable-name>

# Enter LEAN REPL
lake env lean --run
```

### Working with LEAN Files

```bash
# Check a single LEAN file for errors
lake env lean lean/Shoumei/DSL.lean

# View installed LEAN version
lean --version

# Update LEAN toolchain (uses lean-toolchain file)
elan update

# Show LEAN toolchain info
elan show

# Switch LEAN versions
elan default leanprover/lean4:v4.27.0
```

### Common Lake Workflows

```bash
# After modifying LEAN files
lake build

# If build gets stuck or acts weird
lake clean
lake build

# Check what Lake would build
lake build --dry-run

# Build with maximum verbosity (debugging)
lake build -v -Kv
```

### LEAN REPL (Interactive Mode)

```bash
# Start REPL with project environment
lake env lean --run

# In the REPL:
#import Shoumei.DSL
open Shoumei
#check Wire
#eval fullAdderCircuit.name
```

---

## Make Targets

The Makefile orchestrates the entire build pipeline and includes automatic tool checking.

```bash
# Show all available targets with descriptions
make help

# First-time setup (installs elan/lake and the Python dependencies)
make setup

# Build LEAN code (checks for lake first)
make lean

# Run code generators + export the compositional certificate registry
make codegen

# Elaborate the generated SystemVerilog with Yosys
make systemverilog

# Compile the C++ simulation
make cppsim

# Open-source ASIC synthesis
make synth-gf180   # Synthesize to GF180MCU at 64 MHz (15.625 ns)
make synth-asap7   # Synthesize to ASAP7 7nm at 1.0 GHz (1.000 ns)

# Run the CI smoke tests
make smoke-test

# Regenerate the architecture treemap (docs/architecture-treemap.svg)
make architecture-diagram

# Run entire pipeline (checks all tools first)
make all

# Clean all generated files (works even without tools installed)
make clean

# Clean and rebuild everything
make clean all
```

### Make Target Details

| Target | What it does |
|--------|--------------|
| `make setup` | Runs `bootstrap.py` to install dependencies |
| `make lean` | Runs `lake build`, checks for lake first |
| `make codegen` | Runs `lake exe generate_all`, then exports the certificate registry |
| `make systemverilog` | Runs `verification/validate-sv.sh` on `output/sv-from-lean/` |
| `make cppsim` | Compiles the generated C++ simulation with CMake |
| `make synth-gf180` | Synthesizes RV64 core to GF180MCU via Yosys + ABC |
| `make synth-asap7` | Synthesizes RV64 core to ASAP7 7nm via Yosys + ABC |
| `make architecture-diagram` | Runs `lake exe generate_all --treemap`; `make codegen` also emits it |
| `make smoke-test` | `make codegen` followed by `verification/smoke-test.sh` |
| `make all` | Runs `check-tools lean codegen systemverilog cppsim` |
| `make clean` | Removes generated files (graceful if tools missing) |

### Error Handling

The Makefile checks for required tools and provides helpful error messages:

```bash
# If lake is not installed:
$ make lean
Error: lake not found. Run 'make setup' to install dependencies.
```

---

## Git Workflows

### Basic Commits

```bash
# Check status
git status

# Add files
git add .

# Commit
git commit -m "Your message"

# View recent commits
git log --oneline -10
```

### Branching

```bash
# Create and switch to new branch
git checkout -b feature/my-feature

# Switch branches
git checkout main

# List branches
git branch -a

# Delete branch
git branch -d feature/old-feature
```

### Useful Git Commands for This Project

```bash
# See what's been generated (ignored files)
git status --ignored

# Check what would be committed
git diff --staged

# View file at specific commit
git show commit-hash:path/to/file

# Undo uncommitted changes
git checkout -- path/to/file

# View commit history with graph
git log --oneline --graph --all
```

---

## Verification

There is no longer a cross-check between two RTL designs: correctness comes from the
Lean proofs, and the emitted SystemVerilog is checked by elaborating and running it.

```bash
# Lean proofs + coverage report
lake build
./verification/proof-coverage.sh

# Validate and print the compositional certificate registry
lake exe generate_all --export-certs

# Elaborate the emitted SystemVerilog
python3 verification/slang-lint.py output/sv-from-lean
make systemverilog

# Run it
make -C testbench sim && make -C testbench run-all-tests
make -C testbench cosim && make -C testbench run-cosim
```

---

## Troubleshooting

### LEAN Issues

```bash
# Problem: "lake: command not found"
# Solution: Install elan and LEAN
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile

# Problem: Build fails with strange errors
# Solution: Clean and rebuild
lake clean
rm -rf .lake build
lake build

# Problem: Wrong LEAN version
# Solution: Use elan to reset
elan default leanprover/lean4:v4.27.0
elan toolchain list

# Problem: Import errors
# Solution: Check lake-manifest.json is up to date
lake update
lake build
```

### Build System Issues

```bash
# Problem: make can't find lake
# Solution: Ensure it's in PATH
which lake
echo $PATH

# Problem: Permission denied on scripts
# Solution: Make scripts executable
chmod +x verification/smoke-test.sh
chmod +x bootstrap.py

# Problem: Clean doesn't work
# Solution: Manual cleanup
rm -rf .lake build lake-packages output
```

### General Debugging

```bash
# Check all tool versions
lean --version
lake --version
python3 --version
yosys -V
verilator --version

# Check environment
env | grep -E 'LEAN|PATH'

# Verify project structure
tree -L 2 -a

# Check file permissions
ls -la verification/smoke-test.sh
ls -la bootstrap.py
```

---

## Useful Combinations

### After Modifying LEAN DSL

```bash
lake build              # Rebuild LEAN code
make codegen            # Regenerate SystemVerilog, netlist, ASAP7, C++ Sim, testbenches
make systemverilog      # Yosys read/hierarchy check on the regenerated SV
```

### Fresh Start (Nuclear Option)

```bash
# Clean absolutely everything
make clean
lake clean
rm -rf .lake build lake-packages

# Rebuild from scratch
make all
```

### Quick Development Loop

```bash
# 1. Edit LEAN files in lean/Shoumei/
# 2. Test immediately
lake build

# 3. If the build passes, generate code
make codegen

# 4. Check the emitted SV
make systemverilog
```

---

## Advanced: Lake Build Customization

### Adding a New Executable

Edit `lakefile.lean`:

```lean
@[default_target]
lean_exe codegen where
  root := `Main
  srcDir := "lean"
```

Then run:
```bash
lake build codegen
lake exe codegen
```

### Adding Dependencies

```bash
# Add a LEAN package dependency
lake +add <package-name>

# Update all dependencies
lake update
```

---

## Learning Resources

### LEAN4
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)
- [Lake Build System](https://github.com/leanprover/lean4/blob/master/src/lake/README.md)

---

## Cheat Sheet

```bash
# Most common commands you'll use:

# Build LEAN
lake build

# Generate code + export the certificate registry
make codegen

# Elaborate the generated SystemVerilog
python3 verification/slang-lint.py output/sv-from-lean

# Simulate
make -C testbench sim && make -C testbench run-all-tests

# Run full pipeline
make all

# Clean everything
make clean

# Check status
git status
lake build -v
```

---

**Pro Tips:**

1. **Keep lake building in a terminal** - Quick feedback on LEAN changes
2. **Use `make help`** - When you forget what targets exist
3. **Check tool versions first** - When troubleshooting weird errors
4. **Read the error messages** - Lean, slang, Yosys and Verilator all give helpful diagnostics
5. **Start simple** - Get one module working before adding complexity

---

Last updated: 2026-01-31

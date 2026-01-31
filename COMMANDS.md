# Command Reference Guide

Quick reference for working with Shoumei RTL. This guide assumes you're in the project root directory.

## Table of Contents

- [Quick Start](#quick-start)
- [Lake (LEAN Build System)](#lake-lean-build-system)
- [sbt (Scala Build Tool)](#sbt-scala-build-tool)
- [Make Targets](#make-targets)
- [Git Workflows](#git-workflows)
- [Verification](#verification)
- [Troubleshooting](#troubleshooting)

---

## Quick Start

```bash
# Initial setup (run once)
make setup         # Runs bootstrap.py to install elan, lake, and check for sbt

# Build everything
make all           # Automatically checks for required tools

# Or step by step:
make lean          # Build LEAN code
make codegen       # Run code generators (TODO: not yet implemented)
make chisel        # Compile Chisel to SystemVerilog
make lec           # Run logical equivalence checking

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
elan default leanprover/lean4:v4.15.0
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

## sbt (Scala Build Tool)

sbt builds the Chisel/Scala code. It's configured in `chisel/build.sbt`.

### Basic Commands

```bash
# Always run sbt from the chisel/ directory
cd chisel

# Enter interactive sbt shell (recommended)
sbt

# One-off commands (starts JVM each time, slower)
sbt compile
sbt run
sbt test
```

### Interactive sbt Shell

```bash
# Start the shell
cd chisel
sbt

# Inside the shell:
compile          # Compile Scala/Chisel code
run              # Run Main.scala (generates SystemVerilog)
test             # Run all tests
clean            # Remove compiled artifacts
reload           # Reload build.sbt after changes
exit             # Exit the shell
```

### Common sbt Workflows

```bash
# Generate SystemVerilog from Chisel
cd chisel
sbt run

# Run in continuous mode (rebuilds on file changes)
sbt
~compile         # Prefix with ~ for continuous mode
~test

# Clean and rebuild from scratch
sbt clean compile

# Run with verbose output
sbt -v run

# Check dependencies
sbt dependencyTree

# Update dependencies
sbt update
```

### Chisel-Specific Commands

```bash
# Generate SystemVerilog (what sbt run does)
sbt "runMain Main"

# Generate FIRRTL (intermediate representation)
sbt "runMain circt.stage.ChiselStage --target firrtl ..."

# Run with firtool directly (advanced)
sbt "runMain circt.stage.ChiselStage --target systemverilog ..."
```

### Troubleshooting sbt

```bash
# If sbt won't start or acts weird
rm -rf chisel/target chisel/project/target
sbt clean
sbt update

# Check Java version (needs Java 11+)
java -version

# Use specific Java version with sbt
JAVA_HOME=/path/to/java11 sbt run

# Increase sbt memory (if needed)
sbt -J-Xmx4G run
```

---

## Make Targets

The Makefile orchestrates the entire build pipeline and includes automatic tool checking.

```bash
# Show all available targets with descriptions
make help

# First-time setup (installs elan/lake, checks for sbt)
make setup

# Build LEAN code (checks for lake first)
make lean

# Run code generators (generates SV and Chisel from LEAN)
make codegen       # TODO: Not yet implemented

# Compile Chisel to SystemVerilog (checks for sbt first)
make chisel

# Run logical equivalence checking
make lec

# Run entire pipeline (checks all tools first)
make all

# Clean all generated files (works even without tools installed)
make clean

# Clean and rebuild everything
make clean all
```

### Make Target Details

| Target | What it does | Tool Check | Time |
|--------|--------------|------------|------|
| `make setup` | Runs `bootstrap.py` to install dependencies | Python only | ~5-10min |
| `make lean` | Runs `lake build`, checks for lake first | Required | ~10s |
| `make codegen` | Generates SystemVerilog and Chisel from LEAN DSL | Required | TODO |
| `make chisel` | Runs `sbt run` to compile Chisel → SystemVerilog | Required | ~30s |
| `make lec` | Runs LEC script to compare both SystemVerilog outputs | None | ~5s |
| `make all` | Runs entire pipeline with tool checks | All | ~50s |
| `make clean` | Removes generated files (graceful if tools missing) | None | ~1s |

### Error Handling

The Makefile now checks for required tools and provides helpful error messages:

```bash
# If lake is not installed:
$ make lean
Error: lake not found. Run 'make setup' to install dependencies.

# If sbt is not installed:
$ make chisel
Error: sbt not found. Cannot build Chisel code.
Install sbt: https://www.scala-sbt.org/download.html
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

### Logical Equivalence Checking

```bash
# Run LEC on generated SystemVerilog
./verification/run-lec.sh output/sv-from-lean output/sv-from-chisel

# Install ABC (Berkeley Logic Synthesis Tool)
# On macOS:
brew install berkeley-abc

# On Ubuntu/Debian:
sudo apt-get install abc

# On Arch:
yay -S berkeley-abc
```

### ABC Commands (Once Implemented)

```bash
# Start ABC
abc

# In ABC shell:
read_verilog output/sv-from-lean/FullAdder.sv
read_verilog output/sv-from-chisel/FullAdder.sv
miter -c -C 10000        # Create miter circuit
sat -C 10000             # Check satisfiability
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
elan default leanprover/lean4:v4.15.0
elan toolchain list

# Problem: Import errors
# Solution: Check lake-manifest.json is up to date
lake update
lake build
```

### sbt/Chisel Issues

```bash
# Problem: "sbt: command not found"
# Solution: Install sbt
# macOS:
brew install sbt
# Ubuntu/Debian:
echo "deb https://repo.scala-sbt.org/scalasbt/debian all main" | sudo tee /etc/apt/sources.list.d/sbt.list
curl -sL "https://keyserver.ubuntu.com/pks/lookup?op=get&search=0x99E82A75642AC823" | sudo apt-key add
sudo apt-get update
sudo apt-get install sbt

# Problem: Out of memory errors
# Solution: Increase heap size
export SBT_OPTS="-Xmx4G -Xss2M"
sbt run

# Problem: Compilation errors in generated Chisel
# Solution: Check that code generator produces valid Scala
cd chisel/src/main/scala/generated
ls -la
cat YourGeneratedModule.scala

# Problem: firtool not found
# Solution: Chisel 7.0+ should auto-download, but if not:
# macOS:
brew install llvm
# Ubuntu:
# Download from https://github.com/llvm/circt/releases
```

### Build System Issues

```bash
# Problem: make can't find lake or sbt
# Solution: Ensure they're in PATH
which lake
which sbt
echo $PATH

# Problem: Permission denied on scripts
# Solution: Make scripts executable
chmod +x verification/run-lec.sh
chmod +x bootstrap.py

# Problem: Clean doesn't work
# Solution: Manual cleanup
rm -rf .lake build lake-packages chisel/target chisel/project/target output/**/*.{sv,v,fir}
```

### General Debugging

```bash
# Check all tool versions
lean --version
lake --version
scala --version
sbt --version
java -version
python3 --version

# Check environment
env | grep -E 'LEAN|SCALA|JAVA|SBT'

# Verify project structure
tree -L 2 -a

# Check file permissions
ls -la verification/run-lec.sh
ls -la bootstrap.py
```

---

## Useful Combinations

### After Modifying LEAN DSL

```bash
lake build              # Rebuild LEAN code
make codegen           # Regenerate SystemVerilog and Chisel (TODO)
make chisel            # Compile new Chisel
make lec               # Verify equivalence
```

### After Modifying Chisel Build Config

```bash
cd chisel
sbt reload             # Reload build.sbt
sbt clean compile      # Clean rebuild
sbt run                # Generate SystemVerilog
```

### Fresh Start (Nuclear Option)

```bash
# Clean absolutely everything
make clean
lake clean
rm -rf .lake build lake-packages chisel/target chisel/project/target
cd chisel && sbt clean && cd ..

# Rebuild from scratch
make all
```

### Quick Development Loop

```bash
# 1. Edit LEAN files in lean/Shoumei/
# 2. Test immediately
lake build

# 3. If tests pass, generate code
make codegen

# 4. Verify output
make lec
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

### Scala/sbt
- [sbt Tutorial](https://www.scala-sbt.org/1.x/docs/sbt-by-example.html)
- [sbt Command Reference](https://www.scala-sbt.org/1.x/docs/Command-Line-Reference.html)

### Chisel
- [Chisel Bootcamp](https://github.com/freechipsproject/chisel-bootcamp)
- [Chisel Documentation](https://www.chisel-lang.org/docs)
- [Chisel API Docs](https://www.chisel-lang.org/api/latest/)

---

## Cheat Sheet

```bash
# Most common commands you'll use:

# Build LEAN
lake build

# Run code generators (once implemented)
lake exe codegen

# Compile Chisel (from project root)
make chisel

# Or from chisel directory
cd chisel && sbt run

# Run full pipeline
make all

# Clean everything
make clean

# Check status
git status
lake build -v
sbt compile
```

---

**Pro Tips:**

1. **Use sbt interactive shell** - Much faster than one-off commands
2. **Keep lake building in a terminal** - Quick feedback on LEAN changes
3. **Use `make help`** - When you forget what targets exist
4. **Check tool versions first** - When troubleshooting weird errors
5. **Read the error messages** - LEAN and Scala both give helpful diagnostics
6. **Start simple** - Get one module working before adding complexity

---

Last updated: 2026-01-31

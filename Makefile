# Proven RTL - Build System Makefile
# Orchestrates LEAN, Chisel, and verification pipeline

.PHONY: all clean lean codegen chisel lec eqy smoke-test verify help setup check-tools

# Add tool directories to PATH
# This ensures lake (from elan) and sbt (from coursier) are available
export PATH := $(HOME)/.elan/bin:$(HOME)/.local/share/coursier/bin:$(PATH)

# Tool availability checks
HAS_LAKE := $(shell command -v lake 2> /dev/null)
HAS_SBT := $(shell command -v sbt 2> /dev/null)
HAS_PYTHON := $(shell command -v python3 2> /dev/null)

# Default target: run entire pipeline
all: check-tools lean codegen chisel lec
	@echo ""
	@echo "✓ Complete pipeline executed successfully"

# Help target
help:
	@echo "証明 Shoumei RTL - Build Targets:"
	@echo ""
	@echo "Build Targets:"
	@echo "  make setup      - Run bootstrap.py to install all dependencies"
	@echo "  make all        - Run entire pipeline (lean → chisel → lec)"
	@echo "  make lean       - Build LEAN code with Lake"
	@echo "  make codegen    - Run code generators"
	@echo "  make chisel     - Compile Chisel to SystemVerilog"
	@echo ""
	@echo "Verification Targets:"
	@echo "  make lec        - Run Yosys SAT-based LEC (miter + SAT solver)"
	@echo "  make eqy        - Run EQY partitioned equivalence checking"
	@echo "  make verify     - Run all verification methods (lec + eqy)"
	@echo "  make smoke-test - Run comprehensive CI smoke tests"
	@echo ""
	@echo "Utility Targets:"
	@echo "  make clean      - Remove all generated files"
	@echo "  make help       - Show this help message"
	@echo ""
	@echo "First time setup:"
	@echo "  1. make setup   (installs elan, lake, checks for sbt)"
	@echo "  2. make all     (builds everything)"

# Initial setup - run bootstrap script
setup:
ifndef HAS_PYTHON
	@echo "Error: python3 not found. Please install Python 3.11 or higher."
	@exit 1
endif
	@echo "==> Running bootstrap script to install dependencies..."
	python3 bootstrap.py
	@echo ""
	@echo "✓ Setup complete. Run 'make all' to build the project."

# Check that required tools are available
check-tools:
ifndef HAS_LAKE
	@echo "Error: lake not found. Please run 'make setup' first to install dependencies."
	@echo "Or manually install elan: curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
	@exit 1
endif
ifndef HAS_SBT
	@echo "Warning: sbt not found. Chisel builds will fail."
	@echo "Install sbt: https://www.scala-sbt.org/download.html"
	@echo "Or on macOS: brew install sbt"
	@echo "Or on Ubuntu: see COMMANDS.md for detailed instructions"
endif

# Build LEAN code
lean:
ifndef HAS_LAKE
	@echo "Error: lake not found. Run 'make setup' to install dependencies."
	@exit 1
endif
	@echo "==> Building LEAN code with Lake..."
	lake build

# Run code generators
codegen: lean
	@echo "==> Running code generators..."
	lake exe codegen

# Compile Chisel to SystemVerilog
chisel:
ifndef HAS_SBT
	@echo "Error: sbt not found. Cannot build Chisel code."
	@echo "Install sbt: https://www.scala-sbt.org/download.html"
	@exit 1
endif
	@echo "==> Compiling Chisel to SystemVerilog..."
	cd chisel && sbt run

# Run logical equivalence checking with Yosys
lec:
	@echo "==> Running logical equivalence checking (Yosys)..."
	./verification/run-lec.sh output/sv-from-lean output/sv-from-chisel

# Run equivalence checking with EQY (partitioned approach)
eqy:
	@echo "==> Preparing cleaned Chisel output for EQY..."
	@sed '/^\/\/ ----- 8< -----/,$d' output/sv-from-chisel/FullAdder.sv > verification/FullAdder_chisel_clean.sv
	@echo "==> Running EQY equivalence checking..."
	@cd verification && rm -rf FullAdder && eqy FullAdder.eqy

# Run comprehensive smoke tests for CI
smoke-test: codegen chisel
	@echo "==> Running smoke tests..."
	./verification/smoke-test.sh

# Run all verification methods (Yosys LEC + EQY)
verify: lec eqy
	@echo ""
	@echo "✓ All verification methods passed"

# Clean all generated files
clean:
	@echo "==> Cleaning generated files..."
ifdef HAS_LAKE
	-lake clean 2>/dev/null || true
	-rm -rf .lake 2>/dev/null || true
endif
ifdef HAS_SBT
	-cd chisel && sbt clean 2>/dev/null || true
endif
	@# Always clean output directories (doesn't require tools)
	@find output/sv-from-lean -type f ! -name '.gitkeep' -delete 2>/dev/null || true
	@find output/sv-from-chisel -type f ! -name '.gitkeep' -delete 2>/dev/null || true
	@find chisel/src/main/scala/generated -type f ! -name '.gitkeep' -delete 2>/dev/null || true
	@echo "✓ Clean complete"

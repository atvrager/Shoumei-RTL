# Shoumei RTL - Build System Makefile
# Orchestrates LEAN, Chisel, and verification pipeline

.PHONY: all clean lean codegen chisel systemc lec eqy smoke-test verify help setup check-tools opcodes

# Add tool directories to PATH
# This ensures lake (from elan) and sbt (from coursier) are available
export PATH := $(HOME)/.elan/bin:$(HOME)/.local/share/coursier/bin:$(PATH)

# Tool availability checks
HAS_LAKE := $(shell command -v lake 2> /dev/null)
HAS_SBT := $(shell command -v sbt 2> /dev/null)
HAS_PYTHON := $(shell command -v python3 2> /dev/null)

# Default target: run entire pipeline
all: check-tools lean codegen chisel systemc lec
	@echo ""
	@echo "✓ Complete pipeline executed successfully (SV + Chisel + SystemC + LEC)"

# Help target
help:
	@echo "証明 Shoumei RTL - Build Targets:"
	@echo ""
	@echo "Build Targets:"
	@echo "  make setup      - Run bootstrap.py to install all dependencies"
	@echo "  make all        - Run entire pipeline (lean → chisel → systemc → lec)"
	@echo "  make lean       - Build LEAN code with Lake"
	@echo "  make opcodes    - Generate RISC-V instruction definitions (RV32I)"
	@echo "  make codegen    - Run code generators (SV + Chisel + SystemC)"
	@echo "  make chisel     - Compile Chisel to SystemVerilog"
	@echo "  make systemc    - Compile SystemC modules"
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

# Generate RISC-V instruction definitions from riscv-opcodes
opcodes:
	@echo "==> Generating RISC-V instruction definitions (RV32I)..."
	@cd third_party/riscv-opcodes && \
		PYTHONPATH=src python3 -m riscv_opcodes -c 'rv_i' 'rv32_i' && \
		echo "    Generated instr_dict.json with $$(python3 -c 'import json; print(len(json.load(open("instr_dict.json"))))') instructions"

# Run code generators
codegen: lean opcodes
	@echo "==> Running code generators..."
	@echo "    Phase 0+1: Foundation and arithmetic circuits (SV + Chisel)..."
	lake exe codegen
	@echo "    Phase 1b: Decoders (SV + Chisel)..."
	lake exe generate_decoder
	@echo "    Phase 1c: MuxTrees (SV + Chisel)..."
	lake exe generate_muxtree
	@echo "    Phase 2: RV32I decoder (SV + Chisel)..."
	lake exe generate_riscv_decoder
	@echo "    Phase 3A: Multi-entry queue (QueueN) (SV + Chisel)..."
	lake exe generate_queuen
	@echo "    Phase 3B: Register Alias Table (RAT) (SV + Chisel)..."
	lake exe generate_rat
	@echo "    Phase 3: SystemC code generation..."
	lake exe codegen_systemc

# Compile Chisel to SystemVerilog
# Main.scala auto-discovers all generated modules (including RV32IDecoder)
chisel:
ifndef HAS_SBT
	@echo "Error: sbt not found. Cannot build Chisel code."
	@echo "Install sbt: https://www.scala-sbt.org/download.html"
	@exit 1
endif
	@echo "==> Compiling Chisel to SystemVerilog..."
	cd chisel && sbt run

# Compile SystemC modules
systemc:
	@echo "==> Compiling SystemC modules..."
	cd systemc && ./build.sh

# Run logical equivalence checking with Yosys
lec: lean
	@echo "==> Running logical equivalence checking (Yosys)..."
	./verification/run-lec.sh output/sv-from-lean output/sv-from-chisel

# Run equivalence checking with EQY (partitioned approach)
# Usage: make eqy [MODULE=<name>]  (defaults to FullAdder)
MODULE ?= FullAdder
eqy:
	@echo "==> Preparing cleaned Chisel output for EQY ($(MODULE))..."
	@sed '/^\/\/ ----- 8< -----/,$$d' output/sv-from-chisel/$(MODULE).sv > verification/$(MODULE)_chisel_clean.sv
	@echo "==> Running EQY equivalence checking on $(MODULE)..."
	@cd verification && rm -rf $(MODULE) && eqy $(MODULE).eqy

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
	@find output/systemc -type f ! -name '.gitkeep' -delete 2>/dev/null || true
	@find chisel/src/main/scala/generated -type f ! -name '.gitkeep' -delete 2>/dev/null || true
	@# Clean SystemC build artifacts
	@rm -rf systemc/build 2>/dev/null || true
	@# Clean riscv-opcodes generated files
	-rm -f third_party/riscv-opcodes/instr_dict.json third_party/riscv-opcodes/encoding.out.h 2>/dev/null || true
	@echo "✓ Clean complete"

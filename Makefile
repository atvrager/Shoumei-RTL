# Shoumei RTL - Build System Makefile
# Orchestrates LEAN, Chisel, and verification pipeline

.PHONY: all clean lean codegen chisel systemverilog systemc lec eqy smoke-test verify help setup check-tools opcodes opcodes-rv32i opcodes-rv32im filelists generate-optype

# Add tool directories to PATH
# This ensures lake (from elan) and sbt (from coursier) are available
export PATH := $(HOME)/.elan/bin:$(HOME)/.local/share/coursier/bin:$(PATH)

# Tool availability checks
HAS_LAKE := $(shell command -v lake 2> /dev/null)
HAS_SBT := $(shell command -v sbt 2> /dev/null)
HAS_PYTHON := $(shell command -v python3 2> /dev/null)

# Default target: run entire pipeline
all: check-tools lean codegen chisel systemverilog systemc lec
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
	@echo "  make opcodes      - Generate RISC-V instruction definitions (default: RV32I)"
	@echo "  make opcodes-rv32i  - Generate RV32I instruction definitions"
	@echo "  make opcodes-rv32im - Generate RV32IM instruction definitions (with M extension)"
	@echo "  make codegen    - Run code generators (SV + Chisel + SystemC)"
	@echo "  make chisel     - Compile Chisel to SystemVerilog"
	@echo "  make systemverilog - Validate generated SystemVerilog with Yosys"
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

# Generate OpType enum from riscv-opcodes JSON
generate-optype: opcodes
	@echo "==> Generating OpType enum from riscv-opcodes..."
	lake exe generate_optype

# Build LEAN code
lean:
ifndef HAS_LAKE
	@echo "Error: lake not found. Run 'make setup' to install dependencies."
	@exit 1
endif
	@echo "==> Building LEAN code with Lake..."
	lake build

# Generate RISC-V instruction definitions from riscv-opcodes
# Extensions controlled by RISCV_EXTS variable (default: rv_i rv32_i rv_m rv_f rv_zifencei)
RISCV_EXTS ?= rv_i rv32_i rv_m rv_f rv_zifencei
opcodes:
	@echo "==> Generating RISC-V instruction definitions ($(RISCV_EXTS))..."
	@cd third_party/riscv-opcodes && \
		PYTHONPATH=src python3 -m riscv_opcodes -c $(RISCV_EXTS) && \
		echo "    Generated instr_dict.json with $$(python3 -c 'import json; print(len(json.load(open("instr_dict.json"))))') instructions"

# Convenience targets for common configurations
opcodes-rv32i: RISCV_EXTS = rv_i rv32_i
opcodes-rv32i: opcodes

opcodes-rv32im: RISCV_EXTS = rv_i rv32_i rv_m
opcodes-rv32im: opcodes

# Run code generators
codegen: lean opcodes
	@echo "==> Running code generators..."
	@echo "    Phase 1: All circuits (SV + Chisel + SystemC)..."
	lake exe generate_all
	@echo "    Phase 2: RISC-V decoders (RV32I + RV32IM + RV32IF + RV32IMF)..."
	lake exe generate_riscv_decoder
	@echo "    Phase 3: Exporting compositional verification certificates..."
	@mkdir -p verification
	lake exe export_verification_certs > verification/compositional-certs.txt
	@echo "    Phase 4: Generating synthesis filelists..."
	@$(MAKE) --no-print-directory filelists

# Generate per-synth-target filelists (physical/<design>.f)
# Each lists the synth wrapper + ASAP7 overrides + generic SV modules
SYNTH_DESIGNS := CPU_RV32I_synth CPU_RV32IF_synth CPU_RV32IM_synth CPU_RV32IMF_synth
filelists:
	@ASAP7_SV=$$(ls output/sv-asap7/*.sv 2>/dev/null || true); \
	ASAP7_NAMES=$$(basename -a $$ASAP7_SV 2>/dev/null || true); \
	for design in $(SYNTH_DESIGNS); do \
		{ echo "physical/$$design.sv"; \
		  for f in $$ASAP7_SV; do echo "$$f"; done; \
		  for f in output/sv-from-lean/*.sv; do \
			b=$$(basename "$$f"); \
			case " $$ASAP7_NAMES " in *" $$b "*) ;; *) echo "$$f" ;; esac; \
		  done; \
		} | sort > "physical/$$design.f"; \
	done
	@echo "✓ Generated filelists: $(addsuffix .f,$(SYNTH_DESIGNS))"

# Compile Chisel to SystemVerilog
# Main.scala auto-discovers all generated modules (including RV32I/RV32IM/RV32IF/RV32IMF decoders)
chisel:
ifndef HAS_SBT
	@echo "Error: sbt not found. Cannot build Chisel code."
	@echo "Install sbt: https://www.scala-sbt.org/download.html"
	@exit 1
endif
	@echo "==> Compiling Chisel to SystemVerilog..."
	cd chisel && sbt run
	@ls output/sv-from-chisel/*.sv 2>/dev/null | xargs -n1 basename | sort > output/sv-from-chisel/filelist.f

# Validate generated SystemVerilog modules with Yosys
# Checks syntax and hierarchy of all generated SV files
systemverilog:
	@echo "==> Validating generated SystemVerilog modules..."
	@./verification/validate-sv.sh output/sv-from-lean

# Compile SystemC modules
systemc:
	@echo "==> Compiling SystemC modules..."
	cd systemc && ./build.sh

# Run logical equivalence checking with Yosys
lec: lean
	@echo "==> Exporting compositional verification certificates..."
	@mkdir -p verification
	lake exe export_verification_certs > verification/compositional-certs.txt
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

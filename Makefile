# Shoumei RTL - Build System Makefile
# Orchestrates the LEAN build, code generation and validation pipeline

.PHONY: all clean lean codegen systemverilog cppsim smoke-test help setup check-tools opcodes opcodes-rv32i opcodes-rv32im filelists generate-optype

# Add tool directories to PATH
# This ensures lake (from elan) is available
export PATH := $(HOME)/.elan/bin:$(PATH)

# Tool availability checks
HAS_LAKE := $(shell command -v lake 2> /dev/null)
HAS_PYTHON := $(shell command -v python3 2> /dev/null)

# Default target: run entire pipeline
all: check-tools lean codegen systemverilog cppsim
	@echo ""
	@echo "✓ Complete pipeline executed successfully (SV + C++ Sim)"

# Help target
help:
	@echo "証明 Shoumei RTL - Build Targets:"
	@echo ""
	@echo "Build Targets:"
	@echo "  make setup      - Run bootstrap.py to install all dependencies"
	@echo "  make all        - Run entire pipeline (lean → codegen → sv → cppsim)"
	@echo "  make lean       - Build LEAN code with Lake"
	@echo "  make opcodes      - Generate RISC-V instruction definitions (default: RV32I)"
	@echo "  make opcodes-rv32i  - Generate RV32I instruction definitions"
	@echo "  make opcodes-rv32im - Generate RV32IM instruction definitions (with M extension)"
	@echo "  make codegen    - Run code generators (SV + netlist + C++ Sim)"
	@echo "  make systemverilog - Validate generated SystemVerilog with Yosys"
	@echo "  make cppsim     - Compile C++ simulation modules"
	@echo ""
	@echo "Verification Targets:"
	@echo "  make smoke-test - Run comprehensive CI smoke tests"
	@echo ""
	@echo "Utility Targets:"
	@echo "  make clean      - Remove all generated files"
	@echo "  make help       - Show this help message"
	@echo ""
	@echo "First time setup:"
	@echo "  1. make setup   (installs elan, lake and the HDL tooling)"
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

# Generate OpType enum from riscv-opcodes JSON
generate-optype: opcodes
	@echo "==> Generating OpType enum from riscv-opcodes..."
	lake --no-ansi exe generate_optype

# Build LEAN code
lean:
ifndef HAS_LAKE
	@echo "Error: lake not found. Run 'make setup' to install dependencies."
	@exit 1
endif
	@echo "==> Building LEAN code with Lake..."
	lake --no-ansi build

# Generate RISC-V instruction definitions from riscv-opcodes
# Extensions controlled by RISCV_EXTS variable (default: rv_i rv32_i rv_m rv_f rv_zifencei)
RISCV_EXTS ?= rv_i rv64_i rv_m rv64_m rv_a rv64_a rv_f rv64_f rv_d rv64_d rv_zicsr rv_zifencei rv_system
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
	@echo "    Phase 1: All circuits (SV + netlist + C++ Sim)..."
	lake --no-ansi exe generate_all     # circuits + decoders + filelists in one pass
	@echo "    Phase 2: Exporting compositional verification certificates..."
	@mkdir -p verification
	lake --no-ansi exe generate_all --export-certs > verification/compositional-certs.txt

# Generate per-synth-target filelists (physical/<design>.f)
# generate_all dynamically generates filelists for all physical/*_synth.sv wrappers
filelists: codegen

# Validate generated SystemVerilog modules with Yosys
# Checks syntax and hierarchy of all generated SV files
systemverilog:
	@echo "==> Validating generated SystemVerilog modules..."
	@./verification/validate-sv.sh output/sv-from-lean

# Compile C++ simulation modules
cppsim:
	@echo "==> Compiling C++ simulation modules..."
	cd cpp_sim && mkdir -p build && cd build && cmake .. && make -j$$(nproc)

# Run comprehensive smoke tests for CI
smoke-test: codegen
	@echo "==> Running smoke tests..."
	./verification/smoke-test.sh

# Build debugging tools
FST_INC := -I/usr/share/verilator/include/gtkwave '-DFST_CONFIG_INCLUDE="fstapi.h"'
# Use system liblz4 if available, otherwise build from /tmp/lz4-src (clone from github.com/lz4/lz4)
FST_LZ4_SYS := $(shell pkg-config --cflags --libs liblz4 2>/dev/null)
FST_LZ4_LOCAL := $(wildcard /tmp/lz4-src/lib/lz4.c)
ifdef FST_LZ4_SYS
  FST_LZ4_CFLAGS :=
  FST_LZ4_OBJ :=
  FST_LZ4_LIBS := $(FST_LZ4_SYS)
else ifdef FST_LZ4_LOCAL
  FST_LZ4_CFLAGS := -I/tmp/lz4-src/lib
  FST_LZ4_OBJ := /tmp/lz4.o
  FST_LZ4_LIBS :=
else
  $(error "liblz4-dev not found and /tmp/lz4-src missing. Install liblz4-dev or: git clone --depth 1 https://github.com/lz4/lz4 /tmp/lz4-src")
endif

scripts/fst_inspect: scripts/fst_inspect.cpp scripts/fst_stubs.c
	@echo "==> Building fst_inspect..."
	@gcc -c -O2 $(FST_INC) $(FST_LZ4_CFLAGS) /usr/share/verilator/include/gtkwave/fstapi.c -o /tmp/fstapi.o
	@gcc -c -O2 scripts/fst_stubs.c -o /tmp/fst_stubs.o
	$(if $(FST_LZ4_OBJ),@gcc -c -O2 -I/tmp/lz4-src/lib /tmp/lz4-src/lib/lz4.c -o $(FST_LZ4_OBJ))
	@g++ -O2 $(FST_INC) $(FST_LZ4_CFLAGS) -o $@ $< /tmp/fstapi.o /tmp/fst_stubs.o $(FST_LZ4_OBJ) -lz -lpthread $(FST_LZ4_LIBS)
	@echo "✓ Built $@"

.PHONY: tools
tools: scripts/fst_inspect

# Clean all generated files
clean:
	@echo "==> Cleaning generated files..."
ifdef HAS_LAKE
	-lake clean 2>/dev/null || true
	-rm -rf .lake 2>/dev/null || true
endif
	@# Always clean output directories (doesn't require tools)
	@find output/sv-from-lean -type f ! -name '.gitkeep' -delete 2>/dev/null || true
	@find output/cpp_sim -type f ! -name '.gitkeep' -delete 2>/dev/null || true
	@# Clean codegen hash cache
	@rm -rf .codegen-cache 2>/dev/null || true
	@# Clean C++ simulation build artifacts
	@rm -rf cpp_sim/build 2>/dev/null || true
	@# Clean riscv-opcodes generated files
	-rm -f third_party/riscv-opcodes/instr_dict.json third_party/riscv-opcodes/encoding.out.h 2>/dev/null || true
	@echo "✓ Clean complete"

# Proven RTL - Build System Makefile
# Orchestrates LEAN, Chisel, and verification pipeline

.PHONY: all clean lean codegen chisel lec help

# Default target: run entire pipeline
all: lean chisel lec
	@echo ""
	@echo "✓ Complete pipeline executed successfully"

# Help target
help:
	@echo "Proven RTL Build Targets:"
	@echo "  make all      - Run entire pipeline (lean → chisel → lec)"
	@echo "  make lean     - Build LEAN code with Lake"
	@echo "  make codegen  - Run code generators (TODO: not yet implemented)"
	@echo "  make chisel   - Compile Chisel to SystemVerilog"
	@echo "  make lec      - Run logical equivalence checking"
	@echo "  make clean    - Remove all generated files"
	@echo "  make help     - Show this help message"

# Build LEAN code
lean:
	@echo "==> Building LEAN code with Lake..."
	lake build

# Run code generators
# TODO: Implement Lake executable for code generation
codegen: lean
	@echo "==> Running code generators..."
	@echo "TODO: Implement code generation executable"
	@echo "Will generate:"
	@echo "  - output/sv-from-lean/FullAdder.sv"
	@echo "  - chisel/src/main/scala/generated/FullAdder.scala"
	# lake exe codegen

# Compile Chisel to SystemVerilog
chisel:
	@echo "==> Compiling Chisel to SystemVerilog..."
	cd chisel && sbt run

# Run logical equivalence checking
lec:
	@echo "==> Running logical equivalence checking..."
	./verification/run-lec.sh output/sv-from-lean output/sv-from-chisel

# Clean all generated files
clean:
	@echo "==> Cleaning generated files..."
	lake clean
	cd chisel && sbt clean
	rm -rf output/sv-from-lean/*
	rm -rf output/sv-from-chisel/*
	rm -rf chisel/src/main/scala/generated/*.scala
	rm -rf .lake
	@echo "✓ Clean complete"

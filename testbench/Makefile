# Testbench Makefile - Verilator simulation of Shoumei CPU
#
# Targets:
#   make sim          - Build Verilator simulation binary
#   make sim-trace    - Build with VCD trace support
#   make run-elf      - Run with an ELF file: make run-elf ELF=path/to/prog.elf
#   make tests        - Build ELF test programs
#   make run-all-tests- Build sim + tests, run all
#   make clean        - Clean build artifacts

PROJ_ROOT := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))..
SV_DIR    := $(PROJ_ROOT)/output/sv-from-lean
BUILD_DIR := $(PROJ_ROOT)/build-sim
TB_DIR    := $(PROJ_ROOT)/testbench

# Verilator flags
VERILATOR  := verilator
VFLAGS     := --cc --exe --build -j 0 \
              --Mdir $(BUILD_DIR)/verilator \
              -Wno-UNOPTFLAT \
              --top-module tb_cpu \
              -CFLAGS "-std=c++17 -O2"

# Source files: all SV from Lean + the decoder + testbench wrapper
SV_SOURCES := $(wildcard $(SV_DIR)/*.sv)
TB_SOURCES := $(TB_DIR)/tb_cpu.sv
CPP_SOURCES := $(TB_DIR)/sim_main.cpp

.PHONY: sim sim-trace run-elf tests run-all-tests clean

sim: $(SV_SOURCES) $(TB_SOURCES) $(CPP_SOURCES)
	@mkdir -p $(BUILD_DIR)/verilator
	$(VERILATOR) $(VFLAGS) \
		-o $(BUILD_DIR)/sim_shoumei \
		$(TB_SOURCES) $(SV_SOURCES) $(CPP_SOURCES)
	@echo "Built: $(BUILD_DIR)/sim_shoumei"

sim-trace: $(SV_SOURCES) $(TB_SOURCES) $(CPP_SOURCES)
	@mkdir -p $(BUILD_DIR)/verilator
	$(VERILATOR) $(VFLAGS) --trace \
		-CFLAGS "-DVM_TRACE=1" \
		-o $(BUILD_DIR)/sim_shoumei_trace \
		$(TB_SOURCES) $(SV_SOURCES) $(CPP_SOURCES)
	@echo "Built: $(BUILD_DIR)/sim_shoumei_trace (with VCD trace)"

run-elf: sim
	$(BUILD_DIR)/sim_shoumei +elf=$(ELF)

tests:
	$(MAKE) -C $(TB_DIR)/tests

run-all-tests: sim tests
	@for elf in $(TB_DIR)/tests/*.elf; do \
		echo "=== Running $$(basename $$elf) ==="; \
		$(BUILD_DIR)/sim_shoumei +elf=$$elf +timeout=2000 || exit 1; \
	done
	@echo "All tests passed."

clean:
	rm -rf $(BUILD_DIR)/verilator $(BUILD_DIR)/sim_shoumei $(BUILD_DIR)/sim_shoumei_trace
	rm -f shoumei_cpu.vcd
	$(MAKE) -C $(TB_DIR)/tests clean

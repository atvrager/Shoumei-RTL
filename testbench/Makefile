# Testbench Makefile - Verilator simulation of Shoumei CPU
#
# Targets:
#   make sim          - Build Verilator simulation binary
#   make sim-trace    - Build with VCD trace support
#   make sim-debug    - Build with TRACE_PIPELINE $display output
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

.PHONY: sim sim-trace sim-debug run-elf tests run-all-tests clean

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

sim-debug: $(SV_SOURCES) $(TB_SOURCES) $(CPP_SOURCES)
	@mkdir -p $(BUILD_DIR)/verilator_dbg
	$(VERILATOR) --cc --exe --build -j 0 \
		--Mdir $(BUILD_DIR)/verilator_dbg \
		-Wno-UNOPTFLAT --top-module tb_cpu \
		-CFLAGS "-std=c++17 -O2" \
		-DTRACE_PIPELINE \
		-o $(BUILD_DIR)/sim_shoumei_dbg \
		$(TB_SOURCES) $(SV_SOURCES) $(CPP_SOURCES)
	@echo "Built: $(BUILD_DIR)/sim_shoumei_dbg (with pipeline trace)"

run-elf: sim
	$(BUILD_DIR)/sim_shoumei +elf=$(ELF)

tests:
	$(MAKE) -C $(TB_DIR)/tests

run-all-tests: sim tests
	@pass=0; fail=0; total=0; \
	for elf in $(TB_DIR)/tests/*.elf; do \
		total=$$((total+1)); \
		name=$$(basename $$elf); \
		result=$$($(BUILD_DIR)/sim_shoumei +elf=$$elf +timeout=2000 2>&1); \
		tohost=$$(echo "$$result" | grep -oP 'tohost:\s+\K0x[0-9a-fA-F]+'); \
		cycles=$$(echo "$$result" | grep -oP 'Total cycles:\s+\K[0-9]+'); \
		if [ "$$tohost" = "0x00000001" ]; then \
			echo "PASS  $$name  (cycle $$cycles)"; \
			pass=$$((pass+1)); \
		else \
			echo "FAIL  $$name  (tohost=$$tohost, cycle $$cycles)"; \
			fail=$$((fail+1)); \
		fi; \
	done; \
	echo ""; \
	echo "$$pass/$$total passed, $$fail failed"; \
	[ $$fail -eq 0 ]

clean:
	rm -rf $(BUILD_DIR)/verilator $(BUILD_DIR)/verilator_dbg $(BUILD_DIR)/sim_shoumei $(BUILD_DIR)/sim_shoumei_trace $(BUILD_DIR)/sim_shoumei_dbg
	rm -f shoumei_cpu.vcd
	$(MAKE) -C $(TB_DIR)/tests clean

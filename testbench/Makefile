# Testbench Makefile - Verilator simulation of Shoumei CPU
#
# Targets:
#   make sim          - Build Verilator simulation binary
#   make sim-trace    - Build with VCD trace support
#   make sim-debug    - Build with TRACE_PIPELINE $display output
#   make run-elf      - Run with an ELF file: make run-elf ELF=path/to/prog.elf
#   make tests        - Build ELF test programs
#   make run-all-tests- Build sim + tests, run all
#   make cosim        - Build cosimulation binary (RTL + Spike + SystemC)
#   make cosim-no-sc  - Build 2-way cosimulation (RTL + Spike only)
#   make run-cosim    - Run 3-way cosim on all ELFs
#   make run-cosim-no-sc - Run 2-way cosim on all ELFs
#   make clean        - Clean build artifacts

PROJ_ROOT := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))..
SV_DIR    := $(PROJ_ROOT)/output/sv-from-lean
BUILD_DIR := $(PROJ_ROOT)/build-sim
TB_DIR    := $(PROJ_ROOT)/testbench

# Verilator flags
VERILATOR  := verilator
VFLAGS     := --cc --exe --build -j 0 \
              --Mdir $(BUILD_DIR)/verilator \
              -Wno-UNOPTFLAT -Wno-PINMISSING \
              --top-module tb_cpu \
              -CFLAGS "-std=c++17 -O2"

# Source files: all SV from Lean + generated testbench
SV_SOURCES := $(wildcard $(SV_DIR)/*.sv)
TB_SOURCES := $(wildcard $(TB_DIR)/generated/tb_*.sv)
CPP_SOURCES := $(TB_DIR)/sim_main.cpp
COSIM_CPP   := $(TB_DIR)/cosim_main.cpp $(TB_DIR)/lib/spike_oracle.cpp

# X-propagation flags: randomize uninitialized regs to catch reset bugs
VFLAGS_XPROP := --x-assign unique --x-initial unique

# Spike paths (override with SPIKE_PREFIX=...)
SPIKE_PREFIX ?= $(HOME)/.local/spike
SPIKE_INC    := $(SPIKE_PREFIX)/include
SPIKE_LIB    := $(SPIKE_PREFIX)/lib

# Auto-build Spike if missing (check for .so or .a)
$(SPIKE_LIB)/libriscv.so $(SPIKE_LIB)/libriscv.a:
	@echo "Spike not found at $(SPIKE_PREFIX), building from source..."
	@git -C $(PROJ_ROOT) submodule update --init third_party/riscv-isa-sim
	SPIKE_PREFIX=$(SPIKE_PREFIX) $(PROJ_ROOT)/scripts/build-spike.sh

.PHONY: sim sim-xprop sim-trace sim-debug run-elf gen-tests tests run-all-tests run-all-tests-xprop cosim cosim-no-sc run-cosim run-cosim-no-sc clean

sim: $(SV_SOURCES) $(TB_SOURCES) $(CPP_SOURCES)
	@rm -rf $(BUILD_DIR)/verilator
	@mkdir -p $(BUILD_DIR)/verilator
	$(VERILATOR) $(VFLAGS) \
		-o $(BUILD_DIR)/sim_shoumei \
		$(TB_SOURCES) $(SV_SOURCES) $(CPP_SOURCES)
	@echo "Built: $(BUILD_DIR)/sim_shoumei"

sim-xprop: $(SV_SOURCES) $(TB_SOURCES) $(CPP_SOURCES)
	@rm -rf $(BUILD_DIR)/verilator_xprop
	@mkdir -p $(BUILD_DIR)/verilator_xprop
	$(VERILATOR) $(VFLAGS) $(VFLAGS_XPROP) \
		--Mdir $(BUILD_DIR)/verilator_xprop \
		-o $(BUILD_DIR)/sim_shoumei_xprop \
		$(TB_SOURCES) $(SV_SOURCES) $(CPP_SOURCES)
	@echo "Built: $(BUILD_DIR)/sim_shoumei_xprop (with X-propagation)"

sim-trace: $(SV_SOURCES) $(TB_SOURCES) $(CPP_SOURCES)
	@rm -rf $(BUILD_DIR)/verilator
	@mkdir -p $(BUILD_DIR)/verilator
	$(VERILATOR) $(VFLAGS) --trace \
		-CFLAGS "-DVM_TRACE=1" \
		-o $(BUILD_DIR)/sim_shoumei_trace \
		$(TB_SOURCES) $(SV_SOURCES) $(CPP_SOURCES)
	@echo "Built: $(BUILD_DIR)/sim_shoumei_trace (with VCD trace)"

sim-debug: $(SV_SOURCES) $(TB_SOURCES) $(CPP_SOURCES)
	@rm -rf $(BUILD_DIR)/verilator_dbg
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

gen-tests:
	@if command -v lake >/dev/null 2>&1; then \
		cd $(PROJ_ROOT) && lake exe gen_tests; \
	elif ls $(TB_DIR)/tests/generated/*.S >/dev/null 2>&1; then \
		echo "lake not found, using pre-generated .S files"; \
	else \
		echo "ERROR: no lake and no generated .S files" >&2; exit 1; \
	fi

tests: gen-tests
	$(MAKE) -C $(TB_DIR)/tests

run-all-tests: sim tests
	@pass=0; fail=0; total=0; \
	for elf in $(TB_DIR)/tests/*.elf $(TB_DIR)/tests/generated/*.elf; do \
		total=$$((total+1)); \
		name=$$(basename $$elf); \
		result=$$($(BUILD_DIR)/sim_shoumei +elf=$$elf +timeout=3000 2>&1); \
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

run-all-tests-xprop: sim-xprop tests
	@pass=0; fail=0; total=0; \
	for elf in $(TB_DIR)/tests/*.elf $(TB_DIR)/tests/generated/*.elf; do \
		total=$$((total+1)); \
		name=$$(basename $$elf); \
		result=$$($(BUILD_DIR)/sim_shoumei_xprop +elf=$$elf +timeout=3000 2>&1); \
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
	echo "$$pass/$$total passed, $$fail failed (X-prop mode)"; \
	[ $$fail -eq 0 ]

SPIKE_LIB_FILE := $(firstword $(wildcard $(SPIKE_LIB)/libriscv.*))
ifeq ($(SPIKE_LIB_FILE),)
  SPIKE_LIB_FILE := $(SPIKE_LIB)/libriscv.so
endif

cosim-no-sc: $(SV_SOURCES) $(TB_SOURCES) $(COSIM_CPP) $(SPIKE_LIB_FILE)
	@rm -rf $(BUILD_DIR)/verilator_cosim
	@mkdir -p $(BUILD_DIR)/verilator_cosim
	$(VERILATOR) --cc --exe --build -j 0 \
		--Mdir $(BUILD_DIR)/verilator_cosim \
		-Wno-UNOPTFLAT --top-module tb_cpu \
		-CFLAGS "-std=c++20 -O2 -I$(SPIKE_INC)" \
		-LDFLAGS "-L$(SPIKE_LIB) -lriscv -lsoftfloat -ldisasm -lfesvr -Wl,-rpath,$(SPIKE_LIB)" \
		-o $(BUILD_DIR)/cosim_shoumei \
		$(TB_SOURCES) $(SV_SOURCES) $(COSIM_CPP)
	@echo "Built: $(BUILD_DIR)/cosim_shoumei (2-way: RTL + Spike)"

cosim: $(SV_SOURCES) $(TB_SOURCES) $(COSIM_CPP) $(TB_DIR)/lib/systemc_oracle.cpp $(SPIKE_LIB_FILE)
	@rm -rf $(BUILD_DIR)/verilator_cosim3
	@mkdir -p $(BUILD_DIR)/verilator_cosim3
	$(VERILATOR) --cc --exe --build -j 0 \
		--Mdir $(BUILD_DIR)/verilator_cosim3 \
		-Wno-UNOPTFLAT --top-module tb_cpu \
		-CFLAGS "-std=c++20 -O2 -I$(SPIKE_INC) -DHAS_SYSTEMC" \
		-LDFLAGS "-L$(SPIKE_LIB) -lriscv -lsoftfloat -ldisasm -lfesvr -lsystemc -Wl,-rpath,$(SPIKE_LIB)" \
		-o $(BUILD_DIR)/cosim_shoumei_3way \
		$(TB_SOURCES) $(SV_SOURCES) $(COSIM_CPP) $(TB_DIR)/lib/systemc_oracle.cpp
	@echo "Built: $(BUILD_DIR)/cosim_shoumei_3way (3-way: RTL + Spike + SystemC)"

run-cosim-no-sc: cosim-no-sc tests
	@pass=0; fail=0; total=0; \
	for elf in $(TB_DIR)/tests/*.elf $(TB_DIR)/tests/generated/*.elf; do \
		total=$$((total+1)); \
		name=$$(basename $$elf); \
		if $(BUILD_DIR)/cosim_shoumei +elf=$$elf +timeout=3000 2>&1 | grep -q "COSIM PASS"; then \
			echo "PASS  $$name"; \
			pass=$$((pass+1)); \
		else \
			echo "FAIL  $$name"; \
			fail=$$((fail+1)); \
		fi; \
	done; \
	echo ""; \
	echo "$$pass/$$total passed, $$fail failed (2-way cosim)"; \
	[ $$fail -eq 0 ]

run-cosim: cosim tests
	@pass=0; fail=0; total=0; \
	for elf in $(TB_DIR)/tests/*.elf $(TB_DIR)/tests/generated/*.elf; do \
		total=$$((total+1)); \
		name=$$(basename $$elf); \
		if $(BUILD_DIR)/cosim_shoumei_3way +elf=$$elf +timeout=3000 2>&1 | grep -q "COSIM PASS"; then \
			echo "PASS  $$name"; \
			pass=$$((pass+1)); \
		else \
			echo "FAIL  $$name"; \
			fail=$$((fail+1)); \
		fi; \
	done; \
	echo ""; \
	echo "$$pass/$$total passed, $$fail failed (3-way cosim)"; \
	[ $$fail -eq 0 ]

clean:
	rm -rf $(BUILD_DIR)/verilator $(BUILD_DIR)/verilator_dbg $(BUILD_DIR)/verilator_xprop $(BUILD_DIR)/verilator_cosim $(BUILD_DIR)/verilator_cosim3 $(BUILD_DIR)/sim_shoumei $(BUILD_DIR)/sim_shoumei_trace $(BUILD_DIR)/sim_shoumei_dbg $(BUILD_DIR)/sim_shoumei_xprop $(BUILD_DIR)/cosim_shoumei $(BUILD_DIR)/cosim_shoumei_3way
	rm -f shoumei_cpu.vcd
	$(MAKE) -C $(TB_DIR)/tests clean

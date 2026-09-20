# Testbench Makefile - Verilator + Arcilator simulation of Shoumei CPU
#
# Targets (Arcilator - default):
#   make sim-arc      - Build Arcilator simulation binary
#   make cosim-arc    - Build Arcilator cosimulation binary
#
# Targets (Verilator - fallback):
#   make sim          - Build Verilator simulation binary (X-prop enabled)
#   make sim-trace    - Build with FST trace support
#   make sim-debug    - Build with TRACE_PIPELINE $display output
#   make cosim        - Build cosimulation binary (RTL + Spike + C++ Sim)
#
# Common:
#   make run-elf      - Run with an ELF file: make run-elf ELF=path/to/prog.elf
#   make tests        - Build ELF test programs
#   make riscv-tests  - Build upstream riscv-tests rv32ui + rv32um ELFs
#   make run-all-tests      - Build sim + tests + riscv-tests, run all (Verilator)
#   make run-all-tests-arc  - Build sim-arc + tests + riscv-tests, run all (Arcilator)
#   make run-cosim          - Run cosim on all ELFs (Verilator)
#   make run-cosim-arc      - Run cosim on all ELFs (Arcilator)
#   make clean        - Clean build artifacts

PROJ_ROOT := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))..
SV_DIR    := $(PROJ_ROOT)/output/sv-from-lean
BUILD_DIR := $(PROJ_ROOT)/build-sim
TB_DIR    := $(PROJ_ROOT)/testbench

# Include auto-generated config from Lean (provides CPU_NAME, SPIKE_ISA, etc.)
-include $(PROJ_ROOT)/output/config.mk

# --------------------------------------------------------------------------
# CIRCT / Arcilator paths
# --------------------------------------------------------------------------
CIRCT_PREFIX  ?= $(HOME)/.local/circt
ARCILATOR     := $(CIRCT_PREFIX)/bin/arcilator
CIRCT_VERILOG := $(CIRCT_PREFIX)/bin/circt-verilog
LLVM_OPT      := $(CIRCT_PREFIX)/bin/opt
LLVM_LLC      := $(CIRCT_PREFIX)/bin/llc

# --------------------------------------------------------------------------
# Verilator flags (X-prop always on to catch reset bugs)
# --------------------------------------------------------------------------
VERILATOR  := verilator
VWARN      := -Wno-UNOPTFLAT -Wno-PINMISSING -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-CASEOVERLAP -Wno-UNUSEDSIGNAL -Wno-UNUSEDPARAM -Wno-NULLPORT -Wno-MULTIDRIVEN -Wno-MULTIDRIVEN
VSPLIT     ?= --output-split 5000 --output-split-cfuncs 5000

# Enable ccache for Verilator compilation if available
OBJCACHE ?= $(if $(shell which ccache 2>/dev/null),ccache,)
export OBJCACHE
OPT_FAST ?= -O2
export OPT_FAST
OPT_SLOW ?= -O1
export OPT_SLOW

# Helper: disable precompiled headers then build (PCH can OOM on large designs)
define verilator_build
	@sed -i 's/VM_PCH = 1/VM_PCH = 0/' $(1)/Vtb_cpu.mk
	$(MAKE) -C $(1) -f Vtb_cpu.mk -j $(shell nproc) OBJCACHE=$(OBJCACHE) OPT_FAST="$(OPT_FAST)" OPT_SLOW="$(OPT_SLOW)"
endef

# Source files: all SV from Lean + generated testbench
SV_SOURCES := $(wildcard $(SV_DIR)/*.sv)
TB_SOURCES := $(wildcard $(TB_DIR)/generated/tb_*.sv)
SIM_CPP    := $(TB_DIR)/generated/sim_main_tb_cpu.cpp
COSIM_CPP  := $(TB_DIR)/generated/cosim_main_tb_cpu.cpp $(TB_DIR)/lib/spike_oracle.cpp \
              $(TB_DIR)/lib/elf_loader.cpp

# Spike paths (override with SPIKE_PREFIX=...)
SPIKE_PREFIX ?= $(HOME)/.local/spike
SPIKE_INC    := $(SPIKE_PREFIX)/include
SPIKE_LIB    := $(SPIKE_PREFIX)/lib

# --------------------------------------------------------------------------
# Unified ELF lists (single source of truth — add new ISA suites here)
# --------------------------------------------------------------------------
RISCV_TEST_GLOBS = $(TB_DIR)/riscv-tests/rv64ui-p-*.elf \
                   $(TB_DIR)/riscv-tests/rv64um-p-*.elf \
                   $(TB_DIR)/riscv-tests/rv64uf-p-*.elf \
                   $(TB_DIR)/riscv-tests/rv64ud-p-*.elf \
                   $(TB_DIR)/riscv-tests/rv64ua-p-*.elf \
                   $(TB_DIR)/riscv-tests/rv64uzb-p-*.elf

CUSTOM_TEST_GLOBS = $(TB_DIR)/tests/*.elf $(TB_DIR)/tests/generated/*.elf

# Auto-build Spike if missing (check for .so or .a)
$(SPIKE_LIB)/libriscv.so $(SPIKE_LIB)/libriscv.a:
	@echo "Spike not found at $(SPIKE_PREFIX), building from source..."
	@git -C $(PROJ_ROOT) submodule update --init third_party/riscv-isa-sim
	SPIKE_PREFIX=$(SPIKE_PREFIX) $(PROJ_ROOT)/scripts/build-spike.sh

.PHONY: sim sim-trace sim-debug run-elf gen-tests tests riscv-tests run-riscv-tests run-all-tests \
        cosim run-cosim coremark run-coremark clean \
        sim-arc cosim-arc run-all-tests-arc run-cosim-arc \
        sim-cov run-coverage run-kanata-traces \
        bench run-benchmarks sim-leansim bench-cppsim bench-compare

SIM_BIN      := $(BUILD_DIR)/sim_shoumei
COSIM_BIN    := $(BUILD_DIR)/cosim_shoumei
SIM_COV_BIN  := $(BUILD_DIR)/sim_shoumei_cov
LEANSIM_BIN  := $(BUILD_DIR)/sim_leansim
ARC_SIM_BIN  := $(BUILD_DIR)/sim_shoumei_arc
ARC_COSIM_BIN := $(BUILD_DIR)/cosim_shoumei_arc

# ==========================================================================
# Arcilator targets
# ==========================================================================

# Arcilator compiles only the CPU design modules (not the SV testbench).
# The C++ driver (sim_main_arc.cpp) replaces the SV testbench functionality.
ARC_TOP_MODULE := CPU_$(CPU_NAME)_L1I256B_L1D256B_L2512B

# Step 0: Preprocess design SV to convert async resets to sync resets
# circt-verilog emits LLHD (unsupported by arcilator) for async reset always_ff blocks
ARC_SV_DIR := $(BUILD_DIR)/arc/sv
ARC_SV_SOURCES := $(patsubst $(SV_DIR)/%.sv,$(ARC_SV_DIR)/%.sv,$(SV_SOURCES))

$(ARC_SV_DIR)/%.sv: $(SV_DIR)/%.sv
	@mkdir -p $(ARC_SV_DIR)
	sed 's/always_ff @(posedge \([^ ]*\) or posedge [^)]*)/always_ff @(posedge \1)/g' $< > $@

# Step 1: SV -> MLIR (via circt-verilog) — design modules only
$(BUILD_DIR)/arc/cpu.mlir: $(ARC_SV_SOURCES)
	@mkdir -p $(BUILD_DIR)/arc
	$(CIRCT_VERILOG) --ir-hw $(ARC_SV_SOURCES) -o $@

# Step 2: MLIR -> LLVM IR + state JSON (via arcilator)
$(BUILD_DIR)/arc/cpu.ll: $(BUILD_DIR)/arc/cpu.mlir
	$(ARCILATOR) $< --state-file=$(BUILD_DIR)/arc/cpu.json \
		--async-resets-as-sync -o $@

# Step 3: LLVM IR -> object file
$(BUILD_DIR)/arc/cpu.o: $(BUILD_DIR)/arc/cpu.ll
	$(LLVM_OPT) -O3 --strip-debug -S $< | $(LLVM_LLC) -O3 --filetype=obj -o $@

# Step 4: Generate C++ header from state JSON
$(BUILD_DIR)/arc/cpu_arc.h: $(BUILD_DIR)/arc/cpu.ll
	python3 $(PROJ_ROOT)/scripts/gen-arc-header.py $(BUILD_DIR)/arc/cpu.json $@ $(ARC_TOP_MODULE)

# Step 5a: Arcilator simulation binary
sim-arc: $(ARC_SIM_BIN)
$(ARC_SIM_BIN): $(BUILD_DIR)/arc/cpu.o $(BUILD_DIR)/arc/cpu_arc.h $(TB_DIR)/sim_main_arc.cpp $(TB_DIR)/lib/elf_loader.cpp
	$(CXX) -std=c++17 -O2 -no-pie \
		-I$(BUILD_DIR)/arc -I$(TB_DIR) \
		$(TB_DIR)/sim_main_arc.cpp $(TB_DIR)/lib/elf_loader.cpp \
		$(BUILD_DIR)/arc/cpu.o \
		-o $@
	@echo "Built: $@ (arcilator)"

# Step 5b: Arcilator cosim binary
SPIKE_LIB_FILE := $(firstword $(wildcard $(SPIKE_LIB)/libriscv.*))
ifeq ($(SPIKE_LIB_FILE),)
  SPIKE_LIB_FILE := $(SPIKE_LIB)/libriscv.so
endif

cosim-arc: $(ARC_COSIM_BIN)
$(ARC_COSIM_BIN): $(BUILD_DIR)/arc/cpu.o $(BUILD_DIR)/arc/cpu_arc.h $(TB_DIR)/cosim_main_arc.cpp $(TB_DIR)/lib/elf_loader.cpp $(TB_DIR)/lib/spike_oracle.cpp $(SPIKE_LIB_FILE)
	$(CXX) -std=c++20 -O2 -no-pie \
		-I$(BUILD_DIR)/arc -I$(TB_DIR) -I$(SPIKE_INC) \
		$(TB_DIR)/cosim_main_arc.cpp $(TB_DIR)/lib/elf_loader.cpp $(TB_DIR)/lib/spike_oracle.cpp \
		$(BUILD_DIR)/arc/cpu.o \
		-L$(SPIKE_LIB) -lriscv -lsoftfloat -ldisasm -lfesvr -Wl,-rpath,$(SPIKE_LIB) \
		-o $@
	@echo "Built: $@ (arcilator + Spike cosim)"

# Run all tests with arcilator
run-all-tests-arc: $(ARC_SIM_BIN) tests riscv-tests
	@mkdir -p $(PROJ_ROOT)/output
	@$(TB_DIR)/run-suite.sh --mode sim --bin $(ARC_SIM_BIN) --jobs $(shell nproc) --default-timeout 200000 \
	    --csv $(PROJ_ROOT)/output/test-results-arc.csv \
	    $(CUSTOM_TEST_GLOBS) $(RISCV_TEST_GLOBS)

# Run cosim with arcilator
run-cosim-arc: $(ARC_COSIM_BIN) tests riscv-tests
	@mkdir -p $(PROJ_ROOT)/output
	@$(TB_DIR)/run-suite.sh --mode cosim --bin $(ARC_COSIM_BIN) --jobs $(shell nproc) --default-timeout 3000 \
	    --timeout '*freertos*=200000' --timeout '*irq*=200000' \
	    --timeout '*timer*=200000' --timeout '*wfi*=200000' --timeout '*lrsc*=60000' \
	    --csv $(PROJ_ROOT)/output/cosim-results-arc.csv \
	    $(CUSTOM_TEST_GLOBS) $(RISCV_TEST_GLOBS)

# ==========================================================================
# Verilator targets
# ==========================================================================

sim: $(SIM_BIN)
$(SIM_BIN): $(SV_SOURCES) $(TB_SOURCES) $(SIM_CPP)
	@rm -rf $(BUILD_DIR)/verilator
	@mkdir -p $(BUILD_DIR)/verilator
	$(VERILATOR) --cc --exe \
		--Mdir $(BUILD_DIR)/verilator \
		$(VWARN) $(VSPLIT) --top-module tb_cpu \
		--x-assign unique --x-initial unique \
		-CFLAGS "-std=c++17" \
		-o $@ \
		$(TB_SOURCES) $(SV_SOURCES) $(SIM_CPP)
	$(call verilator_build,$(BUILD_DIR)/verilator)
	@echo "Built: $@"

sim-trace: $(SV_SOURCES) $(TB_SOURCES) $(SIM_CPP)
	@rm -rf $(BUILD_DIR)/verilator_trace
	@mkdir -p $(BUILD_DIR)/verilator_trace
	$(VERILATOR) --cc --exe \
		--Mdir $(BUILD_DIR)/verilator_trace \
		$(VWARN) $(VSPLIT) --top-module tb_cpu --trace-fst \
		--x-assign unique --x-initial unique \
		-CFLAGS "-std=c++17 -DVM_TRACE=1" \
		-o $(BUILD_DIR)/sim_shoumei_trace \
		$(TB_SOURCES) $(SV_SOURCES) $(SIM_CPP)
	$(call verilator_build,$(BUILD_DIR)/verilator_trace)
	@echo "Built: $(BUILD_DIR)/sim_shoumei_trace (with FST trace)"

sim-debug: $(SV_SOURCES) $(TB_SOURCES) $(SIM_CPP)
	@rm -rf $(BUILD_DIR)/verilator_dbg
	@mkdir -p $(BUILD_DIR)/verilator_dbg
	$(VERILATOR) --cc --exe \
		--Mdir $(BUILD_DIR)/verilator_dbg \
		$(VWARN) $(VSPLIT) --top-module tb_cpu \
		--x-assign unique --x-initial unique \
		-CFLAGS "-std=c++17" \
		-DTRACE_PIPELINE \
		-o $(BUILD_DIR)/sim_shoumei_dbg \
		$(TB_SOURCES) $(SV_SOURCES) $(SIM_CPP)
	$(call verilator_build,$(BUILD_DIR)/verilator_dbg)
	@echo "Built: $(BUILD_DIR)/sim_shoumei_dbg (with pipeline trace)"

sim-cov: $(SIM_COV_BIN)
$(SIM_COV_BIN): $(SV_SOURCES) $(TB_SOURCES) $(SIM_CPP)
	@rm -rf $(BUILD_DIR)/verilator_cov
	@mkdir -p $(BUILD_DIR)/verilator_cov
	$(VERILATOR) --cc --exe \
		--Mdir $(BUILD_DIR)/verilator_cov \
		$(VWARN) $(VSPLIT) --top-module tb_cpu \
		--coverage-line --coverage-toggle \
		--x-assign unique --x-initial unique \
		-CFLAGS "-std=c++17 -DVM_COVERAGE=1" \
		-o $@ \
		$(TB_SOURCES) $(SV_SOURCES) $(SIM_CPP)
	$(call verilator_build,$(BUILD_DIR)/verilator_cov)
	@echo "Built: $@ (with coverage)"

run-elf: $(SIM_BIN)
	$(SIM_BIN) +elf=$(ELF)

gen-tests:
	@if command -v lake >/dev/null 2>&1; then \
		cd $(PROJ_ROOT) && lake --no-ansi exe gen_tests; \
	elif ls $(TB_DIR)/tests/generated/*.S >/dev/null 2>&1; then \
		echo "lake not found, using pre-generated .S files"; \
	else \
		echo "ERROR: no lake and no generated .S files" >&2; exit 1; \
	fi

tests: gen-tests
	$(MAKE) -C $(TB_DIR)/tests

riscv-tests:
	$(MAKE) -C $(TB_DIR)/riscv-tests

run-riscv-tests: $(SIM_BIN) riscv-tests
	@mkdir -p $(PROJ_ROOT)/output
	@$(TB_DIR)/run-suite.sh --mode sim --bin $(SIM_BIN) --jobs $(shell nproc) --default-timeout 3000 \
	    --timeout '*lrsc*=60000' \
	    --csv $(PROJ_ROOT)/output/test-results.csv \
	    $(RISCV_TEST_GLOBS)

run-all-tests: $(SIM_BIN) tests riscv-tests
	@mkdir -p $(PROJ_ROOT)/output
	@$(TB_DIR)/run-suite.sh --mode sim --bin $(SIM_BIN) --jobs $(shell nproc) --default-timeout 5000 \
	    --timeout '*freertos*=200000' --timeout '*irq*=200000' \
	    --timeout '*timer*=200000' --timeout '*wfi*=200000' --timeout '*lrsc*=60000' \
	    --csv $(PROJ_ROOT)/output/test-results.csv \
	    $(CUSTOM_TEST_GLOBS) $(RISCV_TEST_GLOBS)

KANATA_DIR := $(PROJ_ROOT)/output/kanata-traces

# Re-run the ELF suite once per test with +kanata tracing enabled; the
# per-test .txt files feed the TS pipeline viewer and the Pages site.
run-kanata-traces: $(SIM_BIN) tests riscv-tests
	@mkdir -p $(KANATA_DIR)
	@$(TB_DIR)/run-suite.sh --mode sim --bin $(SIM_BIN) --jobs $(shell nproc) --default-timeout 5000 \
	    --timeout '*freertos*=200000' --timeout '*irq*=200000' \
	    --timeout '*timer*=200000' --timeout '*wfi*=200000' --timeout '*lrsc*=60000' \
	    --csv /dev/null --kanata-dir $(KANATA_DIR) \
	    $(CUSTOM_TEST_GLOBS) $(RISCV_TEST_GLOBS)

run-coverage: $(SIM_COV_BIN) tests riscv-tests
	@mkdir -p $(PROJ_ROOT)/output/coverage
	@rm -f $(PROJ_ROOT)/output/coverage/*.dat $(PROJ_ROOT)/output/coverage/*.info
	@rm -rf $(PROJ_ROOT)/output/coverage/annotated
	@$(TB_DIR)/run-suite.sh --mode sim --bin $(SIM_COV_BIN) --jobs $(shell nproc) --default-timeout 5000 \
	    --timeout '*freertos*=200000' --timeout '*irq*=200000' \
	    --timeout '*timer*=200000' --timeout '*wfi*=200000' --timeout '*lrsc*=60000' \
	    --coverage-dir $(PROJ_ROOT)/output/coverage \
	    --csv $(PROJ_ROOT)/output/test-results-coverage.csv \
	    $(CUSTOM_TEST_GLOBS) $(RISCV_TEST_GLOBS)

# ==========================================================================
# Instruction benchmark suite
#
# `bench`          generate + assemble the benchmark ELFs
# `run-benchmarks` run every bench ELF on the RTL sim (parallel), emit
#                  bench-results-rtl.csv + bench-metrics.csv
# `sim-leansim`    build the LeanSim (gate-level C++) standalone driver
# `bench-cppsim`   run the same ELFs on LeanSim
# `bench-compare`  merge RTL + LeanSim CSVs into bench-metrics.json and
#                  output/cpp_sim/bench_metrics.h
# ==========================================================================
BENCH_ELF_GLOBS := $(TB_DIR)/tests/generated/bench/*.elf

bench:
	@cd $(PROJ_ROOT) && lake --no-ansi exe gen_benchmarks
	$(MAKE) -C $(TB_DIR)/tests bench

run-benchmarks: $(SIM_BIN) bench
	@mkdir -p $(PROJ_ROOT)/output/bench
	@$(TB_DIR)/run-suite.sh --mode sim --bin $(SIM_BIN) --jobs $(shell nproc) \
	    --default-timeout 2500000 \
	    --csv $(PROJ_ROOT)/output/bench/bench-results-rtl.csv \
	    --bench-csv $(PROJ_ROOT)/output/bench/bench-metrics.csv \
	    $(BENCH_ELF_GLOBS)

# LeanSim standalone driver: generated lean_sim_{cpu}.{h,cpp} + cpu_setup_{cpu} +
# the driver main (tb_cpu), compiled with the shared ELF loader. The cached CPU
# module appends its cache hierarchy (same spelling as ARC_TOP_MODULE above).
LEANSIM_MODULE := CPU_$(CPU_NAME)_L1I256B_L1D256B_L2512B
# The gate-level model needs every emitted module implementation (the design is
# hierarchical); cpu_setup_/lean_sim_ tie them to the DUT ports + trace buses.
LEANSIM_CPPS := $(wildcard $(PROJ_ROOT)/output/cpp_sim/*.cpp)
LEANSIM_OBJ_DIR := $(BUILD_DIR)/leansim_objs
LEANSIM_OBJS := $(patsubst $(PROJ_ROOT)/output/cpp_sim/%.cpp,$(LEANSIM_OBJ_DIR)/cpp_sim_%.o,$(LEANSIM_CPPS)) \
                $(LEANSIM_OBJ_DIR)/lean_sim.o \
                $(LEANSIM_OBJ_DIR)/cpu_setup.o \
                $(LEANSIM_OBJ_DIR)/main.o \
                $(LEANSIM_OBJ_DIR)/elf_loader.o

$(LEANSIM_OBJ_DIR)/cpp_sim_%.o: $(PROJ_ROOT)/output/cpp_sim/%.cpp
	@mkdir -p $(LEANSIM_OBJ_DIR)
	$(CXX) -std=c++17 -O2 -c \
		-I$(TB_DIR)/generated -I$(TB_DIR)/lib -I$(TB_DIR) -I$(PROJ_ROOT)/output/cpp_sim \
		$< -o $@

$(LEANSIM_OBJ_DIR)/lean_sim.o: $(TB_DIR)/generated/lean_sim_$(LEANSIM_MODULE).cpp
	@mkdir -p $(LEANSIM_OBJ_DIR)
	$(CXX) -std=c++17 -O2 -c \
		-I$(TB_DIR)/generated -I$(TB_DIR)/lib -I$(TB_DIR) -I$(PROJ_ROOT)/output/cpp_sim \
		$< -o $@

$(LEANSIM_OBJ_DIR)/cpu_setup.o: $(TB_DIR)/generated/cpu_setup_$(LEANSIM_MODULE).cpp
	@mkdir -p $(LEANSIM_OBJ_DIR)
	$(CXX) -std=c++17 -O2 -c \
		-I$(TB_DIR)/generated -I$(TB_DIR)/lib -I$(TB_DIR) -I$(PROJ_ROOT)/output/cpp_sim \
		$< -o $@

$(LEANSIM_OBJ_DIR)/main.o: $(TB_DIR)/generated/lean_sim_main_tb_cpu.cpp
	@mkdir -p $(LEANSIM_OBJ_DIR)
	$(CXX) -std=c++17 -O2 -c \
		-I$(TB_DIR)/generated -I$(TB_DIR)/lib -I$(TB_DIR) -I$(PROJ_ROOT)/output/cpp_sim \
		$< -o $@

$(LEANSIM_OBJ_DIR)/elf_loader.o: $(TB_DIR)/lib/elf_loader.cpp
	@mkdir -p $(LEANSIM_OBJ_DIR)
	$(CXX) -std=c++17 -O2 -c \
		-I$(TB_DIR)/generated -I$(TB_DIR)/lib -I$(TB_DIR) -I$(PROJ_ROOT)/output/cpp_sim \
		$< -o $@

sim-leansim: $(LEANSIM_BIN)
$(LEANSIM_BIN): $(LEANSIM_OBJS)
	@mkdir -p $(BUILD_DIR)
	$(CXX) -std=c++17 -O2 -no-pie $(LEANSIM_OBJS) -o $@
	@echo "Built: $@ (LeanSim gate-level sim)"

bench-cppsim: sim-leansim bench
	@mkdir -p $(PROJ_ROOT)/output/bench
	@$(TB_DIR)/run-suite.sh --mode sim --bin $(LEANSIM_BIN) --jobs $(shell nproc) \
	    --default-timeout 2500000 \
	    --csv $(PROJ_ROOT)/output/bench/bench-results-cppsim.csv \
	    --bench-csv /dev/null \
	    $(BENCH_ELF_GLOBS)

bench-compare: run-benchmarks bench-cppsim
	python3 $(PROJ_ROOT)/scripts/bench_compare.py \
	    --rtl $(PROJ_ROOT)/output/bench/bench-results-rtl.csv \
	    --cpp $(PROJ_ROOT)/output/bench/bench-results-cppsim.csv \
	    --programs $(PROJ_ROOT)/output/bench/bench-programs.json \
	    --out $(PROJ_ROOT)/output/bench

cosim: $(COSIM_BIN)
$(COSIM_BIN): $(SV_SOURCES) $(TB_SOURCES) $(COSIM_CPP) $(SPIKE_LIB_FILE)
	@rm -rf $(BUILD_DIR)/verilator_cosim
	@mkdir -p $(BUILD_DIR)/verilator_cosim
	$(VERILATOR) --cc --exe \
		--Mdir $(BUILD_DIR)/verilator_cosim \
		$(VWARN) $(VSPLIT) +define+COSIM_DEBUG \
		--top-module tb_cpu \
		-CFLAGS "-std=c++20 -I$(SPIKE_INC) -I$(TB_DIR)/lib -I$(TB_DIR)/generated -I$(TB_DIR)" \
		-LDFLAGS "-L$(SPIKE_LIB) -lriscv -lsoftfloat -ldisasm -lfesvr -Wl,-rpath,$(SPIKE_LIB)" \
		-o $@ \
		$(TB_SOURCES) $(SV_SOURCES) $(COSIM_CPP)
	$(call verilator_build,$(BUILD_DIR)/verilator_cosim)
	@echo "Built: $@ (RTL + Spike cosim)"

run-cosim: $(COSIM_BIN) tests riscv-tests
	@mkdir -p $(PROJ_ROOT)/output
	@$(TB_DIR)/run-suite.sh --mode cosim --bin $(COSIM_BIN) --jobs $(shell nproc) --default-timeout 3000 \
	    --timeout '*freertos*=200000' --timeout '*irq*=200000' \
	    --timeout '*timer*=200000' --timeout '*wfi*=200000' --timeout '*lrsc*=60000' \
	    --csv $(PROJ_ROOT)/output/cosim-results.csv \
	    $(CUSTOM_TEST_GLOBS) $(RISCV_TEST_GLOBS)

coremark:
	$(MAKE) -C $(TB_DIR)/coremark

run-coremark: $(SIM_BIN) coremark
	$(SIM_BIN) +elf=$(TB_DIR)/coremark/coremark.elf +timeout=10000000

# --------------------------------------------------------------------------
# Cache behavior conformance (long-term software verification of cache RTL)
# Verilator-builds the emitted L1DCache SV and checks it against an
# independent reference (LRU, refill, dirty writeback, byte merge, protocol).
# --------------------------------------------------------------------------
CACHE_TEST_CPP := $(TB_DIR)/cache_model_test/cache_conformance.cpp
CACHE_BUILD    := $(TB_DIR)/build/cache_l1d
CACHE_TEST_BIN := $(TB_DIR)/build/cache_model_test

cache-model-test: $(SV_DIR)/L1DCache.sv $(SV_DIR)/Register25.sv $(SV_DIR)/Mux4x25.sv $(SV_DIR)/EqualityComparator25.sv $(SV_DIR)/Mux8x32.sv $(SV_DIR)/Mux4x32.sv $(CACHE_TEST_CPP)
	@echo "==> Building cache conformance test (Verilator SV)..."
	@mkdir -p $(TB_DIR)/build
	@rm -rf $(CACHE_BUILD)
	@verilator --cc --build -j $(shell nproc) --Mdir $(CACHE_BUILD) \
	    -Wno-fatal -O3 \
	    --top-module L1DCache --exe \
	    $(SV_DIR)/L1DCache.sv $(SV_DIR)/Register25.sv $(SV_DIR)/Mux4x25.sv \
	    $(SV_DIR)/EqualityComparator25.sv $(SV_DIR)/Mux8x32.sv $(SV_DIR)/Mux4x32.sv \
	    -CFLAGS "-std=c++17 -O2" \
	    -o $(CACHE_TEST_BIN) $(CACHE_TEST_CPP)
	@echo "==> Running cache conformance..."
	@$(CACHE_TEST_BIN) --cycles 2000

clean:
	rm -rf $(BUILD_DIR)/verilator $(BUILD_DIR)/verilator_trace $(BUILD_DIR)/verilator_dbg $(BUILD_DIR)/verilator_cov $(BUILD_DIR)/verilator_cosim $(SIM_BIN) $(SIM_COV_BIN) $(LEANSIM_BIN) $(BUILD_DIR)/sim_shoumei_trace $(BUILD_DIR)/sim_shoumei_dbg $(COSIM_BIN)
	rm -rf $(BUILD_DIR)/arc $(ARC_SIM_BIN) $(ARC_COSIM_BIN)
	rm -rf $(PROJ_ROOT)/output/coverage
	rm -f shoumei_cpu.fst
	$(MAKE) -C $(TB_DIR)/tests clean
	$(MAKE) -C $(TB_DIR)/riscv-tests clean

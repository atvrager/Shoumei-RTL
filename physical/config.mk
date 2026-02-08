PROJECT_ROOT := $(shell git rev-parse --show-toplevel)

# Physical Design Configuration
export DESIGN_NAME = CPU_RV32IM_synth
export PLATFORM    = asap7

# CPU requires all submodule SV files (using Lean-generated SV for hierarchical design)
# ASAP7 tech-mapped modules override generic versions to preserve gate topology
ASAP7_SV   := $(wildcard $(PROJECT_ROOT)/output/sv-asap7/*.sv)
ASAP7_NAMES := $(notdir $(ASAP7_SV))
GENERIC_SV := $(filter-out $(addprefix $(PROJECT_ROOT)/output/sv-from-lean/,$(ASAP7_NAMES)), \
                $(wildcard $(PROJECT_ROOT)/output/sv-from-lean/*.sv))
export VERILOG_FILES = $(PROJECT_ROOT)/physical/CPU_RV32IM_synth.sv \
                       $(ASAP7_SV) $(GENERIC_SV)
export SDC_FILE      = $(PROJECT_ROOT)/physical/constraints.sdc

# Timing Target (relaxed for complex CPU - 5ns = 200 MHz)
export CLK_PERIOD_NS = 5.0

# Floorplan Configuration
export CORE_UTILIZATION = 30
export CORE_ASPECT_RATIO = 1

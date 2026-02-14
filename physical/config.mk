PROJECT_ROOT := $(shell git rev-parse --show-toplevel)

# Physical Design Configuration
# Override DESIGN_NAME via env: DESIGN_NAME=CPU_RV32I_synth make ...
export DESIGN_NAME ?= CPU_RV32IMF_Zicsr_Zifencei_synth
export PLATFORM    = asap7

# CPU requires all submodule SV files (using Lean-generated SV for hierarchical design)
# ASAP7 tech-mapped modules override generic versions to preserve gate topology
ASAP7_SV   := $(wildcard $(PROJECT_ROOT)/output/sv-asap7/*.sv)
ASAP7_NAMES := $(notdir $(ASAP7_SV))
GENERIC_SV := $(filter-out $(addprefix $(PROJECT_ROOT)/output/sv-from-lean/,$(ASAP7_NAMES)), \
                $(wildcard $(PROJECT_ROOT)/output/sv-from-lean/*.sv))
export VERILOG_FILES = $(PROJECT_ROOT)/physical/$(DESIGN_NAME).sv \
                       $(ASAP7_SV) $(GENERIC_SV)
export SDC_FILE      = $(PROJECT_ROOT)/physical/constraints.sdc

# Frequency targets (ASAP7 time unit = picoseconds)
#   200 MHz = 5000ps (default, must pass)
#   500 MHz = 2000ps (stretch goal)
#  1000 MHz = 1000ps (aspirational)
FMAX_MHZ ?= 200
export CLK_PERIOD_PS = $(shell expr 1000000 / $(FMAX_MHZ))

# Floorplan Configuration
export CORE_UTILIZATION = 30
export CORE_ASPECT_RATIO = 1

# Repair tuning for slew violations
export REPAIR_DESIGN_MAX_WIRE_LENGTH = 800
export CTS_BUF_DISTANCE = 60

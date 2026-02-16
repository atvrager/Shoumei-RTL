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
FMAX_MHZ ?= 500
export CLK_PERIOD_PS = $(shell expr 1000000 / $(FMAX_MHZ))

# Floorplan Configuration
# Tighter packing reduces wire lengths → lower slew on high-fanout nets
# Sweet spot: 35%/0.70 minimizes slew violations at 500 MHz.
# Higher packing (45%/0.82) causes routing congestion; lower (25%/0.60) has long wires.
export CORE_UTILIZATION = 35
export CORE_ASPECT_RATIO = 1
export PLACE_DENSITY = 0.70

# Repair tuning for slew/cap violations
export REPAIR_DESIGN_MAX_WIRE_LENGTH = 300
export CTS_BUF_DISTANCE = 45
export CAP_MARGIN = 0.15
export SLEW_MARGIN = 0.15
export SETUP_SLACK_MARGIN = 75

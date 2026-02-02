PROJECT_ROOT := $(shell git rev-parse --show-toplevel)

# Physical Design Configuration
export DESIGN_NAME = RV32IMDecoder
export PLATFORM    = asap7

export VERILOG_FILES = $(PROJECT_ROOT)/output/sv-from-lean/RV32IMDecoder.sv
export SDC_FILE      = $(PROJECT_ROOT)/physical/constraints.sdc

# Timing Target
export CLK_PERIOD_NS = 1.0

# Floorplan Configuration
export CORE_UTILIZATION = 30
export CORE_ASPECT_RATIO = 1

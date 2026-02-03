PROJECT_ROOT := $(shell git rev-parse --show-toplevel)

# Physical Design Configuration
export DESIGN_NAME = CPU_RV32IM
export PLATFORM    = asap7

# CPU requires all submodule SV files (using Lean-generated SV for hierarchical design)
# Include all generated SV files to ensure all dependencies are available
export VERILOG_FILES = $(wildcard $(PROJECT_ROOT)/output/sv-from-lean/*.sv)
export SDC_FILE      = $(PROJECT_ROOT)/physical/constraints.sdc

# Timing Target (relaxed for complex CPU - 5ns = 200 MHz)
export CLK_PERIOD_NS = 5.0

# Floorplan Configuration
export CORE_UTILIZATION = 30
export CORE_ASPECT_RATIO = 1

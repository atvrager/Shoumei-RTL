PROJECT_ROOT := $(shell git rev-parse --show-toplevel)

# Physical Design Configuration
export DESIGN_NAME = CPU_RV32IM
export PLATFORM    = asap7

# CPU requires all submodule SV files (using Lean-generated SV for hierarchical design)
export VERILOG_FILES = $(PROJECT_ROOT)/output/sv-from-lean/CPU_RV32IM.sv \
                       $(PROJECT_ROOT)/output/sv-from-lean/FetchStage.sv \
                       $(PROJECT_ROOT)/output/sv-from-lean/RenameStage_32x64.sv \
                       $(PROJECT_ROOT)/output/sv-from-lean/PhysRegFile_64x32.sv \
                       $(PROJECT_ROOT)/output/sv-from-lean/RAT_32x6.sv \
                       $(PROJECT_ROOT)/output/sv-from-lean/FreeList_64.sv \
                       $(PROJECT_ROOT)/output/sv-from-lean/ReservationStation4.sv \
                       $(PROJECT_ROOT)/output/sv-from-lean/IntegerExecUnit.sv \
                       $(PROJECT_ROOT)/output/sv-from-lean/MemoryExecUnit.sv \
                       $(PROJECT_ROOT)/output/sv-from-lean/MulDivExecUnit.sv \
                       $(PROJECT_ROOT)/output/sv-from-lean/PipelinedMultiplier.sv \
                       $(PROJECT_ROOT)/output/sv-from-lean/Divider32.sv \
                       $(PROJECT_ROOT)/output/sv-from-lean/ROB16.sv \
                       $(PROJECT_ROOT)/output/sv-from-lean/LSU.sv \
                       $(PROJECT_ROOT)/output/sv-from-lean/StoreBuffer8.sv \
                       $(PROJECT_ROOT)/output/sv-from-lean/ALU32.sv
export SDC_FILE      = $(PROJECT_ROOT)/physical/constraints.sdc

# Timing Target (relaxed for complex CPU - 5ns = 200 MHz)
export CLK_PERIOD_NS = 5.0

# Floorplan Configuration
export CORE_UTILIZATION = 30
export CORE_ASPECT_RATIO = 1

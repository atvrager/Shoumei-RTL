# SDC Constraints for CPU_RV32IM
# Generated for OpenROAD physical synthesis flow
# NOTE: ASAP7 uses picoseconds as the time unit

current_design CPU_RV32IM

set clk_name  clock

# Default: 200 MHz = 5000ps. Override via CLK_PERIOD_PS env var.
if {[info exists env(CLK_PERIOD_PS)]} {
    set clk_period $env(CLK_PERIOD_PS)
} else {
    set clk_period 5000
}

# Create clock on the actual clock port
create_clock -name ${clk_name} -period ${clk_period} [get_ports clock]

# Input/Output delays (20% of clock period)
set_input_delay [expr ${clk_period} * 0.2] -clock ${clk_name} [all_inputs]
set_output_delay [expr ${clk_period} * 0.2] -clock ${clk_name} [all_outputs]

# Don't constrain clock and reset as inputs
set_input_delay 0 -clock ${clk_name} [get_ports clock]
set_input_delay 0 -clock ${clk_name} [get_ports reset]

# Set false paths for asynchronous reset
set_false_path -from [get_ports reset]

# flush_busy drives pipeline_reset_busy (async reset for pipeline DFFs).
# This is a flush/reset path, not a functional data path — false-path it
# so the resizer doesn't try to buffer the entire reset tree for timing.
set_false_path -through [get_nets {u_cpu.pipeline_reset_busy}]

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

# Pipeline flush DFFs drive async resets (RESETN) via pipeline_reset_* OR gates.
# Yosys opt_merge collapses all flush DFFs (identical d/clock/reset) into one
# cell: u_flush_dff_busy_g0. False-path from surviving flush DFF cells to
# suppress recovery/removal checks on the high-fanout reset tree.
foreach tag {rs_int rs_mem rs_br rs_muldiv rs_fp rob misc} {
    set cells [get_cells -quiet "u_cpu.u_flush_dff_${tag}.*"]
    if {[llength $cells] > 0} {
        set_false_path -from $cells
    }
}
foreach g {0 1 2 3 4 5 6 7} {
    set cells [get_cells -quiet "u_cpu.u_flush_dff_busy_g${g}.*"]
    if {[llength $cells] > 0} {
        set_false_path -from $cells
    }
}

# Max transition constraint: 350ps (ASAP7 RVT library characterization limit)
set_max_transition 350 [current_design]

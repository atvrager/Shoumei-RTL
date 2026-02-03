# SDC Constraints for CPU_RV32IM
# Generated for OpenROAD physical synthesis flow

current_design CPU_RV32IM

set clk_name  clock
set clk_period 5.0

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

current_design RV32IDecoder

set clk_name  vclk
set clk_port  vclk
set clk_period 1.0

create_clock -name ${clk_name} -period ${clk_period}

set_input_delay [expr ${clk_period} * 0.2] -clock ${clk_name} [all_inputs]
set_output_delay [expr ${clk_period} * 0.2] -clock ${clk_name} [all_outputs]

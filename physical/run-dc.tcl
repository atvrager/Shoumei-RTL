# Synopsys Design Compiler / DC NXT Synthesis Script
# Parameterized flow for Shoumei RTL physical synthesis.
#
# Environment variables:
#   DESIGN_NAME       - Top-level module name (default: CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth)
#   TARGET_LIBRARY    - Path to primary target standard cell .db library (required)
#   LINK_LIBRARIES    - Additional .db libraries (optional, space-separated)
#   CLK_PERIOD_NS     - Target clock period in nanoseconds (default: 1.333)
#   CLK_NAME          - Name of clock port (default: clock)
#   RTL_FILELIST      - Path to .f filelist (default: physical/${DESIGN_NAME}.f)
#   OUTPUT_DIR        - Directory for output artifacts (default: syn_out)
#   NUM_CORES         - Max cores for multithreading (default: 16)

if {![info exists env(TARGET_LIBRARY)]} {
    puts "ERROR: TARGET_LIBRARY environment variable must be set to a valid .db file."
    exit 1
}

set design_name "CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth"
if {[info exists env(DESIGN_NAME)]} {
    set design_name $env(DESIGN_NAME)
}

set clk_period 1.333
if {[info exists env(CLK_PERIOD_NS)]} {
    set clk_period $env(CLK_PERIOD_NS)
}

set clk_name "clock"
if {[info exists env(CLK_NAME)]} {
    set clk_name $env(CLK_NAME)
}

set out_dir "syn_out"
if {[info exists env(OUTPUT_DIR)]} {
    set out_dir $env(OUTPUT_DIR)
}

set num_cores 16
if {[info exists env(NUM_CORES)]} {
    set num_cores $env(NUM_CORES)
}

set rtl_dotf "physical/${design_name}.f"
if {[info exists env(RTL_FILELIST)]} {
    set rtl_dotf $env(RTL_FILELIST)
}

file mkdir $out_dir
file mkdir "${out_dir}/reports"
file mkdir "${out_dir}/netlist"

# Libraries
set target_library [list $env(TARGET_LIBRARY)]
set link_library [list * {*}$target_library]
if {[info exists env(LINK_LIBRARIES)]} {
    foreach lib [split $env(LINK_LIBRARIES) " "] {
        if {[string length [string trim $lib]] > 0} {
            lappend link_library $lib
        }
    }
}

puts "INFO: Target library: $target_library"
puts "INFO: Link library:   $link_library"
puts "INFO: Design name:    $design_name"
puts "INFO: Clock period:   ${clk_period} ns"

file mkdir .WORK
define_design_lib work -path .WORK

# Read RTL via directory or filelist
if {[info exists env(RTL_DIR)]} {
    set sv_files [lsort [glob -nocomplain $env(RTL_DIR)/*.sv]]
    puts "INFO: Analyzing [llength $sv_files] SystemVerilog files from $env(RTL_DIR)..."
    analyze -format sverilog -work work $sv_files
} elseif {[file exists $rtl_dotf]} {
    puts "INFO: Reading RTL via filelist: $rtl_dotf"
    analyze -format sverilog -work work -vcs "-f $rtl_dotf"
} else {
    puts "ERROR: No RTL source found (neither RTL_DIR nor $rtl_dotf exists)"
    exit 1
}
elaborate $design_name -work work
current_design $design_name
link

# Timing Constraints
create_clock -name $clk_name -period $clk_period [get_ports $clk_name]
set_clock_uncertainty -setup [expr {$clk_period * 0.02}] [get_clocks $clk_name]
set_clock_transition [expr {$clk_period * 0.02}] [get_clocks $clk_name]

set ord_inputs [remove_from_collection [all_inputs] [get_ports $clk_name]]
if {[sizeof_collection $ord_inputs] > 0} {
    set_input_delay -clock $clk_name [expr {$clk_period * 0.1}] $ord_inputs
}
if {[sizeof_collection [all_outputs]] > 0} {
    set_output_delay -clock $clk_name [expr {$clk_period * 0.1}] [all_outputs]
}

# False paths and ideal network on reset
if {[sizeof_collection [get_ports -quiet reset]] > 0} {
    set_false_path -from [get_ports reset]
    set_ideal_network [get_ports reset]
}

# Pre-CTS ideal clock network for logic synthesis
set_ideal_network [get_ports $clk_name]

# Suppress pre-CTS high-fanout delay estimation warnings on clock/reset/scan
suppress_message TIM-134

# Separate path groups for clear timing analysis
group_path -name INPUTS -from [all_inputs]
group_path -name OUTPUTS -to [all_outputs]
group_path -name COMBO -from [all_inputs] -to [all_outputs]

redirect "${out_dir}/reports/check_design.rpt" { check_design }

# Compile
set_host_options -max_cores $num_cores
compile_ultra -scan -gate_clock -no_autoungroup -no_seq_output_inversion -no_boundary_optimization

# Reports
redirect "${out_dir}/reports/qor.rpt" { report_qor }
redirect "${out_dir}/reports/area.rpt" { report_area -hierarchy -nosplit }
redirect "${out_dir}/reports/timing.rpt" { report_timing -max_paths 50 }
redirect "${out_dir}/reports/power.rpt" { report_power -nosplit }
redirect "${out_dir}/reports/clock_gate.rpt" { report_clock_gating }
redirect "${out_dir}/reports/violators.rpt" { report_constraint -all_violators }

# Netlist export
write -format verilog -hierarchy -output "${out_dir}/netlist/${design_name}.v"
write_sdc "${out_dir}/netlist/${design_name}.sdc"
write -format ddc -hierarchy -output "${out_dir}/netlist/${design_name}.ddc"

puts "INFO: Synthesis of $design_name completed successfully."
exit

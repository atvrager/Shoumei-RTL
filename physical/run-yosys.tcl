# Shoumei RTL - Unified Yosys Physical Synthesis Script
# Parameterized physical synthesis engine supporting multiple PDKs (GF180MCU, ASAP7).
#
# Environment variables:
#   PLATFORM          - Target platform: "gf180" or "asap7" (required)
#   DESIGN_NAME       - Top module (default: CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth)
#   CLK_PERIOD_NS     - Clock period in ns (default based on platform)
#   CLK_NAME          - Clock port name (default: clock)
#   TARGET_LIBRARY    - Primary combinational Liberty file for ABC and stat (required)
#   DFF_LIBRARY       - Liberty file for sequential cells (required)
#   EXTRA_LIBS        - Additional Liberty files for read_liberty (optional, space-separated)
#   ABC_DRIVER_CELL   - Driving cell for ABC constraints (optional)
#   ABC_LOAD_IN_FF    - Output load in fF for ABC constraints (optional)
#   RTL_DIR           - Directory of SystemVerilog files (default: output/sv-from-lean)
#   SYNTH_WRAPPER     - Top-level wrapper (default: physical/${DESIGN_NAME}.sv)
#   OUTPUT_DIR        - Directory for netlist and reports (default: syn_out_${PLATFORM})
#   FLATTEN           - 1 to flatten before ABC, 0 for hierarchical (default: 1)
#   IGNORE_MISS_FUNC  - 1 to pass -ignore_miss_func to read_liberty (default: 0)

yosys -import

if {![info exists env(PLATFORM)]} {
    puts "ERROR: PLATFORM environment variable must be set (e.g. gf180 or asap7)."
    exit 1
}
set platform $env(PLATFORM)

set design_name "CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth"
if {[info exists env(DESIGN_NAME)]} {
    set design_name $env(DESIGN_NAME)
}

set clk_name "clock"
if {[info exists env(CLK_NAME)]} {
    set clk_name $env(CLK_NAME)
}

set clk_period 20.0
if {[info exists env(CLK_PERIOD_NS)]} {
    set clk_period $env(CLK_PERIOD_NS)
}
set clk_period_ps [expr {round($clk_period * 1000)}]

set out_dir "syn_out_${platform}"
if {[info exists env(OUTPUT_DIR)]} {
    set out_dir $env(OUTPUT_DIR)
}

set flatten 1
if {[info exists env(FLATTEN)]} {
    set flatten $env(FLATTEN)
}

set ignore_miss_func 0
if {[info exists env(IGNORE_MISS_FUNC)]} {
    set ignore_miss_func $env(IGNORE_MISS_FUNC)
}

if {![info exists env(TARGET_LIBRARY)]} {
    puts "ERROR: TARGET_LIBRARY environment variable must be set."
    exit 1
}
set target_lib $env(TARGET_LIBRARY)

if {![info exists env(DFF_LIBRARY)]} {
    puts "ERROR: DFF_LIBRARY environment variable must be set."
    exit 1
}
set dff_lib $env(DFF_LIBRARY)

set script_dir [file dirname [file normalize [info script]]]
set project_root [file normalize "${script_dir}/.."]

# Output directories
file mkdir $out_dir
file mkdir "${out_dir}/reports"
file mkdir "${out_dir}/netlist"

puts "INFO: Platform:         $platform"
puts "INFO: Design name:      $design_name"
puts "INFO: Clock port:       $clk_name (${clk_period} ns / ${clk_period_ps} ps)"
puts "INFO: Target lib:       $target_lib"
puts "INFO: DFF lib:          $dff_lib"
puts "INFO: Output directory: $out_dir"
puts "INFO: Flatten mode:     $flatten"

# Step 1: Write ABC constraint file if driver and load are provided
set constr_file "${out_dir}/abc.constr"
set has_constr 0
if {[info exists env(ABC_DRIVER_CELL)] && [info exists env(ABC_LOAD_IN_FF)]} {
    set constr_fp [open $constr_file w]
    puts $constr_fp "set_driving_cell $env(ABC_DRIVER_CELL)"
    puts $constr_fp "set_load $env(ABC_LOAD_IN_FF)"
    close $constr_fp
    set has_constr 1
    puts "INFO: ABC constraint:   driver=$env(ABC_DRIVER_CELL), load=$env(ABC_LOAD_IN_FF) fF"
}

# Step 2: Read Liberty libraries into Yosys
set read_lib_opts [list -lib]
if {$ignore_miss_func} {
    lappend read_lib_opts -ignore_miss_func
}

read_liberty {*}$read_lib_opts $target_lib
if {$dff_lib ne $target_lib} {
    read_liberty {*}$read_lib_opts $dff_lib
}

if {[info exists env(EXTRA_LIBS)]} {
    foreach lib [split $env(EXTRA_LIBS) " "] {
        if {[string length [string trim $lib]] > 0 && [file exists $lib]} {
            puts "INFO: Reading extra lib: $lib"
            read_liberty {*}$read_lib_opts $lib
        }
    }
}

# Step 3: Read SystemVerilog sources
set rtl_dir "${project_root}/output/sv-from-lean"
if {[info exists env(RTL_DIR)]} {
    set rtl_dir $env(RTL_DIR)
}

set sv_files [lsort [glob -nocomplain "${rtl_dir}/*.sv"]]
if {[llength $sv_files] == 0} {
    puts "ERROR: No SystemVerilog files found in $rtl_dir"
    exit 1
}

puts "INFO: Reading [llength $sv_files] SystemVerilog files from $rtl_dir..."
foreach f $sv_files {
    # -nolatches: inferred latches abort the flow (DC NXT LINT-1 mimic).
    # Elaboration warnings (width, multi-driver) remain fatal via set -e in
    # the calling script's post-check (see run-yosys-*.sh: lint-grep).
    read_verilog -sv -nolatches $f
}

# Read optional top synthesis wrapper if present
set synth_wrapper "${project_root}/physical/${design_name}.sv"
if {[info exists env(SYNTH_WRAPPER)]} {
    set synth_wrapper $env(SYNTH_WRAPPER)
}
if {[file exists $synth_wrapper] && [lsearch -exact $sv_files $synth_wrapper] == -1} {
    puts "INFO: Reading synthesis wrapper: $synth_wrapper"
    read_verilog -sv -nolatches $synth_wrapper
}

# Step 4: Check hierarchy and set top module
hierarchy -check -top $design_name

# Pre-synth lint (DC status: LINT-2 comb loops, LINT-3 multi-driver,
# LINT-7 tristate, mem integrity)
yosys proc
yosys opt
yosys select -assert-none t:\$dlatch
yosys select -assert-none t:\$tribuf
yosys check -assert

# Step 5: Coarse synthesis
if {$flatten} {
    synth -top $design_name -flatten
} else {
    synth -top $design_name -hieropt
}

# Step 6: Technology mapping of flip-flops
dfflibmap -liberty $dff_lib

# Step 7: Technology mapping of combinational logic via ABC with timing constraints
set abc_cmd [list abc -liberty $target_lib]
if {$has_constr} {
    lappend abc_cmd -constr $constr_file -D $clk_period_ps
}
{*}$abc_cmd

# Step 8: Clean unused wires and cells
clean -purge

# Step 9: Reports
tee -o "${out_dir}/reports/check_design.rpt" check
set stat_cmd [list stat -liberty $target_lib]
if {$dff_lib ne $target_lib} {
    lappend stat_cmd -liberty $dff_lib
}
tee -o "${out_dir}/reports/area.rpt" {*}$stat_cmd

# Step 10: Export gate-level netlist
set netlist_file "${out_dir}/netlist/${design_name}.v"
write_verilog -noattr -noexpr -nohex $netlist_file
puts "INFO: Exported gate-level netlist: $netlist_file"

# Step 11: Export SDC timing constraints
set sdc_file "${out_dir}/netlist/${design_name}.sdc"
set sdc_fp [open $sdc_file w]
puts $sdc_fp "# Auto-generated SDC timing constraints for ${design_name} (${platform})"
puts $sdc_fp "current_design ${design_name}"
puts $sdc_fp ""
puts $sdc_fp "set clk_name \"${clk_name}\""
puts $sdc_fp "set clk_period ${clk_period}"
puts $sdc_fp ""
puts $sdc_fp "if {\[sizeof_collection \[get_ports -quiet \${clk_name}\]\] > 0} {"
puts $sdc_fp "    create_clock -name \${clk_name} -period \${clk_period} \[get_ports \${clk_name}\]"
puts $sdc_fp "    set_clock_uncertainty \[expr {\${clk_period} * 0.05}\] \[get_clocks \${clk_name}\]"
puts $sdc_fp "    set_input_delay \[expr {\${clk_period} * 0.1}\] -clock \${clk_name} \[remove_from_collection \[all_inputs\] \[get_ports \${clk_name}\]\]"
puts $sdc_fp "    set_output_delay \[expr {\${clk_period} * 0.1}\] -clock \${clk_name} \[all_outputs\]"
puts $sdc_fp "}"
close $sdc_fp
puts "INFO: Exported SDC constraints: $sdc_file"

puts "INFO: Synthesis of $design_name on $platform completed successfully."

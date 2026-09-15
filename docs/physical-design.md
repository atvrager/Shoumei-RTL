# Physical Design Flow (OpenROAD)

This document describes how to run the physical design flow for Shoumei RTL using OpenROAD Flow Scripts (ORFS) via Docker.

## Prerequisites

1.  **Docker**: Ensure Docker is installed and running.
2.  **ORFS Submodule**: The `third_party/orfs` submodule must be initialized.
    ```bash
    git submodule update --init --recursive
    ```
3.  **Generated Verilog**: Run `lake exe generate_all` (or `make codegen`) to emit the SystemVerilog under `output/sv-from-lean/`.
    ```bash
    lake exe generate_all
    ```

## Configuration

The physical design flow is configured using two files in the `physical/` directory:

### 1. `physical/config.mk`
Defines the design parameters, source files, and target platform.

```makefile
PROJECT_ROOT := $(shell git rev-parse --show-toplevel)

# Physical Design Configuration
export DESIGN_NAME = RV32IDecoder
export PLATFORM    = asap7  # Target 7nm Predictive PDK

export VERILOG_FILES = $(PROJECT_ROOT)/output/sv-from-lean/RV32IDecoder.sv
export SDC_FILE      = $(PROJECT_ROOT)/physical/constraints.sdc

# Timing Target (1GHz)
export CLK_PERIOD_NS = 1.0

# Floorplan Configuration
export CORE_UTILIZATION = 30
export CORE_ASPECT_RATIO = 1
```

### 2. `physical/constraints.sdc`
Defines timing constraints (clocks, I/O delays).

```tcl
current_design RV32IDecoder

set clk_name  vclk
set clk_port  vclk
set clk_period 1.0

create_clock -name ${clk_name} -period ${clk_period}

set_input_delay [expr ${clk_period} * 0.2] -clock ${clk_name} [all_inputs]
set_output_delay [expr ${clk_period} * 0.2] -clock ${clk_name} [all_outputs]
```

## Running the Flow

We use the official OpenROAD `builder` image. The command mounts the ORFS flow directory and the project root into the container.

Run the following command from the project root:

```bash
docker run --rm \
  -u $(id -u):$(id -g) \
  -v $(pwd)/third_party/orfs/flow:/OpenROAD-flow-scripts/flow \
  -v $(pwd):/project \
  -w /OpenROAD-flow-scripts/flow \
  openroad/flow-ubuntu22.04-builder:3d5d5a \
  bash -c 'source ../env.sh && make DESIGN_CONFIG=/project/physical/config.mk PROJECT_ROOT=/project ABC_CLOCK_PERIOD_IN_PS=1000'
```

### Explanation of Arguments:
*   `-v .../flow:/OpenROAD-flow-scripts/flow`: Mounts the ORFS flow scripts so results persist on your host machine.
*   `-v ...:/project`: Mounts your entire project root to `/project` inside the container so the flow can access your config and Verilog files.
*   `DESIGN_CONFIG`: Points the flow to your specific configuration file.
*   `PROJECT_ROOT`: Overrides the variable inside the container to point to the mounted `/project` path.
*   `ABC_CLOCK_PERIOD_IN_PS`: Explicitly sets the clock period for ABC synthesis (required if not automatically parsed from SDC).

## Results

After a successful run, artifacts are generated in `third_party/orfs/flow/results/asap7/RV32IDecoder/base/`.

Key files:
*   **GDSII Layout**: `6_final.gds`
*   **OpenDB Database**: `6_final.odb`
*   **Gate-Level Netlist**: `6_final.v`
*   **Def File**: `6_final.def`
*   **Reports**: `third_party/orfs/flow/reports/asap7/RV32IDecoder/base/`

### A Note on ASAP7 Scaling ("The 4x Problem")
Standard ASAP7 PDK releases often use a 4x coordinate scaling (to mimic 28nm dimensions) to avoid precision issues in older tools. **This ORFS flow uses 1x scaled (true physical dimension) views.**
*   The generated GDSII is in **true 7nm dimensions**.
*   **Do not** scale the GDSII down by 4x; it is already correct.
*   The database units are set to 4000 DBU/micron (0.25nm precision) to handle the fine grid.

## Troubleshooting

*   **Permissions**: If you get permission errors, ensure your user is in the `docker` group or run with `sudo` (and `sg docker` if needed).
*   **Missing Variables**: If Yosys fails with "no such variable", ensure variables in `config.mk` are exported (e.g., `export VERILOG_FILES = ...`).
*   **Floorplan Errors**: If floorplanning fails, check `CORE_UTILIZATION` or `DIE_AREA` settings in `config.mk`.

---

## ASIC Synthesis Flow (Synopsys DC / DC NXT)

In addition to OpenROAD, the CPU can be synthesized with commercial ASIC tools using the parameterizable script `physical/run-dc.tcl` and the generated filelists in `physical/`.

### Running Synthesis

```bash
export TARGET_LIBRARY=/path/to/standard_cells.db
export LINK_LIBRARIES="/path/to/multibit_cells.db /path/to/sram_macros.db"
export CLK_PERIOD_NS=5.0
export DESIGN_NAME=CPU_RV32IMAFD_Zicsr_Zifencei_Microcoded_synth

dcnxt_shell -f physical/run-dc.tcl | tee syn.log
```

Generated outputs are placed in `syn_out/`:
*   `syn_out/reports/`: `qor.rpt`, `area.rpt`, `timing.rpt`, `power.rpt`, `clock_gate.rpt`, `violators.rpt`
*   `syn_out/netlist/`: Gate-level netlist (`.v`), timing constraints (`.sdc`), and database (`.ddc`)

### ASIC Baseline: GF 12LPP+ (RV32IMAFD Core)

Synthesized with Synopsys DC NXT using GlobalFoundries 12LPP+ 7.5T RVT standard cells (`sc7p5mcpp84_base_rvt_c16`, nominal corner 0.80V, 25°C):

| Metric | Result |
|---|---|
| **Design** | `CPU_RV32IMAFD_Zicsr_Zifencei_Microcoded_synth` |
| **Architecture** | Dual-dispatch superscalar ($W=2$), RV32IMAFD (with atomics & 64-bit DP FPU) |
| **Clock Target** | 5.00 ns (200 MHz) |
| **Timing** | **Met** (WNS = 0.00 ns, TNS = 0.00 ns, 0 violating paths) |
| **Critical Path** | 4.91 ns ($F_{\max} \approx 203.7\text{ MHz}$) in `u_exec_fp/u_mul_dp` $\rightarrow$ CDB |
| **Total Cell Area** | **$47,184.8\,\mu\text{m}^2$** ($0.0472\text{ mm}^2$) |
| **Combinational Area** | $29,600.6\,\mu\text{m}^2$ (62.7%) |
| **Sequential Area** | $17,584.2\,\mu\text{m}^2$ (37.3%) |
| **Leaf Cell Count** | **143,122** (124,841 combinational, 18,281 sequential) |
| **Dynamic Power** | 3.48 mW (3.18 mW internal, 0.29 mW switching) |
| **Leakage Power** | 10.4 µW |

#### Subsystem Area Breakdown

| Subsystem | Area ($\mu\text{m}^2$) | Share | Notes |
|---|---|---|---|
| FP Rename & PRF | 11,961.4 | 25.4% | $64\times 64$-bit FP Physical Register File + rename logic |
| DP FP Execution Unit | 11,779.4 | 25.0% | Double-precision `FPAdderD`, `FPMulD`, `FPDivD`, `FPSqrtD`, `FPFMAD` |
| Integer Rename & PRF | 7,767.0 | 16.5% | $64\times 32$-bit Integer Physical Register File + rename logic |
| Integer Mul/Div Unit | 1,706.5 | 3.6% | Pipelined multiplier & radix-4 divider |
| Load-Store Unit | 1,641.2 | 3.5% | 64-bit LSU datapath & 8-entry store buffer |
| Reservation Stations | 4,456.6 | 9.4% | FP (64b), Memory (64b), Integer, Mul/Div, Branch |
| Queues & ROB | 2,757.4 | 5.9% | 16-entry dual-retire ROB, instruction & PC queues |
| Integer ALU & Branch | 445.5 | 0.9% | Dual-issue integer execution units |
| Control & Decoders | 489.2 | 1.0% | Dual `RV32GDecoder`, microcode sequencer & fetch |
| Glue & Clock Gating | 4,180.6 | 8.8% | CDB muxes, bypass FIFOs, 52 clock gating cells |

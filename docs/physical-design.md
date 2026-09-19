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
export DESIGN_NAME=CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth

dcnxt_shell -f physical/run-dc.tcl | tee syn.log
```

Generated outputs are placed in `syn_out/`:
*   `syn_out/reports/`: `qor.rpt`, `area.rpt`, `timing.rpt`, `power.rpt`, `clock_gate.rpt`, `violators.rpt`
*   `syn_out/netlist/`: Gate-level netlist (`.v`), timing constraints (`.sdc`), and database (`.ddc`)

### ASIC Synthesis Results: GF 12LPP+ (RV64IMAFD Core)

Synthesized with Synopsys DC NXT using GlobalFoundries 12LPP+ 7.5T RVT standard cells (`sc7p5mcpp84_base_rvt_c16`, nominal corner 0.80V, 25°C):

| Metric | 200 MHz Baseline | 750 MHz Pipelined |
|---|---|---|
| **Design** | `CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth` | `CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth` |
| **Architecture** | Dual-dispatch ($W=2$) RV64IMAFD | Dual-dispatch ($W=2$) RV64IMAFD |
| **Clock Target** | 5.00 ns (200 MHz) | 1.333 ns (750 MHz) |
| **Timing Status** | **Met** (WNS = 0.00 ns, 0 violations) | **Met** (WNS = 0.00 ns, 0 violations) |
| **Critical Path Delay** | 4.85 ns | **1.27 ns** ($F_{\max} \approx 787.4\text{ MHz}$) |
| **Max Logic Levels (Clock)** | 161 levels | **62 levels** |
| **Total Cell Area** | $55,499.8\,\mu\text{m}^2$ ($0.0555\text{ mm}^2$) | **$57,269.8\,\mu\text{m}^2$** ($0.0573\text{ mm}^2$, +3.2%) |
| **Combinational Area** | $35,449.5\,\mu\text{m}^2$ (63.9%) | $36,776.6\,\mu\text{m}^2$ (64.2%) |
| **Sequential Area** | $20,050.4\,\mu\text{m}^2$ (36.1%) | $20,493.2\,\mu\text{m}^2$ (35.8%) |
| **Leaf Cell Count** | 168,140 | 184,285 |
| **Dynamic Power** | 3.90 mW | 14.97 mW |
| **Leakage Power** | 12.2 µW | 13.2 µW |

#### Pipeline Timing Cuts (750 MHz Target)

To eliminate long timing paths without regressing architectural correctness:
1. **FPExecUnit Misc/Converter Pipeline Register**: Added 1-cycle pipeline register decoupling RS issue and long converter from CDB writeback, breaking the 174-level CDB loop.
2. **FPMultiplierD 3-Stage Split**: Pipelined 106-bit Kogge-Stone CPA across Stage 2 and Stage 3 (norm/round/pack), eliminating the critical multiplier CPA bottleneck.
3. **FPFMAD 4-Stage Delay Matching**: Inter-unit pipeline registers between multiplier and adder with 4-stage control delay lines, eliminating the 216-level composite path.
4. **Balanced Priority Encoder & Reductions**: Replaced serial linear chains in `Int64ToFP` and `FPToInt64` with an 8x8 parallel tree priority encoder and balanced logarithmic OR/AND trees.

#### Subsystem Area Breakdown (750 MHz)

| Subsystem | Area ($\mu\text{m}^2$) | Share | Notes |
|---|---|---|---|
| DP FP Execution Unit | 13,347.0 | 23.3% | Pipelined `FPAdderD`, `FPMulD`, `FPFMAD`, `FPDivD`, `FPSqrtD`, `FPLongConverter` |
| Integer Rename & PRF | 12,971.8 | 22.7% | $64\times 64$-bit Integer Physical Register File + rename logic (`IntRenameStage_W2_64`) |
| FP Rename & PRF | 9,088.9 | 15.9% | $64\times 64$-bit FP Physical Register File + rename logic (`FPRenameStage_W1_64`) |
| Integer Mul/Div Unit | 5,758.1 | 10.1% | 64-bit Pipelined multiplier & radix-4 divider |
| Reservation Stations | 3,717.5 | 6.5% | FP, Memory, Integer, Mul/Div, Branch (modular RS subcircuits) |
| Load-Store Unit | 2,282.2 | 4.0% | 64-bit LSU datapath & 8-entry store buffer |
| Queues & ROB | 2,790.1 | 4.9% | 16-entry dual-retire ROB, instruction & PC queues |
| Integer ALU & Branch | 1,238.3 | 2.2% | Dual-issue 64-bit integer execution units & branch comparator |
| CSR File | 534.7 | 0.9% | Modular `CSRFile_RV64IMAFD_Zicsr_Zifencei_Microcoded` |
| Scoreboard Busy Tables | 397.1 | 0.7% | Modular `BusyTable_W2` and `FPBusyTable` |
| Microcode & Control | 309.7 | 0.5% | Modular `TrapSequencer` and `FetchStage_W2` |
| Glue & Clock Gating | 4,834.4 | 8.4% | CDB muxes, bypass FIFOs, comparators, ICG clock gating cells |

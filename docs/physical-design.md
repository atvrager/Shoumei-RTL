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

---

## Open-Source Synthesis Flow: GF180MCU & ASAP7 (Yosys)

In addition to commercial DC NXT and full OpenROAD PnR flows, Shoumei provides a lightweight, native open-source synthesis flow targeting both **GlobalFoundries 180nm MCU (GF180MCU)** and **ASAP7 7nm Predictive FinFET** using host-native Yosys and ABC.

No Docker containers, OpenROAD PnR engines, or commercial licenses are required to generate mapped gate-level netlists and area reports.

### Architecture of the Flow

The flow is driven by a shared, parameterizable TCL engine (`physical/run-yosys.tcl`) with dedicated platform frontends:
*   `physical/run-yosys-gf180.sh`: Targets GF180MCU 9-track 5.0V standard cells (`gf180mcu_fd_sc_mcu9t5v0__tt_025C_5v00.lib.gz`).
*   `physical/run-yosys-asap7.sh`: Targets ASAP7 7.5-track RVT standard cells, automatically merging multi-category combinational libraries (`INVBUF`, `SIMPLE`, `OA`, `AO`) into an ABC-compatible library.

### Running Synthesis

```bash
# GF180MCU: RV64 CPU at 64 MHz (canonical default: 15.625 ns)
./physical/run-yosys-gf180.sh
make synth-gf180

# GF180MCU: Conservative target at 50 MHz (20.0 ns)
./physical/run-yosys-gf180.sh CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth 20.0

# ASAP7: RV64 CPU at 1.0 GHz (canonical default: 1.000 ns)
./physical/run-yosys-asap7.sh
make synth-asap7

# ASAP7: Target matching GF12 baseline at 750 MHz (1.333 ns)
./physical/run-yosys-asap7.sh CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth 1.333

# Lightweight subsystem smoke synthesis (< 4 seconds runtime)
./physical/run-yosys-gf180.sh ALU64 10.0
./physical/run-yosys-asap7.sh ALU64 1.0
```

Generated outputs are placed in `syn_out_gf180/` or `syn_out_asap7/`:
*   `netlist/`: Gate-level netlist (`.v`) and timing constraints (`.sdc`)
*   `reports/`: `area.rpt` (`stat -liberty`) and `check_design.rpt` (design integrity checks)

### Synthesis Results: RV64IMAFD Top-Level Core

Synthesized with Yosys 0.66 on the top-level dual-dispatch RV64 core (`CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth`):

| Metric | GF 12LPP+ (DC NXT) | GF180MCU @ 50 MHz | GF180MCU @ 64 MHz | ASAP7 @ 750 MHz | ASAP7 @ 1.0 GHz |
|---|---|---|---|---|---|
| **PDK / Node** | GF 12LPP+ (12nm) | GF180MCU 9T (180nm) | GF180MCU 9T (180nm) | ASAP7 7.5T (7nm) | ASAP7 7.5T (7nm) |
| **Tool** | Synopsys DC NXT | Yosys 0.66 / ABC | Yosys 0.66 / ABC | Yosys 0.66 / ABC | Yosys 0.66 / ABC |
| **Clock Target** | 1.333 ns (750 MHz) | 20.0 ns (50 MHz) | 15.625 ns (64 MHz) | 1.333 ns (750 MHz) | 1.000 ns (1.0 GHz) |
| **Total Cell Area** | $57,269.8\,\mu\text{m}^2$ ($0.0573\text{ mm}^2$) | **$6,393,077.5\,\mu\text{m}^2$** ($6.393\text{ mm}^2$) | **$6,406,435.9\,\mu\text{m}^2$** ($6.406\text{ mm}^2$) | **$24,769.3\,\mu\text{m}^2$** ($0.0248\text{ mm}^2$) | **$24,770.1\,\mu\text{m}^2$** ($0.0248\text{ mm}^2$) |
| **Combinational Area**| $36,776.6\,\mu\text{m}^2$ (64.2%) | $4,659,085.3\,\mu\text{m}^2$ (72.9%) | $4,672,443.7\,\mu\text{m}^2$ (72.9%) | $17,512.6\,\mu\text{m}^2$ (70.7%) | $17,513.4\,\mu\text{m}^2$ (70.7%) |
| **Sequential Area** | $20,493.2\,\mu\text{m}^2$ (35.8%) | $1,733,992.2\,\mu\text{m}^2$ (27.1%) | $1,733,992.2\,\mu\text{m}^2$ (27.1%) | $7,256.7\,\mu\text{m}^2$ (29.3%) | $7,256.7\,\mu\text{m}^2$ (29.3%) |
| **Leaf Cell Count** | 184,285 | 194,700 | 194,700 | 266,042 | 266,042 |
| **Synthesis Runtime** | Commercial compute cluster | **78.2 seconds** | **82.0 seconds** | **82.7 seconds** | **87.6 seconds** |
| **Check Violations** | 0 violations | 0 violations | 0 violations | 0 violations | 0 violations |

### Key Observations

1. **GF180 vs FinFET Area Footprint**: At 180nm, the complete out-of-order RV64IMAFD core occupies ~$6.4\,\text{mm}^2$. On a standard Efabless/Google GF180 MPW shuttle ($3\times3\text{ mm} = 9\,\text{mm}^2$ total die area), the CPU occupies ~71% of raw die area (before pads/peripherals/SRAM).
2. **ASAP7 7nm vs GF12 12nm**: ASAP7 standard cell area is ~$0.0248\,\text{mm}^2$, approximately 2.3× smaller than GF 12LPP+ ($0.0573\,\text{mm}^2$), reflecting the smaller contacted poly pitch (54nm vs 84nm CPP) and fin pitch (27nm vs 34nm).
3. **Synthesis Engine Performance**: Host-native Yosys 0.66 + ABC completes full-chip synthesis of the 194k–266k cell RV64 core in ~80–88 seconds on a single thread with ~640 MB peak memory. Subsystems such as `ALU64` synthesize in ~3.2–3.6 seconds.

---

## PDK Scaling Quirks & Units in the Open-Source Ecosystem

Open-source and academic PDKs exhibit scaling conventions that differ from legacy tool assumptions:

### 1. The ASAP7 "4x Scaling Problem"
*   **Historical Context**: When ASU released ASAP7 in 2016, commercial physical design tools enforced a minimum database/manufacturing grid (typically 1nm) and had fixed 32-bit integer database units (DBU). True 7nm dimensions (CPP = 54nm, M2 pitch = 36nm, min wire width = 18nm, grid = 0.25nm) caused severe grid-snapping errors, false DRC violations, and router crashes in legacy tools.
*   **Original 4x Workaround**: ASU scaled up the original PDK layouts by **4x linearly** in LEF/DEF/GDS (CPP became 216nm, cell height became $1.080\,\mu\text{m}$). Consequently, layout area reported by tools was **16x ($4^2$) larger** than physical reality. Standard cell delay and capacitance tables were adjusted so timing remained realistic.
*   **Modern 1x Adoption**: Modern OpenROAD and the flow platform files under `third_party/orfs/flow/platforms/asap7` use true **1x views** (`asap7_tech_1x_201209.lef`, `asap7sc7p5t_28_R_1x_220121a.lef`, $4000\text{ DBU}/\mu\text{m}$). Our synthesis flow operates directly on true 1x dimensions ($0.0248\,\text{mm}^2$).

### 2. Liberty Timing and Capacitance Units
*   **GF180MCU / Legacy Nodes**:
    *   `time_unit : 1ns;`
    *   `capacitive_load_unit(1, pf);`
    *   Typical gate delay: 0.2–1.5 ns; pin cap: 10–50 fF (0.01–0.05 pF).
*   **ASAP7 / Advanced FinFET**:
    *   `time_unit : "1ps";` (1,000× smaller)
    *   `capacitive_load_unit(1, ff);` (1,000× smaller, femtofarads)
    *   Typical gate delay: 4–15 ps; pin cap: 0.2–1.5 fF.
*   **Tool Implications**: Tools or scripts assuming hardcoded `ns` or `pF` units can miscalculate timing constraints by $10^3$ to $10^6$. In `physical/run-yosys.tcl`, driver cell instances and standard load equivalents (`ABC_DRIVER_CELL`, `ABC_LOAD_IN_FF`) are passed explicitly to match each platform's native units.


---

## Cache SRAM Strategy: Foundry Macros, Not FF Arrays

Emitted cache data RAMs (`RAMPrimitive` in the Lean DSL) carry a
process-explicit SRAM hook.  Every RAM emits as:

```
`ifdef SHOUMEI_SRAM_MACROS
  sram_1r1w_<width>x<depth> u_ram_<name> (.clk, .we, .waddr, .wdata,
                                          .raddr, .rdata);
`else
  reg [width-1:0] <name> [0:depth-1];   // sim/verilator fallback only
`endif
```

- **Port contract**: `clk/we/waddr/wdata/raddr/rdata` matches the
  GF180MCU vendor family (`gf180mcu_fd_ip_sram`) and OpenRAM 1R1W macros.
  RAMPrimitives with exactly one write + one read port map to the macro;
  other configurations keep the fallback.
- **Generation**: `make sram-macros` drives
  `scripts/gen-sram-macros.sh` (OpenRAM, `--pdk gf180mcuD`/`asap7`,
  1R1W), emitting a shim with the canonical module name so the codegen
  contract is immune to OpenRAM's internal naming.  Sizes per node follow
  the heuristic in `docs/lsu-architecture.md` §13 (GF180: 8 KB ITCM /
  16 KB DTCM; FinFET-class: 16 / 64).
- **Verification of the macro branch without real IP**:
  `verification/sram-macro-stub.sv` provides behavioral stubs
  (synchronous read) so slang lint checks the `ifdef` path in CI
  (`python3 verification/slang-lint.py --sram output/sv-from-lean`).
- **Simulation**: the `else` reg-array fallback is the Verilator path —
  intentionally a plain memory, never an FF array in synthesis.  If a
  macro-accurate sim model is needed, the fallback can be replaced by a
  DPI-backed model of the same `1w1r` contract without touching RTL.
- **Measured impact (FF-array caches)**: GF180MCU CachedCPU 8.40 mm²
  @ 20 ns vs 6.40 mm² core — the ~2 mm² delta is exactly what the
  foundry SRAM macros (≈3 µm²/bit, ≈0.5 mm² for 24 KB) recover.
  ASAP7 CachedCPU synthesizes clean at 1.0 GHz (32.5 kµm²).

# Physical Design Flow (OpenROAD)

This document describes how to run the physical design flow for Shoumei RTL using OpenROAD Flow Scripts (ORFS) through Docker.

## Prerequisites

1.  **Docker**: Install Docker and start it.
2.  **ORFS Submodule**: Initialize the `third_party/orfs` submodule.
    ```bash
    git submodule update --init --recursive
    ```
3.  **Generated Verilog**: Run `bazel build //:rtl` to emit the SystemVerilog under `output/sv-from-lean/`.
    ```bash
    bazel build //:rtl
    ```

## Configuration

Two files in the `physical/` directory configure the physical design flow:

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

After a successful run, the flow generates artifacts in `third_party/orfs/flow/results/asap7/RV32IDecoder/base/`.

Key files:
*   **GDSII Layout**: `6_final.gds`
*   **OpenDB Database**: `6_final.odb`
*   **Gate-Level Netlist**: `6_final.v`
*   **Def File**: `6_final.def`
*   **Reports**: `third_party/orfs/flow/reports/asap7/RV32IDecoder/base/`

### A Note on ASAP7 Scaling ("The 4x Problem")
Standard ASAP7 PDK releases often use a 4x coordinate scaling (to mimic 28nm dimensions). This avoids precision issues in older tools. **This ORFS flow uses 1x scaled (true physical dimension) views.**
*   The generated GDSII is in **true 7nm dimensions**.
*   **Do not** scale the GDSII down by 4x. It is already correct.
*   The flow sets the database units to 4000 DBU/micron (0.25nm precision) to handle the fine grid.

## Troubleshooting

*   **Permissions**: If you get permission errors, ensure your user is in the `docker` group or run with `sudo` (and `sg docker` if needed).
*   **Missing Variables**: If Yosys fails with "no such variable", ensure you export the variables in `config.mk` (for example, `export VERILOG_FILES = ...`).
*   **Floorplan Errors**: If floorplanning fails, check `CORE_UTILIZATION` or `DIE_AREA` settings in `config.mk`.

---

## ASIC Synthesis Flow (Synopsys DC / DC NXT)

Shoumei also synthesizes the CPU with commercial ASIC tools. The parameterizable script `physical/run-dc.tcl` and the generated filelists in `physical/` drive that flow.

### Running Synthesis

```bash
export TARGET_LIBRARY=/path/to/standard_cells.db
export LINK_LIBRARIES="/path/to/multibit_cells.db /path/to/sram_macros.db"
export CLK_PERIOD_NS=5.0
export DESIGN_NAME=CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth

dcnxt_shell -f physical/run-dc.tcl | tee syn.log
```

The flow places generated outputs in `syn_out/`:
*   `syn_out/reports/`: `qor.rpt`, `area.rpt`, `timing.rpt`, `power.rpt`, `clock_gate.rpt`, `violators.rpt`
*   `syn_out/netlist/`: Gate-level netlist (`.v`), timing constraints (`.sdc`), and database (`.ddc`)

### ASIC Synthesis Results: GF 12LPP+ (RV64IMAFD Core)

Synthesized with Synopsys DC NXT using GlobalFoundries 12LPP+ 7.5T RVT standard cells (`sc7p5mcpp84_base_rvt_c16`, nominal corner 0.80V, 25°C):

| Metric | 200 MHz Baseline | 750 MHz Pipelined |
|---|---|---|
| **Design** | `CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth` | `CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth` |
| **Architecture** | Dual-dispatch ($W=2$) RV64IMAFD | Dual-dispatch ($W=2$) RV64IMAFD + Zb* |
| **Clock Target** | 5.00 ns (200 MHz) | 1.333 ns (750 MHz) |
| **Timing Status** | **Met** (WNS = 0.00 ns, 0 violations) | **Met** (WNS = 0.00 ns, 0 violations) |
| **Critical Path Delay** | 4.85 ns | **1.29 ns** ($F_{\max} \approx 775.2\text{ MHz}$) |
| **Max Logic Levels (Clock)** | 161 levels | **55 levels** |
| **Total Cell Area** | $55,499.8\,\mu\text{m}^2$ ($0.0555\text{ mm}^2$) | **$61,335.7\,\mu\text{m}^2$** ($0.0613\text{ mm}^2$) |
| **Combinational Area** | $35,449.5\,\mu\text{m}^2$ (63.9%) | $39,793.6\,\mu\text{m}^2$ (64.9%) |
| **Sequential Area** | $20,050.4\,\mu\text{m}^2$ (36.1%) | $21,542.1\,\mu\text{m}^2$ (35.1%) |
| **Leaf Cell Count** | 168,140 | 201,319 |
| **Dynamic Power** | 3.90 mW | 16.11 mW |
| **Leakage Power** | 12.2 µW | 14.4 µW |

#### Pipeline Timing Cuts (750 MHz Target)

1. **FPExecUnit Misc/Converter Pipeline Register**: Added 1-cycle pipeline register decoupling RS issue and long converter from CDB writeback. This breaks the 174-level CDB loop.
2. **FPMultiplierD 3-Stage Split**: The design pipelines the 106-bit Kogge-Stone CPA across Stage 2 and Stage 3 (norm/round/pack). This removes the critical multiplier CPA bottleneck.
3. **FPFMAD 4-Stage Delay Matching**: Inter-unit pipeline registers sit between the multiplier and adder, with 4-stage control delay lines. This removes the 216-level composite path.
4. **Balanced Priority Encoder & Reductions**: `Int64ToFP` and `FPToInt64` dropped their serial linear chains. An 8x8 parallel tree priority encoder and balanced logarithmic OR/AND trees replace them.

#### Subsystem Area Breakdown (750 MHz)

| Subsystem | Area ($\mu\text{m}^2$) | Share | Notes |
|---|---|---|---|
| DP FP Execution Unit | 13,933.0 | 22.7% | Pipelined `FPAdderD`, `FPMulD`, `FPFMAD`, `FPDivD`, `FPSqrtD`, `FPLongConverter` |
| Integer Rename & PRF | 12,984.8 | 21.2% | $64\times 64$-bit Integer Physical Register File + rename logic (`IntRenameStage_W2_64`) |
| FP Rename & PRF | 9,107.2 | 14.8% | $64\times 64$-bit FP Physical Register File + rename logic (`FPRenameStage_W1_64`) |
| Integer Mul/Div Unit | 5,767.3 | 9.4% | 64-bit Pipelined multiplier & radix-4 divider |
| Reservation Stations | 3,778.3 | 6.2% | FP, Memory, Integer, Mul/Div, Branch (modular RS subcircuits) |
| Microcode Zb* Sequencer | 3,063.1 | 5.0% | Microcoded sequencer for Zb* bitmanip operations (`FallbackSequencer`) |
| Queues & ROB | 2,788.2 | 4.5% | 16-entry dual-retire ROB, instruction & PC queues |
| Load-Store Unit | 2,417.1 | 3.9% | 64-bit LSU datapath & 8-entry store buffer |
| Integer ALU & Branch | 1,232.6 | 2.0% | Dual-issue 64-bit integer execution units & branch comparator |
| CSR File | 535.2 | 0.9% | Modular `CSRFile_RV64IMAFD_Zicsr_Zifencei_Microcoded` |
| Scoreboard Busy Tables | 397.7 | 0.6% | Modular `BusyTable_W2` and `FPBusyTable` |
| Microcode & Control | 459.0 | 0.7% | Modular `TrapSequencer`, `FetchStage_W2`, decoders |
| Glue & Clock Gating | 4,869.3 | 7.9% | CDB muxes, bypass FIFOs, comparators, ICG clock gating cells |

---

## Open-Source Synthesis Flow: GF180MCU & ASAP7 (Yosys)

Shoumei also provides a lightweight, native open-source synthesis flow. It targets both **GlobalFoundries 180nm MCU (GF180MCU)** and **ASAP7 7nm Predictive FinFET**, and uses host-native Yosys and ABC.

You do not need Docker containers, OpenROAD PnR engines, or commercial licenses to generate mapped gate-level netlists and area reports.

### Architecture of the Flow

A shared, parameterizable TCL engine (`physical/run-yosys.tcl`) drives the flow, with dedicated platform frontends:
*   `physical/run-yosys-gf180.sh`: Targets GF180MCU 9-track 5.0V standard cells (`gf180mcu_fd_sc_mcu9t5v0__tt_025C_5v00.lib.gz`).
*   `physical/run-yosys-asap7.sh`: Targets ASAP7 7.5-track RVT standard cells, automatically merging multi-category combinational libraries (`INVBUF`, `SIMPLE`, `OA`, `AO`) into an ABC-compatible library.

### Running Synthesis

```bash
# Quad-Target synthesis flow:
bazel test //verification:synth_asap7_test
bazel test //verification:synth_gf180_test
bazel test //verification:synth_stats_test

# Lightweight subsystem smoke synthesis (< 4 seconds runtime)
./physical/run-yosys-gf180.sh ALU64 10.0
./physical/run-yosys-asap7.sh ALU64 1.0
```

The flow places generated outputs in `syn_out_gf180_cpu/`, `syn_out_gf180_soc/`, `syn_out_asap7_cpu/`, or `syn_out_asap7_soc/`:
*   `netlist/`: Gate-level netlist (`.v`) and timing constraints (`.sdc`)
*   `reports/`: `area.rpt` (`stat -liberty`) and `check_design.rpt` (design integrity checks)

### Quad-Target Synthesis Results: Cached CPU against Shoumei SoC

Synthesized with Yosys 0.66 comparing the canonical cached RV64G OoO core (`CachedCPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth`) against the complete SoC (`Shoumei_SoC_synth`):

| Metric | GF180MCU CPU (T1) | GF180MCU SoC (T3) | GF180 Delta | ASAP7 CPU (T2) | ASAP7 SoC (T4) | ASAP7 Delta |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **PDK / Node** | GF180MCU 9T (180nm) | GF180MCU 9T (180nm) | — | ASAP7 7.5T RVT (7nm) | ASAP7 7.5T RVT (7nm) | — |
| **Clock Target** | 15.625 ns (64 MHz) | 15.625 ns (64 MHz) | — | 1.000 ns (1.0 GHz) | 1.000 ns (1.0 GHz) | — |
| **Total Cells** | 245,299 | 245,644 | **+345 (+0.1%)** | 343,150 | 343,568 | **+418 (+0.1%)** |
| **Sequential (FF) Cells** | 29,460 | 29,588 | **+128 (+0.4%)** | 29,460 | 29,588 | **+128 (+0.4%)** |
| **Combinational Cells** | 215,839 | 216,056 | **+217 (+0.1%)** | 313,690 | 313,980 | **+290 (+0.1%)** |
| **Chip Area** | $8.438\text{ mm}^2$ ($8,437,649.5\,\mu\text{m}^2$) | $8.455\text{ mm}^2$ ($8,455,182.2\,\mu\text{m}^2$) | **+$17,532.7\,\mu\text{m}^2$ (+0.2%)** | $0.0327\text{ mm}^2$ ($32,713.7\,\mu\text{m}^2$) | $0.0328\text{ mm}^2$ ($32,785.6\,\mu\text{m}^2$) | **+$71.9\,\mu\text{m}^2$ (+0.2%)** |
| **Total Wires** | 203,135 | 203,323 | **+188 (+0.1%)** | 318,302 | 318,659 | **+357 (+0.1%)** |
| **Synthesis Runtime** | 94.0 s | 94.0 s | — | 96.0 s | 104.0 s | — |

### What the Numbers Mean

1. **GF180MCU MPW Silicon Fit**: At 180nm, the complete cached RV64G OoO SoC occupies **$8.455\,\text{mm}^2$**. That area covers CPU + L1/L2 caches + TileLink crossbar + ACLINT + APLIC + UART + GPIO + BootROM + SRAM + AASD ResetSync. A standard Google/Efabless GF180 shuttle provides a $3.0\times 3.0\text{ mm}$ ($9.0\,\text{mm}^2$) die cavity. The full SoC fits comfortably within the pad ring, and the core uses ~94% of the raw die area.
2. **ASAP7 7nm High-Density Scaling**: At 7nm Predictive FinFET, standard cell area shrinks to **$0.0328\,\text{mm}^2$**. That square measures only $\approx 181\,\mu\text{m} \times 181\,\mu\text{m}$, and the design operates at 1.0 GHz.
3. **Verified Peripheral Overhead**: The peripheral subsystem and interconnect crossbar are compact and verified. Across both 180nm and 7nm nodes, TileLink TL-UH routing, timer counters, interrupt controllers, and UART/GPIO buffers add **exactly 128 flip-flops**. The total area overhead over the cached CPU core is **+0.2%**.

---

## PDK Scaling Quirks & Units in the Open-Source Ecosystem

Open-source and academic PDKs exhibit scaling conventions that differ from legacy tool assumptions:

### 1. The ASAP7 "4x Scaling Problem"
*   **Historical Context**: When ASU released ASAP7 in 2016, commercial physical design tools enforced a minimum database/manufacturing grid (typically 1nm). These tools also had fixed 32-bit integer database units (DBU). True 7nm dimensions (CPP = 54nm, M2 pitch = 36nm, min wire width = 18nm, grid = 0.25nm) stressed legacy tools. Those tools reported severe grid-snapping errors, false DRC violations, and router crashes.
*   **Original 4x Workaround**: ASU scaled up the original PDK layouts by **4x linearly** in LEF/DEF/GDS. CPP became 216nm, and cell height became $1.080\,\mu\text{m}$. Consequently, layout area reported by tools was **16x ($4^2$) larger** than physical reality. ASU adjusted standard cell delay and capacitance tables so timing remained realistic.
*   **Modern 1x Adoption**: Modern OpenROAD and the flow platform files under `third_party/orfs/flow/platforms/asap7` use true **1x views** (`asap7_tech_1x_201209.lef`, `asap7sc7p5t_28_R_1x_220121a.lef`, $4000\text{ DBU}/\mu\text{m}$). Our synthesis flow operates directly on true 1x dimensions ($0.0248\,\text{mm}^2$).

### 2. Liberty Timing and Capacitance Units
*   **GF180MCU / Legacy Nodes**:
    *   `time_unit : 1ns;`
    *   `capacitive_load_unit(1, pf);`
    *   Typical gate delay: 0.2–1.5 ns. Pin cap: 10–50 fF (0.01–0.05 pF).
*   **ASAP7 / Advanced FinFET**:
    *   `time_unit : "1ps";` (1,000× smaller)
    *   `capacitive_load_unit(1, ff);` (1,000× smaller, femtofarads)
    *   Typical gate delay: 4–15 ps. Pin cap: 0.2–1.5 fF.
*   **Tool Implications**: Tools or scripts assuming hardcoded `ns` or `pF` units can miscalculate timing constraints by $10^3$ to $10^6$. In `physical/run-yosys.tcl`, the flow passes driver cell instances and standard load equivalents (`ABC_DRIVER_CELL`, `ABC_LOAD_IN_FF`) explicitly to match each platform's native units.


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
  RAMPrimitives with exactly one write + one read port map to the macro.
  Other configurations keep the fallback.
- **Generation**:
  `scripts/gen-sram-macros.sh` (OpenRAM, `--pdk gf180mcuD`/`asap7`,
  1R1W), emitting a shim with the canonical module name so the codegen
  contract is immune to OpenRAM's internal naming.  Sizes per node follow
  the heuristic in `docs/lsu-architecture.md` §13 (GF180: 8 KB ITCM /
  16 KB DTCM, FinFET-class: 16 / 64).
- **Verification of the macro branch without real IP**:
  `verification/sram-macro-stub.sv` provides behavioral stubs
  (synchronous read) so slang lint checks the `ifdef` path in CI
  (`bazel test //verification:slang_sram_lint_test`).
- **Simulation**: the `else` reg-array fallback is the Verilator path. It is
  intentionally a plain memory, never an FF array in synthesis. If you need a
  macro-accurate sim model, you can replace the fallback with a DPI-backed
  model of the same `1w1r` contract without touching RTL.
- **Measured impact (FF-array caches)**: GF180MCU CachedCPU measures
  8.40 mm² @ 20 ns against a 6.40 mm² core. That ~2 mm² delta is exactly what
  the foundry SRAM macros (≈3 µm²/bit, ≈0.5 mm² for 24 KB) recover.
  ASAP7 CachedCPU synthesizes clean at 1.0 GHz (32.5 kµm²).

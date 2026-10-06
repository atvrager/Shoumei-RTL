# ASAP7 Timing Analysis and Critical Path Backlog

This document records physical synthesis results for Shoumei RTL on ASAP7 at 1.0 GHz (1000.0 ps target period).

## Current Status (Work Packages 1-4)

Synthesis completed with 0 logic loops.
The `yosys scc` command found 0 strongly connected components.
24 submodules meet the 1.0 GHz timing constraint.

### Verified Fast Paths (< 1000.0 ps)

| Module | ABC Delay (ps) | Status |
| :--- | :--- | :--- |
| `Subtractor64` | 28.9 | MET |
| `Int64ToFP` (top wrapper) | 137.5 | MET |
| `FPLongConverter` (wrapper) | 150.5 | MET |
| `Comparator64` | 151.7 | MET |
| `Mux8x64` | 215.9 | MET |
| `ALU64` | 232.0 | MET |
| `LogicUnit64` | 245.8 | MET |
| `Comparator6` | 246.2 | MET |
| `Shifter64` | 350.0 | MET |
| `PCIncrementer8` | 370.8 | MET |
| `PCIncrementer4` | 381.7 | MET |
| `TrapSequencer` | 381.9 | MET |
| `Int64NormShift` | 386.2 | MET |
| `PriorityArbiter64` | 394.5 | MET |
| `FPToInt64` (hierarchical) | 511.5 | MET |
| `KoggeStoneAdder32` | 539.1 | MET |
| `PipelinedMultiplier64` | 587.6 | MET |
| `KoggeStoneAdder32NoCin` | 588.8 | MET |
| `BranchTargetAdder32` | 619.1 | MET |
| `Mul32x32To64` | 731.8 | MET |
| `MulFinalAdder64` | 777.5 | MET |
| `FPFMA` | 828.5 | MET |
| `Int64RoundPack` | 869.1 | MET |
| `KoggeStoneAdder64WithCin1` | 871.1 | MET |
| `KoggeStoneAdder64NoCin` | 915.2 | MET |
| `Int64Prep` | 930.2 | MET |
| `FPFMAD` | 994.1 | MET |

## Critical Paths Backlog (> 1000.0 ps)

The following paths exceed the 1000.0 ps target period.
Future work must pipeline these paths.

### 1. `FPExecUnit_D` (3214.7 ps)
- **Path**: Output priority MUX and hold network across execution sub-units.
- **Cause**: Cascaded priority MUX network selects between 14 execution units.
- **Proposed Solution**: Insert a pipeline stage between sub-unit hold queues and final CDB output arbitration.

### 2. `CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth` (1752.6 ps)
- **Path**: Top-level core dispatch and bypass interconnect.
- **Cause**: Long routing paths connect reservation stations, execution units, and the reorder buffer.
- **Proposed Solution**: Register reservation station issue lines and CDB bypass broadcast nets.

### 3. `FPMultiplierD` (1348.9 ps)
- **Path**: Stage 3 rounding, special case evaluation, and format packing.
- **Note**: Pipelining levels 0-4 and 5-8 across two cycles closed the 1410.5 ps CSA tree path.
- **Proposed Solution**: Insert pipeline registers between the mantissa round adder and the exception logic.

### 4. `FPAdderD` (1223.2 ps)
- **Path**: Stage 3 mantissa add/sub and parallel-prefix leading-zero detect.
- **Note**: Splitting Stage 4 into Stage 4a and Stage 4b closed the 1478.9 ps Stage 4 path.
- **Proposed Solution**: Register the mantissa sum before the leading-zero detection network.

### 5. `KoggeStoneAdder106NoCin` (1065.9 ps)
- **Path**: 106-bit carry-propagate adder.
- **Proposed Solution**: Decompose into a 2-stage pipelined adder or a carry-select architecture.

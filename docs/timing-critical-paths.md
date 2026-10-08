# ASAP7 Timing Analysis and Critical Path Backlog

This document records physical synthesis results for Shoumei RTL on ASAP7 at 1.0 GHz (1000.0 ps target period).

## Current Status (Work Packages 1-4)

Synthesis completed with 0 logic loops.
The `yosys scc` command found 0 strongly connected components.
31 modules meet the 1.0 GHz timing constraint.

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
| `FPExecUnit_D` (top wrapper) | 930.2 | MET |
| `Int64Prep` | 930.2 | MET |
| `FPAdderD` | 987.1 | MET |
| `FPMultiplierD` | 992.0 | MET |
| `FPFMAD` | 994.1 | MET |
| `KoggeStoneAdder106NoCin` | 996.0 | MET |

## Critical Paths Backlog (> 1000.0 ps)

The following paths exceed the 1000.0 ps target period.
Future work must pipeline these paths.

### 1. `CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth` (1752.6 ps)
- **Path**: Top-level core dispatch and bypass interconnect.
- **Cause**: Long routing paths connect reservation stations, execution units, and the reorder buffer.
- **Proposed Solution**: Register reservation station issue lines and CDB bypass broadcast nets.

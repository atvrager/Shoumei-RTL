# Roadmap

Current directions and future milestones for Shoumei RTL.

---

## 1. Near-term

### Microarchitecture-targeted test generation
- Automatically synthesize test ELFs directly from Lean microarchitectural models to systematically exercise edge states.
- Target the 20 cataloged hazard patterns (see [docs/hazard-patterns.md](hazard-patterns.md) and [docs/test-generation.md](test-generation.md)):
  - Forwarding races, CDB multi-wakeups, and structural buffer exhaustion.
  - Store buffer youngest-match forwarding across byte/word/doubleword width combinations.
  - Exception and misprediction recovery interleavings.

### C extension (RV64GC)
- Implement 16-bit compressed instruction decompression in Fetch/Decode.
- Support unaligned 32-bit instruction fetch across 64-bit boundaries.
- Target: Full RV64GC compliance suite pass.

---

## 2. Medium-term

### Dynamic branch prediction
- Branch Target Buffer (BTB) and Two-Level Adaptive / Gshare predictor in the Fetch stage.
- Early branch recovery before ROB commit to reduce misprediction penalty.

### Non-blocking data cache (D-cache)
- L1 Data Cache with hit-under-miss capability and Miss Status Holding Registers (MSHRs).
- Integration with the existing TSO store buffer and store-to-load forwarding logic.

### Parameterized width polymorphism
- Abstract `XLEN` (32/64) and `FLEN` (32/64) into parameterized top-level CPU generators. The generators then emit both RV32G and RV64G from identical shared subcircuits.

### Compiler scheduling model (LLVM)
- **Tier 1**: Microarchitecture tuning flags for `clang` based on ROB/RS depths.
- **Tier 2**: `llvm-mca` pipeline scheduling model (see [docs/compiler-integration.md](compiler-integration.md)).
- **Tier 3**: Full TableGen scheduling model in LLVM RISC-V backend.

---

## 3. Long-term

### Privileged supervisor mode & virtual memory
- Privileged S-mode and U-mode execution.
- SV39/SV48 hardware page table walker and Translation Lookaside Buffer (TLB).
- Milestone: Booting Linux on the "formally verified" core.

### 2-wide superscalar execution
- 2-wide decode, renaming, and dispatch into reservation stations.
- Dual execution pipes and multi-port register file/ROB bypass.

### Vector extension (RV64GV / RVV 1.0)
- Configurable vector execution unit with VLEN=128/256 and SIMD arithmetic.

### Physical realization & FPGA
- FPGA target validation (Xilinx UltraScale+ / ECP5).
- Complete OpenROAD tapeout flow (RTL-to-GDSII) on ASAP7 and GF180MCU.

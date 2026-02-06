# LEC Failure Diagnosis and Fix Plan

## Context

`make lec` shows 36% coverage (34/92 modules verified). The goal is to fix the root causes and significantly increase LEC coverage. There are **5 distinct failure categories** affecting 58 modules.

## Failure Summary

| Category | Root Cause | Modules | Fix Location |
|----------|-----------|---------|-------------|
| A. Chisel "Cannot reassign" | Chisel codegen assigns to output ports driven by submodule | 4 (+cascading ~10) | `Chisel.lean` |
| B. firtool "sink not fully initialized" | Chisel codegen doesn't connect all submodule ports | ~11 | `Chisel.lean` |
| C. SV port name mismatch | Lean SV uses vectorized ports (`out[1:0]`), Chisel uses individual (`out_0`, `out_1`) | 14 | `SystemVerilog.lean` |
| D. SV compilation errors | Reserved keywords as wire names + invalid indexed port syntax `.port[idx]()` | 12 | `SystemVerilog.lean` |
| E. Sequential equiv failures | Structural mismatch between Lean/Chisel SV too large for induction | 9 | `CompositionalCerts.lean` |

Categories A+B produce "No Chisel output" (23 modules). Many cascade (e.g., IntegerExecUnit fails because ALU32 fails).

## Fix Plan (ordered by impact)

### Fix 1: Chisel codegen — "Cannot reassign to read-only" (Cat A)

**Root cause:** When a submodule output drives a circuit output, the codegen assigns to the output port AND connects the submodule — double-assignment.

**Affected:** ALU32, FetchStage, CPU_RV32I, CPU_RV32IM (+ IntegerExecUnit, MulDivExecUnit, LSU, etc. cascade)

**File:** `lean/Shoumei/Codegen/Chisel.lean`
**Fix:** When connecting a submodule output to a circuit output, don't generate a redundant `io.out := ...` if the submodule connection already drives it. Need to track which outputs are driven by submodule connections and skip direct assignments for those.

### Fix 2: Chisel codegen — "sink not fully initialized" (Cat B)

**Root cause:** Port mapping in hierarchical Chisel codegen doesn't connect all submodule input ports. The codegen misses connections when port names use indexed patterns that don't match the generated Chisel port structure.

**Affected:** Mux64x6, Mux64x32, Queue64_32, Queue64_6, Queue2_8, Queue4_8, QueueRAM_64x32, QueueRAM_64x6, RAT_32x6, FreeList_64, PhysRegFile_64x32

**File:** `lean/Shoumei/Codegen/Chisel.lean`
**Fix:** Fix bus port connection logic — when the DSL has `in7_0`, `in7_1`, etc. mapped to a submodule port `in7` that's a `UInt`, the codegen needs to concatenate individual wires into the bus connection: `u_sub.in7 := Cat(in7_5, in7_4, ..., in7_0)`.

### Fix 3: SV codegen — port name mismatch (Cat C)

**Root cause:** Lean SV codegen reconstructs buses from indexed wires (`out_0..out_N` → `output logic [N:0] out`) but Chisel/CIRCT emits individual ports (`output out_0, out_1, ...`). Yosys LEC can't match `\out` to `\out_0`.

**Affected:** Decoder1-6, RippleCarryAdder4/8/32/64, Subtractor4/8/32, CSACompressor64

**File:** `lean/Shoumei/Codegen/SystemVerilog.lean`
**Fix:** Change `generateSignalGroupPort` to emit individual ports instead of vectorized ports, matching CIRCT's output format. For signal groups, emit `output logic out_0, out_1, ...` instead of `output logic [1:0] out`.

### Fix 4: SV codegen — compilation errors (Cat D)

Two sub-bugs:

**4a. Reserved keywords as wire names**
- LogicUnit4/8/32 declare `logic and;`, `logic or;`, `logic xor;`
- Fix: Apply `sanitizeSVName()` to standalone wire declarations (line ~271 in `SystemVerilog.lean`)

**4b. Invalid indexed port connections**
- QueueRAM_2x8/4x8, Mux64x32, PipelinedMultiplier emit `.x[0](wire)` syntax
- Fix: Fix `groupPortMapEntries()` / `generateBusPortConnection()` to consolidate indexed port maps into proper concatenation syntax

**File:** `lean/Shoumei/Codegen/SystemVerilog.lean`

### Fix 5: Sequential equivalence — compositional certs (Cat E)

**Root cause:** QueueCounterUpDown and QueuePointer modules have structurally different Lean vs Chisel SV that exceeds Yosys induction capability.

**Affected:** QueueCounterUpDown_2/3/4/5/7, QueuePointer_2/3/4/6

**File:** `lean/Shoumei/Verification/CompositionalCerts.lean`
**Fix:** Add compositional certificates for these modules (they're already proven correct in Lean). This is the same approach used for Register91 and Register24.

## Implementation Order

1. **Fix 1 + Fix 2** (Chisel codegen) — unblocks 23 modules from "No Chisel output"
2. **Fix 4a** (reserved keywords) — quick fix, unblocks LogicUnit4/8/32
3. **Fix 3** (port name mismatch) — unblocks 14 modules
4. **Fix 4b** (indexed port syntax) — unblocks QueueRAM, PipelinedMultiplier, Mux64x32
5. **Fix 5** (compositional certs) — resolves 9 sequential modules

## Agent Swarm Recommendation

**Yes, this is a good candidate for a swarm.** The fixes are in 3 independent files:

| Agent | Focus | Files |
|-------|-------|-------|
| chisel-codegen | Fixes 1 + 2 | `lean/Shoumei/Codegen/Chisel.lean` |
| sv-codegen | Fixes 3 + 4a + 4b | `lean/Shoumei/Codegen/SystemVerilog.lean` |
| comp-certs | Fix 5 | `lean/Shoumei/Verification/CompositionalCerts.lean` |

All three can work in parallel since they modify different files.

## Verification

After all fixes:
```bash
lake build                        # Verify Lean compiles
lake exe generate_all             # Regenerate all outputs
cd chisel && sbt run && cd ..     # Verify Chisel compiles (target: 92/92)
make lec                          # Verify LEC (target: >90% coverage)
```

## Key Files

- `lean/Shoumei/Codegen/Chisel.lean` — Chisel code generator
- `lean/Shoumei/Codegen/SystemVerilog.lean` — SV code generator
- `lean/Shoumei/Codegen/Common.lean` — Shared codegen utilities (signal groups, clock/reset detection)
- `lean/Shoumei/Verification/CompositionalCerts.lean` — Compositional verification certificates
- `verification/run-lec.sh` — LEC script

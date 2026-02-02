# Compiler Integration

How to make LLVM generate good code for the Shoumei microarchitecture, iteratively from "works today" to "fully optimized."

## Background

LLVM already has a mature RISC-V backend. We don't need a new backend -- we need to tell the existing one what our pipeline looks like. LLVM uses this information for instruction scheduling, register allocation heuristics, and cost-based optimization decisions (inlining, unrolling, vectorization thresholds).

There are three tiers of integration, each building on the last:

| Tier | What | Effort | Requires LLVM rebuild? |
|------|------|--------|----------------------|
| 1 | Compiler wrapper with tuned flags | Hours | No |
| 2 | `llvm-mca` model for profiling | Days | No (uses existing infra) |
| 3 | Full TableGen scheduling model | Weeks | Yes (one-time RISC-V-only build) |

Start with Tier 1. It's useful immediately and the work feeds forward into the later tiers.

## Tier 1: Compiler Wrapper (no LLVM rebuild)

### What this does

Generates a `shoumei-clang` shell script that passes microarchitecture-aware flags to a stock `clang`. The flags control unrolling, inlining, and scheduling heuristics based on buffer sizes extracted from the Lean model.

### Where the numbers come from

| Parameter | Value | Source |
|-----------|-------|--------|
| ROB depth | 16 | `RISCV/Retirement/ROB.lean:87` — `entries : Fin 16` |
| RS entries | 4 | `RISCV/Execution/ReservationStation.lean` — `RSState 4` |
| Issue width | 1 | RS single-dispatch design |
| Physical registers | 64 | `RISCV/Renaming/PhysRegFile.lean` — `PhysRegFileState 64` |
| Architectural registers | 32 | `RISCV/Renaming/RAT.lean` — `Fin 32` |
| ALU latency | 1 cycle | `RISCV/Execution/IntegerExecUnit.lean` — combinational |
| Load latency | 2 cycles | `RISCV/Execution/MemoryExecUnit.lean` — AGU + mem access |

### The wrapper script

Generate `output/shoumei-clang` with contents:

```bash
#!/bin/bash
# Auto-generated from Shoumei Lean microarchitecture model
# Microarch: 1-wide OoO, ROB=16, RS=4, PRF=64, 1c ALU, 2c load
#
# Source of truth:
#   ROB depth:    ROB.lean (Fin 16)
#   RS entries:   ReservationStation.lean (RSState 4)
#   Issue width:  Single dispatch from RS4
#   PRF size:     PhysRegFile.lean (PhysRegFileState 64)

exec clang --target=riscv32 \
  -march=rv32i \
  -O2 \
  -mllvm -unroll-threshold=50 \
  -mllvm -unroll-count=2 \
  -mllvm -inline-threshold=225 \
  -mllvm -bonus-inst-threshold=2 \
  -mllvm -enable-loop-versioning-licm=false \
  "$@"
```

**Why these values:**

- **`-unroll-threshold=50`** (default 150): A 16-entry ROB with 4 RS entries can't keep a heavily unrolled loop in flight. Over-unrolling bloats code and wastes ROB capacity on loop overhead.
- **`-unroll-count=2`** (default varies): At most 2x unroll. More than that exceeds the useful OoO window.
- **`-inline-threshold=225`** (default 225): Default is fine. Inlining helps a narrow OoO machine by removing call/ret overhead that would eat ROB entries.
- **`-bonus-inst-threshold=2`**: Conservative speculation. With only 4 RS entries, speculative instructions compete for limited dispatch slots.

### Implementation

Add to `GenerateAll.lean` or create a standalone `GenerateCompilerFlags.lean`:

```lean
-- lean/Shoumei/Codegen/CompilerFlags.lean

def generateClangWrapper (robDepth rsEntries issueWidth : Nat)
    (loadLatency : Nat) : String :=
  let unrollThreshold := robDepth * 3  -- heuristic: 3x ROB depth
  let unrollCount := min 4 (rsEntries / 2 + 1)
  s!"#!/bin/bash
# Auto-generated from Shoumei microarchitecture model
# ROB={robDepth} RS={rsEntries} Issue={issueWidth} LoadLat={loadLatency}
exec clang --target=riscv32 \\
  -march=rv32i \\
  -O2 \\
  -mllvm -unroll-threshold={unrollThreshold} \\
  -mllvm -unroll-count={unrollCount} \\
  \"$@\""
```

This is intentionally simple. The point is that when you deepen the ROB to 32 or widen issue to 2, you re-run the generator and the thresholds update.

### Validation

Compare generated code quality:

```bash
# Stock clang
clang --target=riscv32 -march=rv32i -O2 -S bench.c -o bench.stock.s

# Shoumei-tuned
./output/shoumei-clang -S bench.c -o bench.tuned.s

# Compare: instruction count, loop structure, spill count
diff bench.stock.s bench.tuned.s
```

What to look for:
- Fewer loop unrolls (less ROB pressure)
- Loads hoisted above consumers (hide 2-cycle latency)
- Fewer register spills (64 physical regs is generous)

## Tier 2: llvm-mca Performance Model

### What this does

`llvm-mca` is LLVM's static pipeline simulator. It reads assembly, simulates scheduling on a modeled pipeline, and reports throughput/bottleneck analysis. It uses the same scheduling models as the compiler but can be driven without recompilation using a stock RISC-V generic model as a baseline.

### Usage with stock llvm-mca

```bash
# Compile to assembly
./output/shoumei-clang -S -o kernel.s kernel.c

# Analyze with generic RV32 model (built into llvm-mca)
llvm-mca -mcpu=generic-rv32 \
  -iterations=100 \
  -timeline \
  kernel.s
```

The output shows per-instruction resource usage, pipeline stalls, and bottleneck identification. With `generic-rv32` the latency numbers won't match your hardware, but the dependency analysis and structural hazard detection are still useful.

### Interpreting results for Shoumei

When reading `llvm-mca` output, mentally apply these corrections:

| llvm-mca assumption (generic) | Shoumei reality | Impact |
|-------------------------------|-----------------|--------|
| In-order pipeline | OoO with 4-entry RS | Independent ops can overlap |
| 1-cycle loads | 2-cycle loads | Load-use stalls underestimated |
| Large ROB | 16-entry ROB | Long dependency chains will stall |
| Wide issue | 1-wide issue | Back-to-back independent ops serialize |

This gives you a "good enough" profiling tool before investing in a custom model.

### Toward a custom llvm-mca model

`llvm-mca` models are the same TableGen `.td` files used by the compiler. Building a full model (Tier 3) automatically gives you accurate `llvm-mca` output. This is the main reason to eventually do Tier 3.

## Tier 3: Full TableGen Scheduling Model

### What this does

Adds a `RISCVSchedShoumei.td` file to LLVM's RISC-V backend. This gives the instruction scheduler, register allocator, and `llvm-mca` a complete picture of the Shoumei pipeline. Users compile with `-mcpu=shoumei`.

### The generated .td file

Every value traces back to a specific Lean source file:

```tablegen
// RISCVSchedShoumei.td
// AUTO-GENERATED from Shoumei-RTL Lean microarchitecture model

//===--------------------------------------------------------------===//
// Machine model
//===--------------------------------------------------------------===//

def ShoumeiModel : SchedMachineModel {
  let MicroOpBufferSize = 16;    // ROB.lean:87 — entries : Fin 16
  let IssueWidth = 1;            // RS4: single dispatch per cycle
  let LoadLatency = 2;           // MemoryExecUnit: 1c AGU + 1c mem
  let MispredictPenalty = 8;     // ROB flush estimate (tunable)
  let CompleteModel = 1;
}

//===--------------------------------------------------------------===//
// Execution units (from lean/Shoumei/RISCV/Execution/)
//===--------------------------------------------------------------===//

// IntegerExecUnit.lean: 1 ALU, combinational, 1-cycle
def ShoumeiUnitALU    : ProcResource<1>;

// MemoryExecUnit.lean: 1 AGU + memory port
def ShoumeiUnitMem    : ProcResource<1>;

// BranchExecUnit.lean: branch target resolution
def ShoumeiUnitBranch : ProcResource<1>;

//===--------------------------------------------------------------===//
// Write latencies (from IntegerExecUnit.opTypeToALUOpcode mapping)
//===--------------------------------------------------------------===//

// ALU opcodes 0-9: all single-cycle combinational
// Source: IntegerExecUnit.lean:55-73
def : WriteRes<WriteIALU,     [ShoumeiUnitALU]> { let Latency = 1; }
def : WriteRes<WriteIALU32,   [ShoumeiUnitALU]> { let Latency = 1; }
def : WriteRes<WriteShiftImm, [ShoumeiUnitALU]> { let Latency = 1; }
def : WriteRes<WriteShiftReg, [ShoumeiUnitALU]> { let Latency = 1; }

// Memory: 2-cycle (AGU + access)
// Source: MemoryExecUnit.lean — RippleCarryAdder32 for addr calc
def : WriteRes<WriteLDB, [ShoumeiUnitMem]> { let Latency = 2; }
def : WriteRes<WriteLDH, [ShoumeiUnitMem]> { let Latency = 2; }
def : WriteRes<WriteLDW, [ShoumeiUnitMem]> { let Latency = 2; }

// Stores: address calc only, no writeback result
def : WriteRes<WriteSTB, [ShoumeiUnitMem]> { let Latency = 1; }
def : WriteRes<WriteSTH, [ShoumeiUnitMem]> { let Latency = 1; }
def : WriteRes<WriteSTW, [ShoumeiUnitMem]> { let Latency = 1; }

// Branches/jumps
def : WriteRes<WriteJmp,  [ShoumeiUnitBranch]> { let Latency = 1; }
def : WriteRes<WriteJal,  [ShoumeiUnitBranch]> { let Latency = 1; }
def : WriteRes<WriteJalr, [ShoumeiUnitBranch]> { let Latency = 1; }

// M-extension (Phase 7+ — placeholder latencies)
// def : WriteRes<WriteIMul,  [ShoumeiUnitALU]> { let Latency = 3; }
// def : WriteRes<WriteIDiv,  [ShoumeiUnitALU]> { let Latency = 20; }

//===--------------------------------------------------------------===//
// Read advances (CDB forwarding)
// CDB broadcast is combinational — same-cycle snoop by RS entries
//===--------------------------------------------------------------===//

def : ReadAdvance<ReadIALU, 0>;
def : ReadAdvance<ReadJmp, 0>;
def : ReadAdvance<ReadMemBase, 0>;

//===--------------------------------------------------------------===//
// Instruction-to-resource mapping
// Source: ISA.lean:65-113 OpType enum
//        IntegerExecUnit.lean:55-73 opTypeToALUOpcode
//===--------------------------------------------------------------===//

let NumMicroOps = 1 in {
  // Arithmetic/logic → ALU (opcodes 0-6)
  def : InstRW<[WriteIALU], (instrs
    ADD, ADDI, SUB, AND, ANDI, OR, ORI, XOR, XORI,
    SLT, SLTI, SLTU, SLTIU,
    LUI, AUIPC
  )>;

  // Shifts → ALU (opcodes 7-9)
  def : InstRW<[WriteShiftImm], (instrs SLLI, SRLI, SRAI)>;
  def : InstRW<[WriteShiftReg], (instrs SLL, SRL, SRA)>;

  // Loads → Memory unit
  def : InstRW<[WriteLDW], (instrs LW)>;
  def : InstRW<[WriteLDH], (instrs LH, LHU)>;
  def : InstRW<[WriteLDB], (instrs LB, LBU)>;

  // Stores → Memory unit
  def : InstRW<[WriteSTW], (instrs SW)>;
  def : InstRW<[WriteSTH], (instrs SH)>;
  def : InstRW<[WriteSTB], (instrs SB)>;

  // Branches → Branch unit
  def : InstRW<[WriteJmp], (instrs
    BEQ, BNE, BLT, BGE, BLTU, BGEU, JAL, JALR
  )>;
}
```

### Mapping from Lean to TableGen

The instruction groupings come directly from `IntegerExecUnit.opTypeToALUOpcode`:

| Lean OpType | ALU opcode | LLVM WriteRes |
|-------------|-----------|---------------|
| ADD, ADDI | 0 | WriteIALU |
| SUB | 1 | WriteIALU |
| SLT, SLTI | 2 | WriteIALU |
| SLTU, SLTIU | 3 | WriteIALU |
| AND, ANDI | 4 | WriteIALU |
| OR, ORI | 5 | WriteIALU |
| XOR, XORI | 6 | WriteIALU |
| SLL, SLLI | 7 | WriteShiftImm/Reg |
| SRL, SRLI | 8 | WriteShiftImm/Reg |
| SRA, SRAI | 9 | WriteShiftImm/Reg |
| LB..LW | (memory unit) | WriteLDB/H/W |
| SB..SW | (memory unit) | WriteSTB/H/W |
| BEQ..BGEU, JAL, JALR | (branch unit) | WriteJmp |

### Building LLVM with the model

Only the RISC-V target is needed, which keeps build scope small:

```bash
git clone --depth 1 https://github.com/llvm/llvm-project.git
cp output/RISCVSchedShoumei.td llvm-project/llvm/lib/Target/RISCV/

# Patch includes (append to existing file)
echo 'include "RISCVSchedShoumei.td"' \
  >> llvm-project/llvm/lib/Target/RISCV/RISCVSchedModels.td

# Add processor definition to RISCVProcessors.td:
#   def : ProcessorModel<"shoumei", ShoumeiModel, [FeatureStdExtI]>;

cmake -G Ninja -S llvm-project/llvm -B build \
  -DLLVM_ENABLE_PROJECTS=clang \
  -DLLVM_TARGETS_TO_BUILD=RISCV \
  -DCMAKE_BUILD_TYPE=Release

ninja -C build clang llvm-mca
```

After this, both `clang -mcpu=shoumei` and `llvm-mca -mcpu=shoumei` use the model.

### Generator implementation

Add a Lean code generator alongside the existing three (SV, Chisel, SystemC):

```
lean/Shoumei/Codegen/
  SystemVerilog.lean   # existing
  Chisel.lean          # existing
  SystemC.lean         # existing
  LLVMSched.lean       # new — reads microarch, emits .td
```

The generator extracts parameters from the circuit definitions:

```lean
-- lean/Shoumei/Codegen/LLVMSched.lean

structure ExecUnitDesc where
  name : String
  count : Nat
  latency : Nat

structure MicroarchModel where
  robDepth : Nat
  rsEntries : Nat
  issueWidth : Nat
  physRegs : Nat
  execUnits : List ExecUnitDesc

-- Extract from existing circuit definitions
def shoumeiModel : MicroarchModel := {
  robDepth := 16       -- ROBState (Fin 16)
  rsEntries := 4       -- RSState 4
  issueWidth := 1      -- single dispatch
  physRegs := 64       -- PhysRegFileState 64
  execUnits := [
    { name := "ALU",    count := 1, latency := 1 },
    { name := "Mem",    count := 1, latency := 2 },
    { name := "Branch", count := 1, latency := 1 }
  ]
}

def generateTableGen (m : MicroarchModel) : String := ...
-- Output: output/RISCVSchedShoumei.td
```

Wire into `GenerateAll.lean` so `lake exe generate_all` produces the `.td` file alongside SV, Chisel, and SystemC.

## Iteration plan

### Now (Tier 1)

1. Write `CompilerFlags.lean` generator
2. Add to `generate_all` pipeline
3. Output `shoumei-clang` wrapper to `output/`
4. Validate: compile a few benchmarks, inspect assembly

### After Phase 7 (memory system)

5. Update load/store latencies once LSU and store buffer exist
6. Add store-forwarding latency if applicable
7. Build Tier 2: use `llvm-mca` with generic model to profile memory-heavy benchmarks

### After Phase 8 (integration)

8. Write `LLVMSched.lean` generator (Tier 3)
9. Generate `RISCVSchedShoumei.td`
10. One-time LLVM RISC-V build
11. Validate: `llvm-mca -mcpu=shoumei` predictions vs. RTL simulation IPC

### After Phase 9 (compliance)

12. Tune MispredictPenalty using branch benchmark results
13. Add M-extension latencies (multiply/divide) if implemented
14. Compare `llvm-mca` throughput predictions against simulated IPC on compliance benchmarks
15. Iterate: adjust latencies until model matches simulation within 10%

## What changes when the hardware changes

| Hardware change | What to update | Tier affected |
|-----------------|---------------|---------------|
| Deepen ROB (16 → 32) | `robDepth`, unroll threshold | 1, 3 |
| Widen issue (1 → 2) | `issueWidth`, all thresholds | 1, 3 |
| Add second ALU | `ProcResource<2>` | 3 |
| Add M-extension | Multiply/divide WriteRes entries | 3 |
| Add store buffer (Phase 7) | Store latency, forwarding | 1, 3 |
| Change cache latency | `LoadLatency` | 1, 3 |

If the generator reads these from the Lean model, re-running `lake exe generate_all` propagates changes automatically.

## Files

| File | Purpose |
|------|---------|
| `lean/Shoumei/Codegen/CompilerFlags.lean` | Tier 1: generates `shoumei-clang` wrapper |
| `lean/Shoumei/Codegen/LLVMSched.lean` | Tier 3: generates `RISCVSchedShoumei.td` |
| `output/shoumei-clang` | Generated wrapper script |
| `output/RISCVSchedShoumei.td` | Generated TableGen scheduling model |

## References

- [LLVM RISC-V scheduling models](https://github.com/llvm/llvm-project/tree/main/llvm/lib/Target/RISCV) — existing `.td` files to use as templates
- [LLVM Machine Code Analyzer](https://llvm.org/docs/CommandGuide/llvm-mca.html) — pipeline simulation tool
- [TableGen Programmer's Reference](https://llvm.org/docs/TableGen/ProgRef.html) — `.td` file syntax
- `RISCV/Execution/IntegerExecUnit.lean:55-73` — canonical opcode-to-unit mapping
- `RISCV/Retirement/ROB.lean:85-95` — ROB parameters
- `RISCV/Execution/ReservationStation.lean` — RS sizing and dispatch model

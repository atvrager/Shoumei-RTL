# Test Generation from Lean CPU Definition

Design document for generating RV32IM test binaries directly from the Lean microarchitectural models, using Spike as the ISA-level oracle.

## Motivation

Standard CPU verification approaches have a gap:

- **Random instruction generation** (riscv-dv) has no awareness of the microarchitecture. It may take millions of programs to reach corner cases like "ROB full + branch misprediction + store buffer forwarding in the same cycle."
- **Directed tests** are manually written, tedious, and incomplete.
- **Formal verification** (bounded model checking on RTL) is powerful but doesn't produce reusable regression binaries.

Shoumei has a unique advantage: the ISA semantics, the decoder, and the full microarchitectural behavioral models (reservation stations, ROB, rename stage, store buffer, dispatch routing) all live in the same Lean codebase. The models are executable and proven correct. Using them to guide test generation means tests can target specific pipeline states that are hard to reach randomly, and coverage is measured against the actual microarchitectural model.

## Architecture

```
  Lean (microarch models)              Spike (ISA oracle)
         |                                    |
   generates programs                  runs same ELF
         |                                    |
         v                                    v
      ELF binary ─────────────────► commit log (golden trace)
         |                                    |
         v                                    v
   RTL simulation ─────────────────► commit log (DUT trace)
   (Verilator / SystemC)                      |
                                              v
                                    diff ── mismatch = bug
```

**Lean** generates the programs and emits valid ELF binaries. **Spike** says what the correct answer is. **RTL** is the DUT. The Lean ISA semantics model is not trusted at runtime -- Spike is the single source of truth.

### Role of each component

| Component | Role |
|-----------|------|
| Lean microarch models | Guide test generation toward specific pipeline states |
| Lean encoder | Produce instruction words from `OpType` + operands |
| Lean ELF emitter | Package instructions into valid bare-metal ELF binaries |
| Spike | ISA-level golden reference (commit log = expected behavior) |
| RTL (Verilator/SystemC) | Design under test |
| Trace comparator | Align Spike and RTL commit logs, report first divergence |

### Why Spike and not the Lean semantics model?

Spike is the canonical RISC-V ISA reference simulator. Using it as the oracle means:

- Any divergence from Spike is a bug by definition (Spike defines correct behavior)
- No need to replicate sign extension, alignment, memory width semantics in Lean
- Spike handles edge cases (div-by-zero results, signed overflow, CSR behavior) that the Lean model may not cover
- Spike is already validated against the riscv-arch-test compliance suite
- Standard tooling (riscv-dv, riscof) already speaks Spike

The Lean `executeInstruction` model remains useful for fast pre-filtering during generation and for cross-checking that the Lean proofs are grounded in reality (see [Lean semantics cross-check](#lean-semantics-cross-check)).

## ELF Generation

All test binaries are emitted as ELF32. No flat binaries -- ELF provides metadata, symbols, section info, and compatibility with standard tooling (`objdump`, `gdb`, `readelf`).

### ELF structure

```
ELF32 Header (52 bytes)
  e_machine  = EM_RISCV (243)
  e_entry    = 0x80000000
  e_phoff    = 52

Program Header (.text LOAD)
  p_vaddr    = 0x80000000
  p_filesz   = code size
  p_flags    = PF_R | PF_X

Program Header (.data LOAD)
  p_vaddr    = 0x80002000
  p_filesz   = data size
  p_flags    = PF_R | PF_W

.text section
  _start:         bootstrap
  test_body:      generated test instructions
  test_end:       termination sequence

.data section
  .align 4
  tohost:    .word 0    # HTIF -- Spike watches this address
  fromhost:  .word 0

Section Headers + Symbol Table
  tohost, fromhost, _start, test_body, test_end
```

### Termination via HTIF

Spike uses the Host-Target Interface for program termination. The program writes to the `tohost` symbol to signal completion. Convention from riscv-tests:

- Write `1` to `tohost` = PASS
- Write `(test_num << 1) | 1` to `tohost` = FAIL at test_num

### Bootstrap preamble

Every generated ELF begins with a fixed preamble (~20 instructions):

```asm
_start:
    la    sp, _stack_top       # Set up stack pointer
    j     test_body

test_pass:
    li    a0, 1
    la    a1, tohost
    sw    a0, 0(a1)            # tohost = 1 -> PASS
1:  j     1b                   # Spin (Spike terminates on tohost write)

test_fail:
    slli  a0, a0, 1
    ori   a0, a0, 1
    la    a1, tohost
    sw    a0, 0(a1)            # tohost = (test_num << 1) | 1 -> FAIL
1:  j     1b
```

### Lean ELF emitter

```lean
structure ELF32 where
  entry     : UInt32                       -- e_entry
  text      : ByteArray                    -- .text contents
  data      : ByteArray                    -- .data contents
  textBase  : UInt32 := 0x80000000
  dataBase  : UInt32 := 0x80002000
  symbols   : List (String × UInt32)       -- symbol table

def ELF32.serialize (elf : ELF32) : ByteArray   -- emit valid ELF32 bytes
```

**Validation:** After emitting, run `riscv32-unknown-elf-objdump -d` on the ELF and verify the disassembly matches the intended instructions. This catches ELF encoding bugs immediately.

### File locations

| Component | Path |
|-----------|------|
| Instruction encoder | `lean/Shoumei/RISCV/Encoder.lean` |
| ELF emitter | `lean/Shoumei/TestGen/ELF.lean` |
| Bootstrap preamble | `lean/Shoumei/TestGen/Bootstrap.lean` |
| Test patterns | `lean/Shoumei/TestGen/Patterns.lean` |
| Coverage model | `lean/Shoumei/TestGen/Coverage.lean` |
| Generated ELFs | `tests/generated/*.elf` |

## Instruction Encoder

Inverse of `Decoder.lean`. Built from the existing `InstructionDef` with `matchBits`/`maskBits` and `variableFields`.

### Per-format encoding

```lean
namespace Shoumei.RISCV.Encoder

def encodeR (op : OpType) (rd rs1 rs2 : Fin 32) : UInt32
def encodeI (op : OpType) (rd rs1 : Fin 32) (imm : BitVec 12) : UInt32
def encodeS (op : OpType) (rs1 rs2 : Fin 32) (imm : BitVec 12) : UInt32
def encodeB (op : OpType) (rs1 rs2 : Fin 32) (imm : BitVec 13) : UInt32
def encodeU (op : OpType) (rd : Fin 32) (imm : BitVec 20) : UInt32
def encodeJ (op : OpType) (rd : Fin 32) (imm : BitVec 21) : UInt32

-- Unified interface
def encode (op : OpType) (rd rs1 rs2 : Fin 32) (imm : Int) : UInt32
```

### Round-trip proof

The encoder's correctness is provable: encoding an instruction and then decoding it must yield the original fields.

```lean
theorem decode_encode_R (op rd rs1 rs2) :
    decode (encodeR op rd rs1 rs2) = some { opType := op, rd, rs1, rs2, imm := 0 }

-- Unified round-trip:
theorem decode_encode_roundtrip (instr : DecodedInstruction) :
    decode (encode instr) = some instr
```

This is verified with `native_decide` for concrete instruction types. If the encoder is wrong, every generated test is suspect. The proof eliminates that risk.

## Test Pattern Library

Test patterns are defined as a Lean inductive type. Each pattern has a `generate` function that emits instruction words and a `coverage` function that predicts which microarchitectural coverage points the pattern exercises.

```lean
inductive TestPattern where
  | smoke                                              -- one of each instruction
  | rawChain (distance : Nat) (ops : List OpType)     -- read-after-write forwarding
  | wawChain (length : Nat)                            -- write-after-write rename stress
  | rsExhaustion (unit : ExecUnit) (depth : Nat)       -- fill reservation station
  | robFill (depth : Nat)                              -- fill reorder buffer
  | branchMispredict (branchOp : OpType) (specDepth : Nat)
  | storeForward (storeW loadW : Nat) (addrOffset : Int)
  | freeListExhaustion                                 -- burn through physical registers
  | dividerOccupancy (backToBack : Nat)                -- N back-to-back DIVs
  | comboHazard (hazards : List TestPattern)           -- multiple simultaneous hazards
  | custom (instrs : List UInt32)                      -- manually specified

def TestPattern.generate : TestPattern → List UInt32
def TestPattern.expectedCoverage : TestPattern → List CoveragePoint
```

See [Hazard Pattern Catalog](hazard-patterns.md) for detailed descriptions of each pattern.

## Coverage Model

Coverage is measured against the Lean microarchitectural model, not just instruction-level metrics.

```lean
inductive CoveragePoint where
  -- Pipeline structural hazards
  | rsFullStall (unit : ExecUnit)
  | robFullStall
  | freeListEmpty
  -- Data forwarding paths
  | cdbForwardToRS
  | cdbWakesBothOperands
  | storeBufferForwardHit
  | storeBufferForwardWidthMismatch
  | prfReadAfterCDBWrite
  -- Control flow
  | branchFlushWithPendingStores
  | branchFlushROBNonEmpty (entries : Nat)
  | branchFlushDuringCDBBroadcast
  -- Execution unit occupancy
  | dividerBusy32Cycles
  | allExecUnitsBusy
  | multiplierPipelineFull
  -- Retirement
  | robCommitDeallocatesPhysReg
  | exceptionAtCommit
  deriving BEq, Hashable
```

### Coverage-guided generation loop

```lean
def coverageLoop (maxIters : Nat) : IO (List TestProgram) := do
  let mut covered : HashSet CoveragePoint := {}
  let mut tests : List TestProgram := []
  for _ in List.range maxIters do
    let uncovered := allCoveragePoints.filter (! covered.contains ·)
    if uncovered.isEmpty then break
    let target := uncovered.head!
    let program ← synthesizeForTarget target
    let microSim ← simulateMicroarch program
    covered := covered ∪ microSim.hitPoints
    tests := tests ++ [program]
  return tests
```

Coverage is measured against the Lean microarchitectural model. Correctness is checked by Spike. These are separate concerns.

## Lean Semantics Cross-Check

As a secondary benefit, the same ELFs can validate the Lean `executeInstruction` model against Spike:

```lean
def crosscheck (elf : ELF32) (spikeTrace : List TraceEntry) : IO Unit := do
  let mut state := ArchState.init elf.entry
  for expected in spikeTrace do
    let (state', result) := executeStep state
    if result.rd_value != expected.rd_value then
      throw s!"Lean/Spike divergence at PC={state.pc}: lean={result.rd_value} spike={expected.rd_value}"
    state := state'
  IO.println "Lean semantics matches Spike"
```

This is not part of the RTL verification flow. It validates that the Lean proofs are grounded in reality. Any divergence means the Lean semantics model has a bug, which matters for the formal proofs even though Spike is the runtime oracle.

## Implementation Phases

| Phase | Deliverable | Dependencies |
|-------|-------------|--------------|
| A: Encoder | `Encoder.lean` with round-trip proofs | Existing `Decoder.lean`, `ISA.lean` |
| B: ELF emitter | `ELF.lean` + `Bootstrap.lean`, `lake exe emit_test` | Phase A |
| C: Spike harness | `scripts/run_spike.sh`, trace parser | Spike installed |
| D: Hazard patterns | `Patterns.lean` with all pattern types | Phase B |
| E: RTL trace extraction | Commit log output from SystemC/Verilator testbench | Phase 8 integration |
| F: Trace comparison | `scripts/compare_traces.py`, CI integration | Phases C + E |
| G: Coverage model | `Coverage.lean` + microarch simulator | Existing behavioral models |
| H: Coverage-guided fuzzer | Generation loop with coverage feedback | Phases D + G |

Phases A-D can proceed before the CPU is integrated (Phase 8). The generated ELFs are validated by Spike and stockpiled for when RTL simulation becomes available.

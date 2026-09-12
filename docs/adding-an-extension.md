# Adding an ISA Extension

Companion to [adding-a-module.md](adding-a-module.md). That document covers one
module; this one covers an **instruction-set extension** — new opcodes that must
be decoded, classified, executed, and verified end-to-end. Derived from adding
the A (atomics) extension (`LR.W`/`SC.W`/`AMO*.W`) to reach `RV32IMA`.

## Checklist

| # | Step | Where |
|---|------|-------|
| 1 | Add encodings | `third_party/riscv-opcodes/extensions/rv_<x>` → `instr_dict.json` |
| 2 | New encoding fields (if any) | `lean/Shoumei/RISCV/ISA.lean` (`FieldType`) |
| 3 | Extension group | `GenerateOpType.lean` (`extGroups`) → `lake exe generate_optype` |
| 4 | Config flag | `lean/Shoumei/RISCV/Config.lean` |
| 5 | Decoder classification | `lean/Shoumei/RISCV/Codegen{SystemVerilog,CppSim}.lean` |
| 6 | Dispatch routing | `lean/Shoumei/RISCV/Execution/Dispatch.lean` |
| 7 | Execution / pipeline | `lean/Shoumei/RISCV/CPU.lean` (+ `CPUHelpers.lean`) |
| 8 | Spec semantics | `lean/Shoumei/RISCV/Semantics.lean` |
| 9 | Decode proofs | `lean/Shoumei/RISCV/DecoderProofs.lean` |
| 10 | Codegen + testbench | `GenerateAll.lean`, `testbench/Makefile` |
| 11 | Verify | sim + Spike cosim + slang |

## 1. Encodings

**Never hand-write encodings.** The canonical source is the bundled
`riscv-opcodes` checkout. Add/extend `third_party/riscv-opcodes/extensions/rv_<x>`
and regenerate:

```sh
cd third_party/riscv-opcodes
PYTHONPATH=src python3 -m riscv_opcodes -c rv_i rv32_i rv_m rv_a rv_f \
    rv_zicsr rv_zifencei rv_system
```

This rewrites `instr_dict.json` (sorted) and `encoding.out.h`. Verify the result
is a *superset* of the previous JSON before committing:

```sh
git stash; python3 -c "import json;print(len(json.load(open('instr_dict.json'))))"
```

`instr_dict.json` drives **everything** downstream: `OpType`, the generated
decoders, and `config.opcodeIndex`.

> **Trap — funct3 from the spec.** The ISA manual describes AMO `funct3` as
> `000`; riscv-opcodes (and the assembler) encode `010`. Always trust
> `extensions/` + a round-trip through `riscv32-unknown-elf-as`, never the prose.

## 2. New encoding fields

If the JSON `variable_fields` names a field `FieldType` does not know (e.g. the
A extension's `aq`/`rl`), `parseInstructionDef` throws and the instruction is
**silently skipped** — the opcode simply never appears. Add the constructor to
`FieldType`, its `toString`, and its `fromString` in `ISA.lean`. Fields that are
not extracted (hints) need no decoder support.

## 3. OpType

Add an extension group to `extGroups` in `GenerateOpType.lean`:

```lean
{ comment := "A Extension: Atomic Memory Operations", exts := ["rv_a"] },
```

then `lake exe generate_optype`. This regenerates `OpTypeGenerated.lean`
(constructors, `all`, `toIndex`/`ofIndex`, `extensionGroup`, `isFpGroup`).

Adding constructors makes every exhaustive `match` on `OpType` fail — that is
the compiler finding your worklist. Expect hits in `IntegerExecUnit`,
`Dispatch`, `TestGen/AsmEmitter`, `Semantics`, and the FP/format helpers.

## 4. Config

In `Config.lean` add `enable<X>` to `CPUConfig`, extend `enabledExtensions`,
`isaString`, and `spikeIsa`, and add a preset (`rv32imaConfig`, `rv32gConfig`).
`decoderInstrNames` / `opcodeIndex` derive from `OpType.all` — no table to edit.

## 5. Decoder classification

The generated decoder emits `io_is_integer/memory/branch/store`, `io_use_imm`,
`io_has_rd`, and (for FP) the FP signals, all keyed on **opcode bits**. Add your
major opcode to the right class in the generators
(`CodegenSystemVerilog.lean`, `CodegenCppSim.lean`) behind
a `has<X> defs` guard. Add a dedicated signal when the class is not enough (the
A extension added `io_is_atomic` so the RS can order atomics).

### The opcode-space trap (read this)

Reservation-station entries store opcodes in `opcodeWidth` bits. Two decoders
must agree:

* the generated decoder enum (from `instr_dict.json` order, reverse-alpha via
  the parser's prepending fold), and
* `CPUConfig.opcodeIndex` (from `OpType.all` reverse-alpha).

They agree by construction — verify with:

```lean
#eval defaultCPUConfig.opcodeIndex OpType.LW
```

and compare against the position in the generated `typedef enum`. If they
diverge, every opcode match silently points at the wrong instruction.

**When the enabled instruction count exceeds the field width, widen it.** With
A enabled the integer group exceeds 64, so a 6-bit RS opcode aliases `ADD` with
`XORI` and `SC` with `FLW`. Widening touches:

* `Execution/ReservationStation.lean` — `opcodeWidth`, `entryWidth`
  (`Register{entryWidth}`), and `GenerateAll.lean` (`mkRegisterNHierarchical`).
* `CPU.lean` — every `makeIndexedWires "…opcode" W`, **and the loop ranges of the
  opcode muxes** (`(List.range W).map …`). A mux left at the old width leaves the
  top bit undriven: opcodes ≥ 2^(W-1) decode as 0. This is the single most
  expensive bug class here — grep `d0_op.take` next to `List.range`.
* `mkOpcodeMatch6` → `mkOpcodeMatch7` for the now-wider domains.

## 6. Dispatch

`classifyToUnit` in `Dispatch.lean` maps each new `OpType` to its unit, gated by
the config flag so the op is `Illegal` when disabled (matches the decoder, which
omits it).

## 7. Execution

For in-pipeline units (ALU, MulDiv, FP) extend the exec unit and its opcode LUT
(`CPUCircuitHelpers.lean`). For memory-resident work, the pattern is:

1. Decode the op from the RS opcode (`mkOpcodeMatch7`; OR a set with
   `mkOpcodeMatchAny7`), and any sub-op via `mkOpTypeLUT`.
2. Register what the memory stage needs (`mkMemPipeline` for address/tag, or
   bespoke DFFs for extra fields).
3. Gate dispatch, execute, and broadcast on the CDB.

**Atomics specifically** (see `mkAtomicUnit` in `CPUHelpers.lean`):

* A single-hart reservation register `(valid, addr)`; `lr.w` sets it on its read
  response, `sc.w` checks+clears it, and any intervening store to the reserved
  word (snooped on store-buffer dequeue) clears it.
* An AMO is a read-modify-write that reuses the one-slot memory pipeline: the
  read goes through the normal load path, the new value is written directly to
  DMEM. While it is in flight, **block all memory dispatch** so no younger
  access can slip between read and write.
* RMW ops wait for a drained store buffer *and* no pending plain store in the
  memory RS (an older store may not have reached the SB yet). Expose
  `pending_store` from the RS for this.
* Atomics take part in store-load ordering: mark them `issue_is_store` so
  younger loads cannot bypass them, but keep them out of plain-store arbitration
  so an LR/SC pair dispatches in program order (otherwise the SC can execute
  before its LR and fail spuriously).

> **Trap — spurious failures break cosim.** The spec permits `sc.w` to fail
> spuriously, but a lock-step comparison against Spike treats any failure Spike
> did not take as a mismatch. Do not clear the reservation on pipeline flush,
> and order LR→SC in program order.

## 8-9. Semantics and proofs

Add the spec behaviour to `Semantics.lean` (extend `ArchState`, add the
execution case). In `DecoderProofs.lean` prove non-overlap and decode coverage
over the new patterns with a concrete definition list (`native_decide`).

## 10. Codegen and testbench

`GenerateAll.lean` regenerates decoders from `instr_dict.json` automatically.
The top-module name and `SPIKE_ISA` in `output/config.mk` change with the config
— update `ARC_TOP_MODULE` in `testbench/Makefile` and any hardcoded name.

Add test targets mirroring the existing suites (`rv32ua-p-%.elf`, `-march` flag,
glob, timeout for long-running atomic loops).

## 11. Verify

```sh
make codegen
make -C testbench sim && make -C testbench run-all-tests
make -C testbench cosim && make -C testbench run-cosim   # RTL vs Spike
python3 verification/slang-lint.py output/sv-from-lean
```

The cosim is the north star: retired PC/insn/rd-data must match Spike
instruction-for-instruction, including the new extension's tests.

## Build-system notes

* **Generated outputs are version-blind.** The incremental cache is keyed on a
  circuit hash; a change to the *generators* does not change the hash. Bump
  `codegenVersion` in `Codegen/Unified.lean` when emitted text changes.
* **Stale outputs linger.** Renamed/removed modules leave files behind that
  break elaboration. `pruneStaleOutputs` removes them (and their cache entry) at
  the end of `generate_all`.

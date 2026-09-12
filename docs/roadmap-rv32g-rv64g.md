# Roadmap: two ISA configurations (RV32G, RV64G)

**Status:** draft for review. High level by design — sequencing, milestones, exit
criteria and risks. Detailed design lives in
[rv32g-d-extension-plan.md](rv32g-d-extension-plan.md) once each phase starts.

## Target state

Two supported configurations, and only two:

- **RV32G** — `RV32IMAFD_Zicsr_Zifencei`
- **RV64G** — `RV64IMAFD_Zicsr_Zifencei`

Both fully verified to the project's standing bar: simulation, Spike
lock-step cosimulation, and logical equivalence checking between the two
generated RTL artifacts.

## Current state

`RV32IMAF_Zicsr_Zifencei`. Verified end to end: 111/111 Verilator tests and
111/111 Spike cosim tests, including the ten atomics suites.

The distance to the target:

| | RV32G | RV64G |
| :--- | :--- | :--- |
| Double-precision FP | missing | missing |
| 64-bit FP registers | missing | missing |
| 64-bit load/store data path | missing | missing |
| 64-bit integer datapath | not needed | missing |
| 64-bit addresses and CSRs | not needed | missing |
| RV64-only instructions (17) | not needed | missing |
| Config as a first-class choice | `xlen` is currently a dead field | same |

## Strategy

**Double-precision first, XLEN second.** The D extension forces the 64-bit FP
register file, NaN-boxing, the 64-bit FP result path, the 64-bit FP memory data
path and the double-precision arithmetic units — all of which RV64G requires
anyway. Doing D on the 32-bit integer core is the same work in a smaller, better
understood setting, and it ships a milestone on its own.

RV64G then reduces to a single question — **parameterise the core by XLEN, or
fork it** — plus the propagation of that decision. Deciding it early would be a
guess; deciding it after D is informed, because nothing about D constrains it.

## Phases

### Phase 0 — Foundation (unblock, then leave it alone)

Nothing below is glamorous and all of it is cheaper now than later.

| Item | Why now |
| :--- | :--- |
| Fix the FP-store race | `fsw` intermittently enqueues a zero operand. Every `FLD`/`FSD` test would inherit exactly this flakiness |
| Land `Circuit ⊨ Behavior` refinement atoms + the composition lemma | D and XLEN each multiply the module count; the verification ladder must compose, not grow a single long-running proof |
| Make verification scale | the LEC long pole is already the CPU top-level; it must not become the wall |
| Resolve the Chisel question | either replace it with a netlist-level comparison or keep paying for it — do not carry the decision into two ISA ports |

**Exit:** FP memory tests are trustworthy; a full verification run is bounded by
many small checks rather than one large one.

### Phase 1 — RV32G (add D)

Five workstreams, roughly in dependency order but overlapping:

1. **Decode and configuration** — the D instructions, `fmt=01`, the `enableD`
   flag, the `RV32G` preset, module naming. Small, and it unblocks test authoring.
2. **Registers and transport** — 64-bit FP register file; a 64-bit FP result
   path (the current FP bus is only a buffered copy of the shared 32-bit one).
3. **Memory** — 64-bit load/store data through the store buffer, the data cache
   and the CPU memory interface; `FLD`/`FSD`.
4. **Datapath** — double-precision add, multiply, fused multiply-add, divide,
   square root, plus the conversion and comparison family.
5. **Verification** — `rv32ud-p-*` suites in simulation and cosim, plus a test
   dedicated to NaN-boxing.

**Exit:** all `rv32ud-p-*` suites pass in simulation *and* lock-step cosim;
`RV32G` is a selectable configuration with no regressions in `IMAF`.

### Phase 2 — RV64G

1. **Design decision** — parameterise by XLEN, or fork the core. This is the
   single most consequential architectural call in the programme and gets its own
   design review before code.
2. **Integer widening** — registers, ALU, adders, comparators, shifters, PC,
   immediates, CSRs, addresses.
3. **RV64 instructions** — the 17 new integer/multiply ops and the 64-bit FP
   conversions and moves.
4. **Memory and interfaces** — 64-bit addresses through the cache tags, the
   store buffer and the CPU interface; testbench memory model and CLINT.
5. **Toolchain** — RV64 test suites, `-march`, Spike ISA string, linker script,
   physical wrappers, module naming.

**Exit:** `rv64g-p-*` suites pass in simulation and cosim; both configurations
build from one code path (or one clearly-owned pair of paths).

## Sequencing

```mermaid
graph LR
  P0[Phase 0: foundation] --> P1A[Decode + config]
  P1A --> P1B[FP registers + bus]
  P1B --> P1C[64-bit memory path]
  P1C --> P1D[DP datapath]
  P1D --> P1V[RV32G verification]
  P1V --> P2A[XLEN design decision]
  P2A --> P2B[Integer widening]
  P2B --> P2C[RV64 instructions]
  P2C --> P2V[RV64G verification]
```

Memory and datapath can proceed in parallel once the registers and bus are
settled; verification workstreams start as soon as there is anything to run.

## Risks

| Risk | Impact | Mitigation |
| :--- | :--- | :--- |
| Double-precision arithmetic is large | codegen and verification times grow with gate count | build DP units alongside SP, share unpack/pack/rounding; watch compile times as a first-class metric |
| NaN-boxing is silent | wrong FP results with no structural signature | dedicated test; enforce at one place (the FP write path) and check at one place (the read path) |
| The FP-store race | undermines every FP memory test | fixed in Phase 0, before any D memory work |
| Forking for XLEN | two cores diverging, every future feature done twice | treat "parameterise" as the default and require evidence to fork |
| Verification wall | a full run becomes too slow to gate commits | Phase 0's composition work; keep the commit gate as a fast tier and move heavyweight sweeps off the critical path |
| Carrying the Chisel decision | paying the cost twice across two ports | resolve in Phase 0 |

## Effort framing

Relative, not dated:

- **Phase 0** — small, high leverage, unblocks everything.
- **Phase 1 (RV32G)** — one large feature. Comparable to the F extension, with
  the double-precision arithmetic as the dominant item.
- **Phase 2 (RV64G)** — the largest single effort in the programme, dominated by
  propagation rather than novelty. Partly de-risked by Phase 1: the 64-bit FP
  side and the 64-bit memory data path are already done.

## Non-goals

- No third ISA configuration; no 32-bit-only FP variants once both targets exist.
- No new extensions beyond IMAFD + Zicsr + Zifencei.
- No optimisation work (pipeline depth, IPC, cache tuning) inside these phases.

## Success metrics

1. Two configurations, one code path (or one owned pair), no third variant.
2. `RV32G` and `RV64G` both green on simulation, cosim and LEC.
3. Commit-gate verification time stays flat as the module count grows.
4. Every module carries its own small proof; no single long-running check.

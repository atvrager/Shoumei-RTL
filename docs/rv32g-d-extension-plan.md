# RV32G Plan: the D extension, and what is left open

Working document.  Records the state after the A extension landed, the measured
shape of the D work, and the decisions still open.  See
[adding-an-extension.md](adding-an-extension.md) for the mechanics of adding an
extension and [verification-guide.md](verification-guide.md) for the
verification architecture.

## Where we are

`RV32IMAF_Zicsr_Zifencei`, fully verified: 111/111 Verilator tests and 111/111
Spike lock-step cosim tests, including the ten `rv32ua-p-*` atomics suites
(PR #95).

`RV32G` is `RV32IMAFD_Zicsr_Zifencei`.  The gap is exactly the **D extension**.

## D is a datapath widening project, not an opcode project

Measured widths in the current tree:

| Path | Today | D needs |
| :--- | :--- | :--- |
| `PhysRegFileState.regs` (reused for `fpPhysRegFile`) | `Fin n -> UInt32` | 64-bit FP register file |
| `cdb_data` / `cdb_data_fp` | 32-bit; `cdb_data_fp` is a **buffered copy of the same bus**, not an independent one | 64-bit FP result path |
| `StoreBufferEntry.data`, `QueueRAM_8x66` | 32-bit data | `FLD`/`FSD` 8-byte payload (66 -> 98 bits) |
| `dmem_req_data` / `dmem_resp_data` | 32-bit | 64-bit |
| `L1DCache.resp_data` | 32-bit | 64-bit (the 256-bit line already holds it) |
| `FPAdder` / `FPMultiplier` / `FPFMA` / `FPDivider` / `FPSqrt` | single precision | 53-bit significand, 11-bit exponent |
| decoder `fmt` / load-store width | `fmt=00` (S), widths up to word | `fmt=01` (D), width `011` |

Decode and config (`rv_d` in riscv-opcodes, `enableD`, `isaString`/`spikeIsa`,
`rv32ud-p-*` targets) is the small part.  Everything else is widening.

### NaN-boxing is mandatory

Once FP registers are 64-bit, single-precision values must be NaN-boxed:
`FLW` writes `{32'hFFFFFFFF, word}`; `FSW` reads only the low 32 bits; every
single-precision result is boxed; an unboxed operand reads as the canonical NaN.
This is the classic silent F-in-D trap -- it corrupts FP results without any
structural change, so it needs its own test.

## Should RV64 come first?  No -- do D first

The FP-side work is a strict prerequisite for both: a 64-bit FP register file,
NaN-boxing, a 64-bit FP result path, 64-bit FP load/store data, and the
double-precision units are all *mandated by the base ISA* on RV64, so they must
exist there too.

What differs is the blast radius:

| | RV32D first | RV64 first |
| :--- | :--- | :--- |
| FP regfile / NaN-boxing / DP units | done once | done once |
| 64-bit load/store data path | done (`FSD`) | done (`LD`/`SD` too) |
| Integer datapath | **untouched** | every adder, comparator, shifter, PC, ROB/RAT/free-list width, RVVI interface |
| Currently verified RTL | intact | largely invalidated |
| Existing test suites | still meaningful | all need re-derivation |

RV64-first re-verifies the 32-bit integer datapath and *then* still does all the
FP work, while turning the F path into a NaN-boxed rewrite rather than an
extension.  D-first is incremental, keeps what is green meaningful, and
front-loads the memory widening both need.

## Width discipline (binding on this phase)

XLEN is a parameter, not a fork (see
[roadmap-rv32g-rv64g.md](roadmap-rv32g-rv64g.md)).  The D work is therefore done
in a width-parameterised style so RV64G inherits it unchanged:

- Introduce the FP register width as a parameter (FLEN = 64) rather than writing
  literal 64s, exactly as the circuit library already parameterises
  `mkSubtractorN`, `mkRegisterN`, `mkMuxTree`, `mkComparatorN`.
- Add **no new hard-coded data widths** to the RTL composition.  The 91 existing
  hard-wired 32-bit data buses are the RV64G workstream; do not add to them.
- Keep the widening of the FP result path, the store-buffer payload and the
  load/store data independent of XLEN, so the same change serves both
  configurations.

Rationale: this phase creates the first 64-bit data paths in the design.  If they
are written parameterised, RV64G is propagation; if they are written with
literals, RV64G is a second implementation of everything this phase touches.

## Decisions still open


1. **FP result bus.**  `cdb_data_fp` is a buffered copy of the shared 32-bit
   `cdb_data`, so "widen FP" touches INT unless FP gets a genuinely separate
   64-bit bus.  Recommendation: give FP its own 64-bit result bus -- FP already
   has its own mux and domain bit, so INT stays 32-bit.
2. **D memory path.**  `FSD` cannot be two 32-bit stores without breaking
   load/store ordering.  Recommendation: widen the store-buffer payload and the
   L1D response to 64 bits.  This is the largest single change and it lands on
   the subsystem that was just stabilized.
3. **DP arithmetic.**  The existing units are hand-built gate-level single
   precision; parameterising them is a rewrite.  Recommendation: new DP units,
   sharing only unpack/pack/rounding scaffolding.
4. **Ordering.**  Fix the pre-existing FP-store race first (see below) so D
   memory tests are trustworthy.
5. **Verification investment.**  Land the `Circuit satisfies Behavior`
   refinement atom and the generic composition lemma *before* D.  D multiplies
   both the datapath and the module count, and the current LEC long pole (the
   CPU top-level, which has no compositional certificate and so gets flattened
   SEC) only gets worse.

## Other threads left open

- **LEC long pole.**  The CPU top-level escalation dominates a full LEC run.  The
  scoped reads, content-addressed cache and structural fast pass improved
  everything around it.  Closing it means either a compositional certificate for
  the CPU or a tree/congruence comparison instead of flattened SEC.
- **Replacing the Chisel cross-check.**  The intended replacement -- a second
  lowering -- cannot be a fully inlined flat netlist: inlining the whole
  hierarchy produced an **8.7 MB** netlist for `PhysRegFile_64x32` (up from
  ~260 KB) and would produce hundreds of megabytes for the CPU.  Compare
  hierarchies as trees instead; see *Work at the netlist level* in
  verification-guide.md.
- **Pre-existing FP-store race.**  `fsw` sometimes enqueues `src2 = 0` into the
  store buffer: timing-dependent and value-independent (the same value passes or
  fails purely on instruction spacing).  Minimal reproducer and the excluded
  `fp_memory` test are in `testbench/tests/generated/`.  It lives in the FP
  rename / busy-table path.
- **`SemanticsTest.lean`** is pre-existing mangled (stray parens,
  `decodeInstruction` arity) and is not part of the build or CI.

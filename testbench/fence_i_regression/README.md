# Zifencei serialization regressions

Three distinct gaps in the `fence.i` / serialize path, found while bringing up
the benchmark suite.  `fence.i` is excluded from the benchmark suite itself
(`BENCH_SKIP` in `lean/Shoumei/RISCV/BenchmarkSpecs.lean`) because the drain
does not increment `minstret`, so a minstret-derived CPI is meaningless for it;
the RTL defect below is fixed.

## 1. Self-modifying code (OPEN)

`fence_i_test.c` reproduces a real gap: a fetched 32B line containing freshly
stored code is not refreshed after `fence.i`.  The cached CPU ties the L1I
`fence_i` invalidate input to zero ("FENCE.I not yet implemented in W=2",
`lean/Shoumei/RISCV/Memory/Cache/CachedCPU.lean`).  The `MemoryHierarchy`
`fence_i` port and the L1I invalidate + `fence_i_busy` handshake exist; only the
CPU -> hierarchy wiring (drive `fence_i` from the serialize start and gate the
drain on `fence_i_busy`) is missing.  Kept OUT of the buildable
`testbench/tests` list (and cppcheck scope) until that lands; run manually:

    make -C testbench/tests fence_i_test.elf   # after moving back

## 2. Stale L1I line decodes during refill (FIXED)

On an L1I miss the cache presents the stale contents of the refilling set
(on the bench: leftover `fence.i` byte patterns) while the fetch stage
holds its PC.  The ungated `fi_selected` start path decoded that stale
word as a real `fence.i` and fired a phantom drain, dropping in-flight
instructions (observed: `.Lfail`'s `lui` never retired, `addiw` ran with a
reset register).  Fixed in `CPU.lean`:

- the serialize start (`fi_selected`) uses the valid-gated
  `fi_det_{0,1}_gated` matches, and
- decode-valid is masked while `fetch_stall_ext` (L1I refill) is high, so
  a stale line can never decode, serialize, or trap mid-refill.

## 3. Slot-0 predecessor of a slot-1 serialize (FIXED)

A serialize-class instruction (fence.i / WFI) decoded in slot 1 used to
suppress *both* slots at the drain start (`fi_start_nocsr`) and redirect to the
serializing instruction's PC+4.  Its slot-0 block-mate - a program-order
predecessor that had not executed yet - was therefore never fetched again and
was dropped silently.  On the bench that showed up as a loop counter that never
decremented, i.e. a hang.

Fixed in `CPU.lean` by *deferring* the serialize one cycle instead of
dispatching into the live drain:

- when slot 1 holds a fence.i/WFI whose slot-0 block-mate is a dispatchable
  non-serialize instruction, the fetch stage is forced to half-step
  (`ser_s1_defer` is OR'd into `any_dual_stall`), which masks slot 1 and
  advances the fetch PC by 4;
- the predecessor then dispatches alone, and the serialize is re-presented in
  slot 0 on the next cycle, where the drain takes its well-tested
  slot-0-selected path.

Only fence.i and WFI need the defer: CSR and the trap-class ops
(ECALL/MRET/illegal) already let slot 0 dispatch, and for those the trap must
keep `mepc` on the serializing instruction - deferring them would move `mepc`
onto a predecessor that has already retired.  Interrupt injection is excluded
for the same reason (slot 0 retires before the sequencer redirects).

Regression test: `testbench/tests/serialize_pair_test.S` (in the default
`run-all-tests` / `run-cosim` suites).  It pairs each `fence.i` with a
dependent slot-0 predecessor in a loop that re-enters at the pair, so both the
counter and a data-carrying predecessor must have executed: pre-fix the test
hangs (never writes `tohost`), post-fix it passes in ~480 cycles.
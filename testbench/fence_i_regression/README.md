# Zifencei serialization regressions

Three distinct `fence.i` / serialize-path defects found while bringing up the
benchmark suite, all now fixed.  Kept as a record of what was wrong and why the
fix looks the way it does.

`fence.i` remains in `BENCH_SKIP` (`lean/Shoumei/RISCV/BenchmarkSpecs.lean`)
for one reason only: the serialized drain does not increment `minstret`, so a
minstret-derived CPI is meaningless for it.  The RTL defects below are fixed and
covered by the default suites.

## 1. Self-modifying code (FIXED)

`fence_i_test.c` (now `testbench/tests/fence_i_test.c`, in the default
`run-all-tests` / `run-cosim` suites) executes freshly stored code after
`fence.i`.  It used to hang: the fetched line containing the copy was never
refreshed.

Three things had to line up, and two were missing:

- the L1D ignored `fence_i` entirely (`fence_i_busy` was tied to 0) — a
  write-back cache, so freshly stored code sat dirty in the L1D and the L2 that
  the L1I refills from never saw it;
- the L1I cleared its valid bits on `fence_i` but left its FSM running, so a
  refill already in flight could install a stale line *after* the invalidate;
- the CPU never asserted `fence_i` at all (`CachedCPU.lean` tied the port to
  zero).

Now:

- **L1D flush** (`L1DCache.lean`): a request latches, and on IDLE the FSM sweeps
  all 8 lines (2 ways × 4 sets) in order, writing each valid+dirty line back to
  the L2 through the existing eviction datapath and dropping its dirty bit.
  `fence_i_busy` is high from the request until the sweep ends.  A `fence.i`
  arriving while the D-side is busy (miss/eviction in flight) is latched and
  served at the next IDLE, so the CPU can pulse.
- **L1I invalidate** (`L1ICache.lean`): `fence_i` now also forces the FSM to
  IDLE, so a response arriving after the invalidate cannot reinstall a line.
- **CPU wiring** (`CPU.lean`, `CachedCPU.lean`): the CPU exposes a one-shot
  `icache_fence_i` pulse, issued only once the pipeline has drained
  (`rob_empty`) and every prior store has reached the L1D (`lsu_sb_empty`) —
  otherwise a store still in flight would land after the flush — and the drain
  completes only after `fence_i_busy` drops.  Ordering is therefore
  stores → writeback → invalidate → redirect → fetch.

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

Note on the alternative: letting slot 0 dispatch *during* the start cycle of a
slot-1 serialize (which is what the CSR/trap paths do) also fixes the drop, but
it exercises a latent free-list hazard - a speculatively allocated physical
register released on that path came back to the speculative bitmap and was
re-allocated (observed as `p0` reaching a rename and the ROB head never
completing).  The defer keeps every drain start on the slot-0-selected path and
never introduces that overlap, so it avoids the hazard rather than fixing it.
The free-list bug is not otherwise reachable by the current tests.
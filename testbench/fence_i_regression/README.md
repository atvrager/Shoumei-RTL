# Zifencei serialization regressions

Three distinct `fence.i` / serialize-path defects found while bringing up the
benchmark suite, all now fixed.  Kept as a record of what was wrong and why the
fix looks the way it does.

`fence.i` remains in `BENCH_SKIP` (`lean/Shoumei/RISCV/BenchmarkSpecs.lean`)
for one reason only: the serialized drain does not increment `minstret`, so a
minstret-derived CPI is meaningless for it.  The fixes for the RTL defects below
are in place, and the default suites cover them.

## 1. Self-modifying code (fixed)

`fence_i_test.c` (now `testbench/tests/fence_i_test.c`, in the default
`run-all-tests` / `run-cosim` suites) executes freshly stored code after
`fence.i`.  It used to hang: the fetched line containing the copy was never
refreshed.

Three things had to line up, and two were missing:

- the L1D ignored `fence_i` entirely (`fence_i_busy` stayed 0). The L1D is a
  write-back cache. Freshly stored code sat dirty in it, and the L2 that the
  L1I refills from never saw it.
- the L1I cleared its valid bits on `fence_i` but left its FSM running. A
  refill already in flight could install a stale line *after* the invalidate.
- the CPU never asserted `fence_i` at all (`CachedCPU.lean` tied the port to
  zero).

Now:

- **L1D flush** (`L1DCache.lean`): a request latches, and on IDLE the FSM sweeps
  all 8 lines (2 ways × 4 sets) in order. It writes each valid+dirty line back
  to the L2 through the existing eviction datapath and drops its dirty bit.
  `fence_i_busy` is high from the request until the sweep ends.  The FSM latches
  a `fence.i` that arrives while the D-side is busy (miss/eviction in flight).
  It serves that request at the next IDLE, so the CPU can pulse.
- **L1I invalidate** (`L1ICache.lean`): `fence_i` now also forces the FSM to
  IDLE, so a response arriving after the invalidate cannot reinstall a line.
- **CPU wiring** (`CPU.lean`, `CachedCPU.lean`): the CPU exposes a one-shot
  `icache_fence_i` pulse. The CPU issues this pulse only once the pipeline has
  drained (`rob_empty`) and every prior store has reached the L1D
  (`lsu_sb_empty`). Without that guard, a store still in flight would land after
  the flush. The drain completes only after `fence_i_busy` drops, so the order
  is stores, writeback, invalidate, redirect, fetch.

## 2. Stale L1I line decodes during refill (fixed)

On an L1I miss the cache presents the stale contents of the refilling set
(on the bench: leftover `fence.i` byte patterns) while the fetch stage
holds its PC.  The ungated `fi_selected` start path decoded that stale
word as a real `fence.i` and fired a phantom drain, dropping in-flight
instructions (observed: `.Lfail`'s `lui` never retired, `addiw` ran with a
reset register).  Fixed in `CPU.lean`:

- the serialize start (`fi_selected`) uses the valid-gated
  `fi_det_{0,1}_gated` matches, and
- the design masks decode-valid while `fetch_stall_ext` (L1I refill) is high.
  A stale line can never decode, serialize, or trap mid-refill.

## 3. Slot-0 predecessor of a slot-1 serialize (fixed)

A serialize-class instruction (fence.i / WFI) decoded in slot 1 used to
suppress *both* slots at the drain start (`fi_start_nocsr`). It also redirected
to the serializing instruction's PC+4.  Its slot-0 block-mate, a program-order
predecessor that had not executed yet, was therefore never fetched again. The
pipeline dropped it silently.  On the bench that showed up as a loop counter
that never decremented, that is, a hang.

Fixed in `CPU.lean` by *deferring* the serialize one cycle instead of
dispatching into the live drain:

- when slot 1 holds a fence.i/WFI whose slot-0 block-mate is a dispatchable
  non-serialize instruction, the fetch stage half-steps. It ORs `ser_s1_defer`
  into `any_dual_stall`, which masks slot 1 and advances the fetch PC by 4.
- the predecessor then dispatches alone. The fetch stage re-presents the
  serialize in slot 0 on the next cycle. There the drain takes its well-tested
  slot-0-selected path.

Only fence.i and WFI need the defer. CSR and the trap-class ops
(ECALL/MRET/illegal) already let slot 0 dispatch, and for those the trap must
keep `mepc` on the serializing instruction. Deferring them would move `mepc`
onto a predecessor that has already retired.  The design excludes interrupt
injection for the same reason (slot 0 retires before the sequencer redirects).

Regression test: `testbench/tests/serialize_pair_test.S` (in the default
`run-all-tests` / `run-cosim` suites).  It pairs each `fence.i` with a
dependent slot-0 predecessor in a loop that re-enters at the pair. Both the
counter and a data-carrying predecessor must therefore have executed. Before
the fix the test hangs (never writes `tohost`), and after the fix it passes in
~480 cycles.

Letting slot 0 dispatch *during* the start cycle of a slot-1 serialize is the
alternative (the CSR/trap paths do this). That also fixes the drop, but it
exercises a latent free-list hazard. A speculatively allocated
physical register released on that path came back to the speculative bitmap.
The allocator then re-allocated it (observed as `p0` reaching a rename and the
ROB head never completing).  The defer keeps every drain start on the
slot-0-selected path and never introduces that overlap, so it avoids the hazard
rather than fixing it. No current test reaches the free-list bug by another
route.
# Zifencei serialization regressions

Three distinct gaps in the `fence.i` / serialize path, from the
benchmark-suite bringup.  Fences and back-to-back serialize instructions
are excluded from the suite (`BENCH_SKIP` in
`lean/Shoumei/RISCV/BenchmarkSpecs.lean`) until these land.

## 1. Self-modifying code (known)

`fence_i_test.c` reproduces a real gap: a fetched 32B line containing
freshly stored code is not refreshed after `fence.i` (sim hangs; Spike
cosim stalls at the copied call).  The cached CPU ties the L1I `fence_i`
invalidate input to zero ("FENCE.I not yet implemented in W=2",
`CachedCPU.lean`).  Kept OUT of the buildable `testbench/tests` list (and
cppcheck scope) until the Zifencei I-flush rework lands; run manually:

    make -C testbench/tests fence_i_test.elf   # after moving back

## 2. Stale L1I line decodes during refill (FIXED)

On an L1I miss the cache presents the stale contents of the refilling set
(on the bench: leftover `fence.i` byte patterns) while the fetch stage
holds its PC.  The ungated `fi_selected` start path decoded that stale
word as a real `fence.i` and fired a phantom drain, dropping in-flight
instructions (observed: `.Lfail`'s `lui` never retired, `addiw` ran with a
reset register).  Fixed in `CPU.lean`:

- the serialize start (`fi_selected`) now uses the valid-gated
  `fi_det_{0,1}_gated` matches, and
- decode-valid is masked while `fetch_stall_ext` (L1I refill) is high, so
  a stale line can never decode, serialize, or trap mid-refill.

## 3. Slot-0 predecessor of a slot-1 serialize is dropped (OPEN)

When a serialize-class instruction (fence.i / CSR) occupies slot 1, its
slot-0 block-mate is a program-order predecessor that has not executed.
The serialize initiator suppresses both slots and the drain redirects to
the serializing instruction's PC+4, silently dropping the predecessor
(observed: `li x29, 64` adjacent to a `fence.i` never retired; the loop
counter stayed 0).  Allowing slot-0 dispatch during the drain start fixes
the drop but exposes a latent freelist/RAT defect (a phys register `p0`
eventually leaks back to the free list and is re-allocated, deadlocking
FreeRTOS's tick path).  Both sides need the serialize/memory rework:
a correct serialize must execute the predecessor before draining without
disturbing the speculative register accounting.
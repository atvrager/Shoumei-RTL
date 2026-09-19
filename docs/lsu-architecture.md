# Decoupled, Timing-First Out-of-Order LSU Architecture

This document specifies the Load-Store Unit (LSU) redesign for Shoumei. It
replaces the current in-order, blocking store-forwarding stub with a decoupled
micro-op engine whose critical paths are budgeted per PDK, and whose store data
path is **length-agnostic with a 128-bit base width** (two 64-bit memory
instructions per execution slot; a clean baseline for future vector loads and
stores).

Status: design specification. Implementation lands in
`lean/Shoumei/RISCV/Memory/{LSU,StoreBuffer,StoreBufferProofs}.lean`,
`lean/Shoumei/RISCV/Execution/MemoryExecUnit.lean`, and the cache hierarchy
(`Cache/L1DCache.lean`, `Cache/CachedCPU.lean`).

---

## 1. Motivation

### 1.1 Timing targets

| PDK | Target | $T_\text{clk}$ | Current LSU critical path |
|---|---|---|---|
| ASAP7 (7nm predictive) | $\ge 1.0$ GHz | $\le 1.0$ ns | 64-bit AGU + 64-bit CAM + priority encode + byte merge + tag hit mux in **one** cycle |
| 12nm/16nm FinFET | $\ge 750$ MHz | $\le 1.33$ ns | same unpipelined chain |
| GF180MCU (180nm planar) | $\ge 66$ MHz | $\le 15.15$ ns | same, and 180nm metal stacks make 8-way CAM fan-out dominate |

The combination of full-width address addition, associative store-queue
comparison, priority encoding, byte merging, and cache-tag hit muxing cannot be
closed in a single cycle at any of these budgets. The redesign splits that
chain across two registered stages (M1, M2) and never feeds combinational
output back into the same cycle it was produced.

### 1.2 Structural critique of today's LSU

- `LSU.lean` executes loads/stores atomically in one step against an
  in-order model; a store result does not leave the memory execution stage
  until the whole instruction retires (`PendingLoadRequest` is a *single*
  in-flight load; any miss blocks the port).
- `StoreBuffer8` already uses an 8-entry circular queue with barrel-rotate +
  `PriorityArbiter8` youngest-match forwarding, but the forwarding decision is
  fully combinational in one cycle: 8× 64-bit equality compares + rotate +
  priority encode + 8:1 data mux, chained with the AGU above it in `LSU`.
- The load miss path (`lsuWait`-style FSM in the cache interface) blocks new
  requests until the outstanding miss refills, so independent loads/stores
  cannot proceed behind a miss.

The target architecture (below) keeps `StoreBuffer8`'s good bones — circular
queue, age-ordered youngest-match priority — and re-times them: compare low
address bits in M1, qualify with the upper tag from a **registered** M1 match
vector in M2, and move byte/lane selection and sign extension into M2's
registered domain.

---

## 2. Top-level architecture

```
              ROB commit                CDB (2×64b results)
                 │                            ▲
                 ▼                            │
   ┌─────────────────────────────────────────────────────┐
   │                     LSU                               │
   │                                                       │
   │  dispatch ──► decode ──► ┌────────┐   ┌────────────┐  │
   │  (2×64b     (STA/STD/    │ STA (M1)│──►│ M1→M2 reg  │  │
   │   uops/     load)        │ AGU     │   │ (addr, tag,│  │
   │   slot)                  └────────┘   │  match[7:0],│  │
   │                              │        │  size, sign)│  │
   │                              ▼        └─────┬──────┘  │
   │                       ┌──────────┐         │         │
   │                       │ SQ (8×W) │◄────────┘         │
   │                       │ age-     │   ┌────────────┐  │
   │                       │ ordered  │──►│ M2: forward │─┼─► CDB
   │                       │ circular │   │ decision +  │  │
   │                       └──────────┘   │ data mux    │  │
   │   STD (rs2 via PRF) ──► data/mask    └────────────┘  │
   │                       write into SQ slot             │
   │                                                       │
   │  miss ──► MSHR[0:1] (2-entry, registered) ──► L1D/L2 request
   └─────────────────────────────────────────────────────┘
                            │
                    L1 D-cache (SRAM tag/data access in M1)
```

Key properties:

- **Decoupled micro-ops.** A memory instruction is split at dispatch into
  STA (address) and STD (data) for stores; loads flow as atomic address+data
  requests through two stages.
- **No circular combinational feedback.** Every path is `register → logic →
  register`. The M1→M2 boundary is a hard pipeline register; the forwarding
  mux in M2 consumes only register outputs.
- **Non-blocking miss handling.** A miss allocates an MSHR slot and releases
  the request bus; independent memory ops continue (hit-under-miss).

---

## 3. Micro-op decoupling (STA / STD / load)

Memory instructions split at dispatch exactly as in the classic decoupled
memory execution literature [ref 2, ref 4]:

| Micro-op | Payload | Where it executes | Effect |
|---|---|---|---|
| **STA** (store address) | `{op, sq_tag, rs1, imm}` | M1 AGU: `addr = rs1 + sext(imm)` | Allocates SQ entry at pre-allocated index; writes `addr`; sets `stA_done` |
| **STD** (store data) | `{sq_tag, data[W-1:0], mask[W/8-1:0]}` | PRF/CDB side path | Writes data + byte-enable mask into the SQ slot; sets `stD_done` — *not* on the AGU path |
| **Load** | `{op, rs1, imm, dest_tag}` | M1 → M2 | Two-stage forwarding vs. cache access; CDB broadcast in M2 |

Ordering rules:

- STA and STD for one store are **independent**: STD may arrive before or
  after STA (data is sourced from the PRF/CDB, as in the decoupled reservation
  station model [ref 2]). An SQ entry only becomes *forwardable* once both
  `stA_done ∧ stD_done` hold.
- Stores allocate SQ entries **in program order** at rename time using the
  existing `sb_alloc_ctr` pre-allocation sidecar in `CPU.lean` (already
  present; flush-reloadable from `sb_flush_tail`).
- Loads are self-contained; they carry no SQ allocation. Their SQ match
  vector is computed against all live entries and qualified by age.

### 3.1 Micro-op interface (delta vs. today)

`MemoryExecUnit.lean` re-emits as a decoupled pair:

- `sta_valid`, `sta_addr[63:0]` — the address output group, valid only for STA.
- `std_valid`, `std_data[W-1:0]` — the store-data output group, valid only for
  STD, **independent** of `sta_valid`/`sta_addr`.

`LSU.lean` dispatch becomes a 2-wide 128-bit slot:

- `dispatch_sta_valid[1:0]`, `dispatch_std_valid[1:0]`: one slot carries up to
  two 64-bit memory ops (or one 128-bit vector op).
- `load_valid`, `load_uop` (opcode | size | sign | dest_tag) for the M1→M2
  load pipeline.
- `sq_flush_restore`: reload of `sb_alloc_ctr` from the SQ's surviving-entry
  tail after a misprediction flush.

---

## 4. Two-stage load pipeline

```
Cycle M1                                     Cycle M2
┌────────────────────────────────────┐      ┌─────────────────────────────────┐
│ 64-bit AGU (Kogge-Stone)          │      │ upper-tag EQ (addr[63:12] vs     │
│   addr = rs1 + sext(imm)          │      │   entry[63:12])  ∧  stA_done     │
│ L1 D-cache SRAM tag/data access   │      │   ∧  stD_done                    │
│ SQ low-bits compare addr[11:3]    │─────►│ age-qualified match vector       │
│   vs entry[11:3] (9-bit, 8×)      │      │ PriorityArbiter (youngest wins)  │
│                                   │      │ 128-bit lane/byte mux           │
└────────────────────────────────────┘      │ sign/zero extend                │
                                            │ replay_needed detect            │
                                            │ CDB drive                       │
                                            └─────────────────────────────────┘
```

### 4.1 M1 (address generation & fast indexing)

- 64-bit address addition — the *only* adder in the load path — plus
  concurrent L1D SRAM tag/data read and SQ `[11:3]` comparisons.
- The `[11:3]` slice covers the complete SRAM index + word/byte offset range
  of an L1 line; **no full 64-bit comparator runs in M1**.

### 4.2 M2 (forwarding decision & CDB broadcast)

- Qualify the M1 match vector with the upper address tag `[63:12]` and the
  entry's `stA_done ∧ stD_done`, from **registered** inputs only.
- Priority-encode the qualified vector (youngest = closest to tail wins) and
  drive the 128-bit data mux + sign/zero extension onto the CDB.
- Compute `replay_needed` (Section 5.3) and `load_addr_unknown` (Section 5.4)
  with no path back into M1.

### 4.3 Clean separation of the classic critical chain

| Operation | Stage | Eval budget (ASAP7 1.0 ns) |
|---|---|---|
| 64-bit AGU | M1 | 4–5 logic levels off the dispatch register |
| 9-bit compare ×8 | M1 | 2 levels, low fan-out |
| upper-tag EQ (52-bit) | M2 | 3 levels off the M1→M2 register |
| priority encode + 8:1 mux | M2 | 3–4 levels |
| lane/byte select + sign extend | M2 | 2 levels |

---

## 5. Low-capacitance circular Store Queue (SQ)

### 5.1 Structure

- **8 entries**, 128-bit data payload each (`W = 128` base): two 64-bit
  memory ops per execution slot, vector-ready (Section 8).
- Circular `head`/`tail` with a running count (reuse `QueuePointer` /
  `QueueCounterLoadable` building blocks already in `StoreBuffer8`).
- Per-entry flags: `valid`, `committed` (ROB), `stA_done`, `stD_done`.

### 5.2 Age masking: `older(i, j)`

The forwarding policy is defined against an explicit total age order on SQ
indices, mirroring the structural barrel-rotate + `PriorityArbiter8`
implementation already present:

```
older(i, j)  ≡  circular distance from head to i  <  distance from head to j
```

- `older` is a strict total order on the live entries (proved in
  `StoreBufferProofs.lean`, Section 11).
- The M2 selection is: *forward from the youngest entry that matches and is
  `stA_done ∧ stD_done`*, where "youngest" is defined by `older`.
- Structural encoding: rotate the qualified match vector so the youngest
  entry lands at position 0 (`tail`-based barrel rotate), run
  `PriorityArbiter8` (position 0 wins), rotate the grant back. No combinational
  loop: the rotate/arbiter consumes only latched match bits; the grant never
  feeds a comparator or the AGU in the same cycle.

### 5.3 Forwarding policy

1. **Exact match** (full address equality, entry forwardable): forward the
   128-bit payload (lane/byte-selected for the load size and `addr[2:0]`)
   directly to the CDB in M2. One-cycle registered path.
2. **Partial overlap / mismatched mask** (e.g. a byte store overlapping a
   word load, or an unaligned access): **do not** build an iterative multi-byte
   rotator or multi-entry byte merger in the critical path (the classic
   frequency killer). Instead assert `replay_needed`; the load is replayed or
   stalled until the offending store drains [ref 1's replay-filter philosophy].
3. **Address unknown**: if the *youngest possibly-matching* store has
   `stA_done = false` (or `stD_done = false`), treat the load as
   `load_addr_unknown` and stall/replay rather than guessing (baseline);
   a later phase may speculate using SVW sequence numbers [ref 1].

### 5.4 Detect outputs

| Output | Meaning |
|---|---|
| `sq_fwd_hit` | youngest-match forwarding available |
| `sq_fwd_data[127:0]` | forwarded payload (lane-selected in M2) |
| `replay_needed` | any partial-overlap/misaligned hit OR unknown-address qualifier |
| `sq_full` / `sq_empty` | dispatch blockers |
| `sq_fwd_committed_hit` | hit on a committed entry (drain-in-progress) |

---

## 6. Non-blocking cache port with registered MSHR

Replaces the blocking `lsuWait`-style behavior in the cache interface
(`L1DCache.lean` FSM `IDLE → WRITEBACK → REFILL_WAIT → IDLE`) with a 2-entry
Miss Status Holding Register:

```
miss    ──► MSHR slot alloc (valid, tag, type, pending data)
                 │
   L1D continues serving hits (hit-under-miss)
                 │
refill/response ──► MSHR slot fill ──► CDB broadcast (load) or SQ drain (store)
```

- **2 entries**, each: `valid`, `addr`, `type` (load / line refill / writeback
  drain), `data[W-1:0]` staging, per-slot FSM
  (`IDLE → ALLOCATED → WAIT → FILL`).
- Misses never hold the request bus; up to two independent misses track
  concurrently, and independent hits/ALU ops proceed.
- Store drains (committed SQ → L1D) allocate an MSHR slot on write miss;
  forward progress is preserved by the SQ's head-ordered dequeue.
- FENCE.I drain uses the existing `fence_i`/`wb_ack` handshake through the
  L1D writeback path; the LSU exposes `fence_i_busy` to the microcode
  sequencer.

---

## 7. Store commitment & memory ordering (TSO)

- Stores commit in program order from the ROB (existing `commit_store_en` +
  internal commit pointer in `StoreBuffer8`).
- Committed stores drain head-first over the Decoupled `deq_valid/deq_ready`
  handshake into the L1D.
- Loads bypass not-yet-committed stores only via the age-ordered forwarding
  path above; a load with no SQ match reads the cache directly. This is the
  TSO rule: *loads may bypass stores to different addresses*; the age-ordered
  SQ guarantees *same-address* forwarding coherence (Section 11).
- The store-buffer reduction argument follows Cohen–Schirmer's inductive
  store-queue draining technique [ref 3] extended to the circular queue;
  the repository tracks it as the `store_buffer_memory_refinement` theorem
  family in `StoreBufferProofs.lean`.

---

## 8. Length-agnostic 128-bit data path

- All data-bearing structures are parameterized by width `W`:
  `StoreQueueEntry W`, SQ payload, `std_data`, `sq_fwd_data`, MSHR staging.
- **Base deployment: `W = 128`.** One execution slot (two dispatch lanes,
  64-bit each) packs **two memory instructions** into one 128-bit data
  request/forwarding event: `{LD64,LD64}`, `{LD64,ST64}`, or `{ST64,ST64}`.
- Lane selection: `addr[3]` picks the 64-bit half-lane within the 128-bit
  payload; `addr[2:0]` selects bytes inside the lane (M2, registered).
- Vector future: `vle128/vse128` (and segmented variants) map directly onto
  the same datapath — one request, one 128-bit payload, mask-driven byte
  enables. Wider vector lengths compose by re-issuing per 128-bit slice.
- Behavioral model uses `BitVec W` for data fields; proofs instantiate
  `W = 128` concretely (`native_decide`) plus generic lemmas where the
  width is free.

---

## 9. Cache hierarchy hookup

Two integration points, both in `Cache/`:

1. **`L1DCache.lean`**: gains the MSHR front-end (Section 6). The L1D keeps
   its 2-way/4-set/32B-line organization; `mkL1DCache` ports gain
   `mshr_alloc`, `mshr_index`, `mshr_fill` signals and drop the monolithic
   `stall` (now only asserted while *both* MSHR slots are occupied by
   non-repeatable misses).
2. **`CachedCPU.lean`**: `mkCachedCPU` currently passes the CPU's
   `dmem_req_*`/`dmem_resp_*` straight into `MemoryHierarchy`. The LSU
   replaces that raw pass-through at the CPU↔L1D boundary: CPU memory
   execution talks to the decoupled LSU (STA/STD/load + CDB), and the LSU
   owns L1D request/response qualification through the MSHR. `MemoryHierarchy`
   is untouched (still L1I/L1D/L2 composition); only its `dmem_*` ports now
   hang off the LSU instead of the CPU internals.

---

## 10. File-by-file implementation plan

| File | Change |
|---|---|
| `Execution/MemoryExecUnit.lean` | Decouple outputs: `sta_valid/sta_addr` group vs `std_valid/std_data[W-1:0]` group; keep AGU = add-in-M1 (Kogge-Stone, already present). |
| `Memory/StoreBuffer.lean` | Parameterize entry data by `W` (base 128); add `stA_done/stD_done`, explicit `older(i,j)`, M1 `[11:3]` compare outputs, registered M2 qualifier, `replay_needed`, `load_addr_unknown`; keep commit pointer + flush recovery (popcount/`flush_tail`). |
| `Memory/LSU.lean` | Two-stage load pipeline registers `lsu_stage1 → lsu_stage2`; STA/STD decoupled dispatch; MSHR-based non-blocking port; CDB drive in M2 only. |
| `Memory/StoreBufferProofs.lean` | Age-order totality of `older`; youngest-match forwarding coherence (forwarded data == data of youngest matching forwardable store); acyclicity of the match→priority→mux chain; port/gate/instance counts (updated). |
| `Memory/LSUProofs.lean` | Updated structural counts for the retimed circuit; dependency certificate refresh. |
| `Cache/L1DCache.lean` | Registered 2-entry MSHR replacing single-slot blocking miss handling. |
| `Verification/CompositionalCerts.lean` | Certificates for the resized `StoreBuffer8`/`LSU`; add MSHR-backed `L1DCache` deps (L1D already certified, deps derive from instances). |
| `GenerateAll.lean` | Keep `mkStoreBuffer8`/`mkLSU` names (topological order preserved); add any new leaf circuits (e.g. lane mux) if emitted. |
| `CPU.lean` | Rewire `u_lsu` port map for the new LSU interface (STA/STD groups, 128-bit `fwd`/`enq` data); keep `sb_alloc_ctr` pre-allocation and flush reload glue. |

Naming stability: `StoreBuffer8` (8 entries × 128-bit payload) and `LSU`
remain the emitted module names so codegen, certificates, and the CPU
instantiation keep their identity; widths grow inside.

---

## 11. Verification plan

### 11.1 Lean theorems (`StoreBufferProofs.lean`)

1. **`older_total_order`**: `older` is irreflexive, transitive, and total on
   live SQ entries (structural: `native_decide` on the 8-entry instance;
   generic: induction on circular distance).
2. **`forward_youngest_match_coherent`**: for every load with an exact match,
   the forwarded payload equals the payload of the youngest forwardable
   matching entry. Proved by defining the selection as
   `scan youngest-first` and showing the structural priority encoding equals
   the scan ([ref 4]'s store-set intuition made exact for the age order).
3. **`forwarding_acyclic`**: every gate in the M1 compare / M2 qualify /
   priority / mux cone drives only registers or primary outputs; no gate in
   the cone is fed by a gate it feeds (structural depth check via
   `native_decide` on the flattened netlist).
4. **`replay_on_partial_overlap`**: any non-exact address overlap asserts
   `replay_needed` (never forwards wrong bytes).
5. **`mshr_two_inflight`**: at most two misses tracked; independent
   request served while slots allocated (hit-under-miss).

### 11.2 Flow checks

- `lake build` — all proofs, zero axioms.
- `make codegen` — `generate_all --export-certs` validates the registry
  against emitted instances.
- `python3 verification/slang-lint.py output/sv-from-lean` — IEEE 1800-2017
  elaboration of the retimed `LSU`/`StoreBuffer8`/`L1DCache`.
- `make systemverilog` (Yosys read/hierarchy).
- RISC-V cosim (`make -C testbench cosim && run-cosim`) for the 107/107
  suite, plus targeted store-forwarding tests (store→load same address,
  sub-word overlap → replay, miss → MSHR → refill → CDB).
- Per-PDK synthesis smoke: `make synth-gf180` / `make synth-asap7` on
  `LSU` and `StoreBuffer8` to confirm M1-only adder + M2-only mux partition
  meets the Section 1.1 budgets.

---

## 12. References

1. S. Subramaniam, G. Loh, and M. Roth, *Store Vulnerability Window (SVW)
   and Scalable Store Forwarding* (MICRO 2005 / IEEE Micro).
   https://acg.cis.upenn.edu/papers/micro05_storeq.pdf
2. R. Castro, D. Chaver, et al., *A Decoupled Execution Engine for
   Out-of-Order Processors* (PACT 2006).
   https://citeseerx.ist.psu.edu/document?doi=2d6b38dafe5fa23dcbab204128f64aaeb578a0a8
3. E. Cohen and N. Schirmer, *A Better Reduction Theorem for Store Buffers*
   (arXiv:0909.4637). https://arxiv.org/abs/0909.4637
4. G. Chrysos and J. Emer, *Memory Dependence Prediction Using Store Sets*
   (ISCA 1998). https://ftp.cs.wisc.edu/sohi/theses/moshovos.pdf
5. Site-local synthesis methodology & budgets:
   `docs/physical-design.md` (GF12 750 MHz close, GF180/ASAP7 Yosys runs).

---

## 13. Cache & TCM sizing (per node, one heuristic)

Sizes are chosen per PDK from **one rule**, so any node's numbers are
derivable: *the SRAM budget is the silicon left after the core, split
I:D = 1:4, stepped to powers-of-two*.

```
mem_budget_mm2 = usable_die − core_logic_area − pad/peripheral_overhead
mem_bits       = mem_budget_mm2 / (bitcell_um2 × 1.3 periphery_factor)
ITCM           = round_pow2(mem_bits / 5)      # I-tight
DTCM           = round_pow2(4 × mem_bits / 5)  # D-ample
```

| Node | Usable die | Core logic | SRAM bitcell | Budget | Recommended ITCM / DTCM |
|---|---|---|---|---|---|
| GF180MCU — wafer.space quarter slot | 4.9 mm² | 6.4 mm² core @ 64 MHz | ≈ 3.0 µm²/bit | ≈ 0 (core overflows slot) | system on full slot; tiny MEM only |
| GF180MCU — wafer.space full slot | ≥ 4.9 mm² (see shuttle) | as above | ≈ 3.0 µm²/bit | ≈ 0.8 mm² ≈ 205 kbit | **8 KB / 16 KB** (8/32 needs a slimmed core) |
| GF 12LPP+ (12 nm) | package-limited | 0.057 mm² core | ≈ 0.05 µm²/bit | effectively unbounded | **16 KB / 64 KB** |
| ASAP7 (research) | n/a | 0.025 mm² core | ≈ 0.04 µm²/bit | effectively unbounded | **16 KB / 64 KB** |

Fabrication reality (wafer.space, GF180MCU open PDK): quarters are 4.9 mm²
from $2,000/slot (~1,000 dies at $7); the 64 MHz core alone (6.4 mm² synth
area) exceeds the quarter slot, so memory-enabled builds target the full
slot. Open SRAM macro sources on this node already exist — the
`gf180mcu_ocd_sram_test` suite (Run 2) and GlobalFoundries'
`gf180mcu_fd_ip_sram` — so "foundry SRAM, not FF arrays" is a resolved
precedent, not a hope.

Answering "8 KB ITCM / 64 KB DTCM": that exact split is a FinFET-class ask.
On the GF180MCU full slot, a 64 KB DTCM alone (~512 kbit ≈ 2 mm²) overflows
the memory budget beside the 6.4 mm² core; 8/16 fits with headroom, 8/32
fits only after trimming core or pads.

Mechanical note: the caches are currently fixed-geometry
(`L1D` 2-way×4-set×32 B, `L1I` 1-way×8-set×... , `L2` …, all FF/register
storage except the L1D data **`RAMPrimitive`s**). Sizing is applied by
parameterizing the cache builders from `CPUConfig.memConfig` (index/tag
widths derive from `size`), keeping the concrete defaults byte-identical so
proofs/certs/cosim stay valid.

## 14. Foundry SRAM integration (OpenRAM, not FF arrays)

The data arrays are the `RAMPrimitive`s already in the DSL (`Circuit.rams`)
and already used by `L1DCache` (2× 4×256, 1R1W). Synthesis intent:

- **Primary path — foundry / OpenRAM macros, never FF arrays.** Each
  `RAMPrimitive` emits as an `ifdef`-guarded instantiation:

  ```
  `ifdef SHOUMEI_SRAM_MACROS
    // e.g. OpenRAM sram_1r1w, per-process bitcell (gf180mcuD / pdk-asap7)
    sram_1r1w_<depth>x<width> u_ram_<name> (
      .clk (clock), .we  (w_we),  .waddr (w_addr),
      .wdata(w_data), .raddr(r_addr), .rdata(r_data));
  `else
    reg [width-1:0] ram_<name> [0:depth-1];   // verilator fallback only
  `endif
  ```

- **OpenRAM support** (scripts/): a `make sram-macros` target drives
  OpenRAM per node (`--pdk gf180mcuD` / ASAP7 flavor) to produce the macro
  models + liberty the flow consumes; the generated module/port contract
  matches the emitter's incl. width/depth.
- Write ports map `en+addr+data`; read ports map `addr+data`; a single
  `1W1R` RAM like L1D's becomes an OpenRAM `sram_1r1w` — no re-architecting.
- Tags/valid/dirty stay registers (tiny, no macro worth it).
- Simulation: the `else` `reg`-array fallback is the Verilator path (fine at
  cache scale); if a macro model is required in sim, the emitted `ifdef`
  branch can instantiate a DPI-backed macro model — never a giant FF array.

## 15. Long-term software verification of cache behavior

Lean proofs alone do not watch cache semantics over time. Added suite:

- `testbench/cache_model_test/` — C++ conformance harness driving the
  emitted CppSim `L1DCache` cycle model against a small reference cache:
  directed + seeded-random traffic; invariants: read-after-write hits,
  refill populate, LRU victim selection, dirty-writeback data integrity,
  FENCE.I drain, miss/hit-under-miss.
- RISC-V system tests (`testbench/tests/`): store-to-load forwarding
  (`store_fwd_test.c`), `fence.i` self-modifying code, cache-thrash stride
  loops — run by the existing `run-all-tests` / cosim targets.
- Hooked into `verification/smoke-test.sh` so CI keeps them alive.

## 16. Lint & synthesis acceptance (DC-NXT-friendly, Yosys-checked)

Emitted SV is checked the way a DC NXT handoff would be:

- Yosys `read_verilog -sv` + `check` (no latches, no combinational loops)
  + `synth -top` with ABC (area+timing per node) for `LSU`,
  `StoreBuffer8`, `L1DCache`, `L2Cache`, `CachedCPU` — the `make synth-*`
  family already covers CPU tops; CachedCPU tops get the same treatment.
- Structural rules enforced at codegen time: registered outputs only for
  forwarding muxes, no `if` without `else` in `always_comb`-style emission,
  no latches (every FF has an enable mux), saturated pointers, no
  combinational feedback (proved in `StoreBufferProofs`), `always_ff` on
  clock edges only.
- slang elaboration of every emitted file (existing lint).
# Zb* microcode: gate-level sketches

How the microcoded Zb* fallback engine is wired. The sketches are a reading aid
for `lean/Shoumei/RISCV/Microcode/FallbackSequencer.lean`; the authority is the
Lean source, and correctness is established by the proofs and the simulations,
not by this document.

Companion files:

| File | Contents |
| :--- | :--- |
| `Microcode/ZbEmulationLibrary.lean` | specs, the 43-entry `zbTable`, `zbRom`, `routineIndex`, the behavioural model |
| `Microcode/FallbackSequencer.lean` | the circuit: encoder, control store, micro-ALU, scratchpad, FSM |
| `Microcode/ZbEmulationProofs.lean` | one equivalence theorem per encoding plus dispatch and fault theorems |
| `Microcode/FallbackSequencerProofs.lean` | port, instance and gate counts |

## 1. Control word

The Zb* engine has its own 32-bit control word and its own control store. The
24-bit CSR/FENCE/trap word (`MicrocodeTypes.ROMEntry`) is left alone: it has a
4-bit opcode, two 2-bit temp indices and no room for the micro-ALU operands the
Zb* routines need.

```
 31      26 25 24 23 22 21 20 19    16 15                    0
┌──────────┬─────┬─────┬─────┬────────┬──────────────────────┐
│  opcode  │ dst │src1 │src2 │  rsvd  │         imm          │
│   6 bit  │2 bit│2 bit│2 bit│  4 bit │        16 bit        │
└──────────┴─────┴─────┴─────┴────────┴──────────────────────┘
   `FallbackOp.toNat`      temp index   0        `LOAD_IMM` payload
```

* `opcode` — 53 micro-ops (`FallbackOp`); `LOAD_SHAMT` = 49, `ALU_ROLW` = 50,
  `ALU_RORW` = 51, `ALU_CTZW` = 52 are the additions the Zb* routines needed.
* `dst`/`src1`/`src2` — scratchpad indices. `dst` is the write target;
  `src1`/`src2` are the micro-ALU operands, except for `MOV_TO_RD`, whose
  `src1` names the temp published on the CDB.
* `imm` — `LOAD_IMM` payload (0, 32, 48 or 56 across the whole store).

`LOAD_SHAMT` exists so that the seven immediate forms (`bseti bclri binvi bexti
rori roriw slli_uw`) take their shift amount from the instruction word at run
time. Without it each would need one routine per shift-amount value baked into
`imm`, against an 8-slot routine stride.

Control store: `routineStride` 8 micro-ops per routine, `routineCount` 43
emulated encodings at slots 0..42, the illegal-instruction routine at slot 43,
`zbRomSize` 512 entries so the micro-PC is exactly 9 bits. Every routine is
5..8 micro-ops and ends in `.DONE`; entries past a routine's last micro-op read
as `.DONE` too.

```
  ridx_q (6) ─┐
              ├─▶ 512 × 32 mux tree ─▶ romData[31:0] ─▶ opcode / dst / src1 / src2 / imm
  step_q (3) ─┘
```

Each of the 32 field bits is its own 512-entry binary mux tree (511 muxes),
addressed by `step_q` (low 3 bits) concatenated with `ridx_q`. That is 16 352
muxes and dominates the module's 43 240 gates.

## 2. Dispatch encoder

`zbTable` is the single source: the software decoder (`routineIndex`, a `find?`
over `List.finRange routineCount`), this encoder, the benchmark specs and the
proofs' `insn<Name>` constants all read it.

For each of the 43 entries the encoder builds one AND-term over the bits the
entry's mask fixes. A bit the mask leaves free is skipped; a fixed bit takes
`insn[b]` when the sample has it set and `~insn[b]` otherwise.

```
  insn_in[31:0] ─┬─▶ ~insn ─┐
                 │          ├─▶ 43 × (27-input AND term)  ─▶ hit_0..hit_42
                 └──────────┘                                     │
                                                                  ▼
     prio_r = hit_r & ~(hit_0 | … | hit_{r-1})   ──▶ 6-bit OR encoder ──▶ ridx_in
                                                                  │
     matched_enc = hit_0 | … | hit_42 ────────────────▶ latched at `start`
```

Priority (lowest index wins) mirrors `find?`. No two entries are ambiguous — the
mask sets were checked pairwise when the table was written — so priority never
actually arbitrates; it exists so that a future table edit cannot silently make
hardware and software disagree. When no term hits, `ridx_in` is `routineCount`
(43, `0b101011`) and the sequence traps.

Masks used: `0xFE00707F` (funct7 fixed, `rs2`/5-bit shamt free — the R-type forms
and `roriw`), `0xFC00707F` (funct6 fixed, 6-bit shamt free — the other immediate
forms) and `0xFFF0707F` (bits 31:20 fixed — the unary forms and `zext.h`).

## 3. Sequencer

```
 start ─────────────────────────────────────────────▶ ridx_q := ridx_in, step_q := 0
                                                        matched_q := matched_enc

 hold   = is_drain(romData) & ~drained        -- DRAIN stalls the micro-PC
 step   = active_q & ~hold                    -- this cycle executes a micro-op
 done   = step & is_done(romData)             -- last micro-op
 active'= start | (active_q & ~done & ~pipeline_flush)
 step'  = step ? step_q + 1 : step_q, forced to 0 on `start`

 cdb_inject  = done & matched_q
 redir_valid = done & matched_q
 trap_active = done & ~matched_q              -- slot 43 ends in TRAP_ILLEGAL
 redir_pc    = pc_q + 4
 trap_cause  = 2
 trap_val    = zext(insn_q)
```

The `active_q` qualification of the completion strobes is structural here: `done`
is combinational from `active_q` and the control store, so a branch redirect that
clears `active_q` cannot leave a stale strobe behind to inject a squashed result
or override the redirect that flushed it.

Capture: `insn_q`, `pc_q` and `cdb_tag_q` load on `start`; `rs1_q`/`rs2_q` load on
`op_latch = step & is_drain`, i.e. on the cycle the DRAIN micro-op retires, which
is the first cycle their CDB snoop value is final. `drain_dly1_q`/`drain_dly2_q`
delay the drain check two cycles so in-flight instructions reach the ROB.

## 4. Micro-ALU

Operands come from the scratchpad, selected by the control word:

```
 temp0..3 ─▶ mux4 (src1) ─▶ src1_val ─┐
 temp0..3 ─▶ mux4 (src2) ─▶ src2_val ─┴─▶ 33 datapaths ─▶ mux33 (opcode) ─▶ alu_val
```

`write_val` then selects between `alu_val`, `rs1_q`, `rs2_q`, the instruction's
shift amount and `romData.imm`; `tempWrite[k] = step & is_write & (dst == k)`
gates the scratchpad registers.

### 6-stage barrel shifter (`SLL`, `SRL`, `SRA`)

Stage `k` shifts by `2^k` and fills the vacated high bits; a stage whose
shift-amount bit is low is a no-op, so a zero shift amount is the identity.

```
  x ─▶ [>>1 | fill] ─▶ [>>2 | fill] ─▶ [>>4 | fill] ─▶ … ─▶ [>>32 | fill] ─▶ srl/sra
          ▲                ▲                ▲                    ▲
        sh[0]            sh[1]            sh[2]               sh[5]

  fill = 0 for SRL, x[63] for SRA
```

384 muxes each. `SLL` is the mirror image, filling with zero.

### Count trees (`CLZ`, `CTZ`, `CPOP`, `CTZW`)

Prefix-OR of the operand, inverted, then a population count.

```
  clz_acc[i]  = clz_acc[i-1] | x[63-i]     -- "some bit in the top i+1 is set"
  clz_bits[i] = ~clz_acc[i]                -- "the top i+1 bits are all zero"
  clz         = Σ clz_bits[0..63]          -- 64 for x = 0

  ctz_acc[i]  = ctz_acc[i-1] | x[i]
  ctz_bits[i] = ~ctz_acc[i]
  ctz         = Σ ctz_bits[0..63]          -- 64 for x = 0

  cpop        = Σ x[0..63]
  ctzw        = Σ (low-word trailing-zero bits)[0..31]   -- 32 for a zero word
```

`Σ` is a balanced adder tree that halves the number of partial sums each round
and doubles their width: 64 → 32 → … → 1, about 310 gates per count.

### Byte wiring (`ORCB`, `REV8`)

`ORCB` ORs each byte to one "any bit set" wire and fans it back out to eight
bits (8 × 7 OR + 64 buffers). `REV8` is pure wiring:
`out[8j+k] = in[8(7-j)+k]`.

### Extenders (`SEXT_W`, `ZEXT_W`)

`ZEXT_W` is 32 buffers plus 32 zeros. `SEXT_W` computes the sign bit once and
fans it out over the high half.

### Carry-less multiply (`CLMUL`, `CLMULH`, `CLMULR`)

Output bit `i` is the XOR of `a[j] & b[k]` over every `j + k = i + offset` with
`j, k < 64`. `offset` selects which 64-bit slice of the 128-bit carry-less
product is read:

| op | offset | `j` range for output bit `i` |
| :--- | :--- | :--- |
| `clmul` | 0 | `max 0 (i-63) … min 63 i` |
| `clmulh` | 64 | `max 0 (i+1) … min 63 (i+64)` |
| `clmulr` | 63 | `max 0 i … min 63 (i+63)` |

An empty term set — `clmulh` bit 63 — reduces to zero. Three XOR trees of the
same shape as the pre-existing `clmul` datapath, ~4100 gates each.

### Rotators (`ROL`, `ROR`, `ROLW`, `RORW`)

`ROL`/`ROR` are 6-stage 64-bit rotators (384 muxes each). `ROLW`/`RORW` rotate
the low 32 bits by `src2[4:0]` in 5 stages (160 muxes) and sign-extend the result.

### The rest

`SH1ADD`/`SH2ADD`/`SH3ADD` pre-shift `src1` by 1/2/3 (wiring plus 64 muxes) and
share one 64-bit ripple-carry adder. `ADD` and `SUB` have their own; the `SUB`
adder's carry-out is also the unsigned compare for `MIN`/`MAX`/`MINU`/`MAXU`.
`ANDN`/`ORN`/`XNOR` are per-bit gates; `BSET`/`BCLR`/`BINV`/`BEXT` decode a
one-hot mask from `src2[5:0]` and combine it with `src1` per bit.

## 5. Observed CPU-side port map of `u_fallback_seq`

The rewrite kept every port the CPU already drives; only the `wcs_*` ports were
dropped. Source of the values is unchanged.

| Port | Driven by |
| :--- | :--- |
| `start` | `fallback_seq_start = illegal_selected & ~any_active` |
| `pipeline_flush` | `pipeline_flush_comb` |
| `insn_*` | `ser_insn_*` (slot-muxed instruction register) |
| `pc_in_*` | `ser_pc_muxed_*` |
| `rs1_val_*` | `csr_rs1cap_reg_*` (CDB-snooped operand capture) |
| `rs2_val_*` | `ser_rs2cap_reg_*` |
| `rd_tag_in_*` | `ser_ophrd_*` (old physical destination tag) |
| `rob_empty`, `sb_empty` | ROB empty, `lsu_sb_empty` |
| `active` | `fallback_active` (suppresses fetch/decode) |
| `cdb_inject` | `fallback_cdb_inject`, also ORed into `all_drain_complete`, `csr_retire_valid_1` and `all_cdb_inject` |
| `cdb_tag_*`, `cdb_data_*` | CDB injection payload |
| `redir_valid`, `redir_pc_*` | fetch redirect on success |
| `trap_active` | `fallback_trap_active`, selects `csr_pc_reg` into the trap PC mux and starts `TrapSequencer` |
| `trap_cause_*`, `trap_val_*` | architectural `mcause`/`mtval` |

`start`, `insn`, `rs1_val`, `rs2_val` and `rd_tag_in` therefore needed no source
change on the CPU side.

`cdb_inject` pulses exactly once per emulated instruction: `done` is the last
micro-op and every routine has exactly one, so `minstret` is not double-counted.

## 6. `wcs_*` audit

The module header claimed a "TileLink TL-UH compatible WCS interface for host
inspection, locking and updates". Nothing implemented it:

* ports `wcs_write_en`, `wcs_write_addr_0..7`, `wcs_write_data_0..31`,
  `wcs_enable`, `wcs_lock` were inputs, `wcs_busy` an output;
* every one of them was tied to `zero` at the `u_fallback_seq` instantiation in
  `CPU.lean`, and `wcs_busy` drove `fallback_wcs_busy`, a wire with no reader;
* the module's `wcsGates` produced `wcs_ram_write_en`, `wcs_addr_buf_*` and
  `wcs_data_buf_*`, all dangling — no RAM instance, no read port, no write port;
* there was no control-store RAM, no SoC address range for one, and no
  `docs/` reference to a WCS.

The rewrite drops the ports and the gate group. A patchable control store would
need a new peripheral and an address map and is deliberately out of scope: the
control store here is read-only.

## 7. `dispatchZb` selector audit

The superseded `dispatchZb` matched Zb* encodings from raw fields. It is kept
here as a record of why the table-driven decoder replaced it.

| Selector | Compared | Should have compared | Consequence |
| :--- | :--- | :--- | :--- |
| `bseti` | `funct7 >>> 1 == 0x14` (i.e. funct7 ∈ {0x28,0x29}) | funct6 = 0x0A | never matched |
| `bclri` | `funct7 >>> 1 == 0x24` | funct6 = 0x12 | never matched |
| `bexti` | `funct7 >>> 1 == 0x24`, f3 = 5 | funct6 = 0x12 | never matched |
| `binvi` | `funct7 >>> 1 == 0x34` | funct6 = 0x1A | never matched |
| `rori` | `funct7 >>> 1 == 0x30`, f3 = 5 | funct6 = 0x18 | never matched |
| `rev8` | `funct7 == 0x34`, f3 = 5 | funct7 = 0x35 | never matched |

The six immediate selectors compared `insn[31:26]` against the *funct7*
constant, so they could only match encodings that do not exist; `rev8` used the
RV32 funct7. The remaining selectors (R-type forms, `clz`/`ctz`/`cpop`,
`orc.b`) were correct, but the hardware matched only 15 of them and had
datapaths for only 7, so `clz`, `ctz`, `cpop`, `orc.b`, `rev8`, `clmulh`,
`clmulr` and every immediate form trapped.

## 8. Sizes

| | before | after |
| :--- | ---: | ---: |
| inputs | 279 | 236 |
| outputs | 267 | 266 |
| instances | 5 | 5 |
| gates | 9 057 | 43 240 |

The growth is the control store (16 352 muxes) and the three carry-less
multiply datapaths (~12 300 gates). The counts are pinned by
`FallbackSequencerProofs.lean`.

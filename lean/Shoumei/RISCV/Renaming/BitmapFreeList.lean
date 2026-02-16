/-
RISCV/Renaming/BitmapFreeList.lean - Bitmap-Based Free Physical Register List

Replaces the FIFO free list with a dual-bitmap design that correctly handles
flush recovery. Two 64-bit bitmaps (bit i=1 → preg i is free):

- Speculative bitmap: alloc clears bit, retire sets bit, flush copies from committed
- Committed bitmap: commit_alloc clears bit, retire sets bit

Allocation uses a priority encoder (find-first-set via PriorityArbiter64)
followed by a one-hot-to-binary encoder (OneHotEncoder64) to produce a 6-bit
preg index.

This design avoids the FIFO flush bug where stale pregs in the RAM could be
re-allocated after flush, corrupting architecturally-live register mappings.
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.Arbiter
import Shoumei.Circuits.Combinational.OneHotEncoder

namespace Shoumei.RISCV.Renaming

open Shoumei
open Shoumei.Circuits.Combinational

/--
Build a Bitmap Free List circuit (64 pregs).

Ports:
- clock, reset
- enq_data[5:0], enq_valid — retire: set bit in BOTH bitmaps
- deq_ready — allocate request
- deq_data[5:0], deq_valid — allocated preg / available
- flush_en — speculative ← committed
- commit_alloc_en, commit_alloc_tag[5:0] — clear bit in committed bitmap
- enq_ready — always 1 (bitmap never "full")

Internals:
- 128 DFFs (64 speculative + 64 committed)
- Decoder6 × 3 (retire decode, alloc decode, commit_alloc decode)
- PriorityArbiter64 (find first free)
- OneHotEncoder64 (one-hot → binary)
- Per-bit next-state MUX chain
- Reset: bits 32-63 = 1 (DFF_SET), bits 0-31 = 0 (DFF)
-/
def mkBitmapFreeList64 : Circuit :=
  let n := 64
  let tagWidth := 6

  -- Input ports
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let enq_data := (List.range tagWidth).map (fun i => Wire.mk s!"enq_data_{i}")
  let enq_valid := Wire.mk "enq_valid"
  let deq_ready := Wire.mk "deq_ready"
  let flush_en := Wire.mk "flush_en"
  let commit_alloc_en := Wire.mk "commit_alloc_en"
  let commit_alloc_tag := (List.range tagWidth).map (fun i => Wire.mk s!"commit_alloc_tag_{i}")

  -- Output ports
  let enq_ready := Wire.mk "enq_ready"
  let deq_data := (List.range tagWidth).map (fun i => Wire.mk s!"deq_data_{i}")
  let deq_valid := Wire.mk "deq_valid"

  -- enq_ready is always 1 (bitmap can always accept retires)
  -- We need a constant 1. Use a trick: NOT(reset AND NOT(reset)) won't work.
  -- Actually we can just tie it. Let's use a BUF from a "one" input.
  let one := Wire.mk "one"
  let zero := Wire.mk "zero"
  let enq_ready_gate := Gate.mkBUF one enq_ready

  -- === Decoder instances ===

  -- Retire decoder: decode enq_data to one-hot for setting bits
  let retire_dec_out := (List.range n).map (fun i => Wire.mk s!"retire_dec_{i}")
  let retire_dec_inst : CircuitInstance := {
    moduleName := "Decoder6"
    instName := "u_retire_dec"
    portMap :=
      (enq_data.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (retire_dec_out.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- Alloc decoder: decode deq_data to one-hot for clearing bits in speculative
  let alloc_dec_out := (List.range n).map (fun i => Wire.mk s!"alloc_dec_{i}")
  let alloc_dec_inst : CircuitInstance := {
    moduleName := "Decoder6"
    instName := "u_alloc_dec"
    portMap :=
      (deq_data.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (alloc_dec_out.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- Commit-alloc decoder: decode commit_alloc_tag for clearing bits in committed
  let commit_dec_out := (List.range n).map (fun i => Wire.mk s!"commit_dec_{i}")
  let commit_dec_inst : CircuitInstance := {
    moduleName := "Decoder6"
    instName := "u_commit_dec"
    portMap :=
      (commit_alloc_tag.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (commit_dec_out.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- === Priority arbiter: find first free bit in speculative bitmap ===
  let spec_bitmap := (List.range n).map (fun i => Wire.mk s!"spec_{i}")
  let arb_grant := (List.range n).map (fun i => Wire.mk s!"arb_grant_{i}")
  let arb_valid := Wire.mk "arb_valid"  -- any free preg available

  let arb_inst : CircuitInstance := {
    moduleName := "PriorityArbiter64"
    instName := "u_arbiter"
    portMap :=
      (spec_bitmap.enum.map (fun ⟨i, w⟩ => (s!"request_{i}", w))) ++
      (arb_grant.enum.map (fun ⟨i, w⟩ => (s!"grant_{i}", w))) ++
      [("valid", arb_valid)]
  }

  -- === One-hot encoder: convert grant to binary index ===
  let enc_out := (List.range tagWidth).map (fun i => Wire.mk s!"enc_out_{i}")
  let enc_inst : CircuitInstance := {
    moduleName := "OneHotEncoder64"
    instName := "u_encoder"
    portMap :=
      (arb_grant.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (enc_out.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- deq_valid = arb_valid (free pregs available)
  let deq_valid_gate := Gate.mkBUF arb_valid deq_valid

  -- deq_data = encoder output
  let deq_data_gates := (List.range tagWidth).map (fun i =>
    Gate.mkBUF (enc_out[i]!) (deq_data[i]!))

  -- === Speculative bitmap DFFs and next-state logic ===
  -- For each bit i:
  --   retire_set_i = enq_valid AND retire_dec[i]
  --   alloc_clr_i = deq_ready AND alloc_dec[i]  (only when actually dequeuing)
  --   commit_set_i = enq_valid AND retire_dec[i]  (same as retire, both bitmaps)
  --   commit_clr_i = commit_alloc_en AND commit_dec[i]
  --
  -- Speculative next:
  --   if flush_en: committed[i]
  --   elif retire_set_i: 1
  --   elif alloc_clr_i: 0
  --   else: spec[i]
  --
  -- Committed next:
  --   if retire_set_i: 1
  --   elif commit_clr_i: 0
  --   else: committed[i]

  let committed_bitmap := (List.range n).map (fun i => Wire.mk s!"comm_{i}")

  -- alloc_fire = deq_ready AND arb_valid (actually allocating)
  let alloc_fire := Wire.mk "alloc_fire"
  let alloc_fire_gate := Gate.mkAND deq_ready arb_valid alloc_fire

  let perBitGates := (List.range n).foldl (fun acc i =>
    let retire_set := Wire.mk s!"ret_set_{i}"
    let alloc_clr := Wire.mk s!"alloc_clr_{i}"
    let commit_clr := Wire.mk s!"comm_clr_{i}"
    let spec_next := Wire.mk s!"spec_nx_{i}"
    let comm_next := Wire.mk s!"comm_nx_{i}"

    -- retire_set = enq_valid AND retire_dec[i]
    let g1 := Gate.mkAND enq_valid (retire_dec_out[i]!) retire_set
    -- alloc_clr = alloc_fire AND alloc_dec[i]
    let g2 := Gate.mkAND alloc_fire (alloc_dec_out[i]!) alloc_clr
    -- commit_clr = commit_alloc_en AND commit_dec[i]
    let g3 := Gate.mkAND commit_alloc_en (commit_dec_out[i]!) commit_clr

    -- Speculative next-state:
    -- m1 = MUX(spec[i], zero, alloc_clr)   -- if alloc_clr: 0, else spec[i]
    -- m2 = MUX(m1, one, retire_set)        -- if retire_set: 1, else m1
    -- spec_next = MUX(m2, comm[i], flush_en) -- if flush_en: comm[i], else m2
    let m1 := Wire.mk s!"spec_m1_{i}"
    let m2 := Wire.mk s!"spec_m2_{i}"
    let g4 := Gate.mkMUX (spec_bitmap[i]!) zero alloc_clr m1
    let g5 := Gate.mkMUX m1 one retire_set m2
    let g6 := Gate.mkMUX m2 (committed_bitmap[i]!) flush_en spec_next

    -- Committed next-state:
    -- cm1 = MUX(comm[i], zero, commit_clr)  -- if commit_clr: 0, else comm[i]
    -- comm_next = MUX(cm1, one, retire_set) -- if retire_set: 1, else cm1
    let cm1 := Wire.mk s!"comm_m1_{i}"
    let g7 := Gate.mkMUX (committed_bitmap[i]!) zero commit_clr cm1
    let g8 := Gate.mkMUX cm1 one retire_set comm_next

    -- DFFs: bits 32-63 reset to 1 (free), bits 0-31 reset to 0 (allocated)
    let spec_dff := if i >= 32 then
      Gate.mkDFF_SET spec_next clock reset (spec_bitmap[i]!)
    else
      Gate.mkDFF spec_next clock reset (spec_bitmap[i]!)
    let comm_dff := if i >= 32 then
      Gate.mkDFF_SET comm_next clock reset (committed_bitmap[i]!)
    else
      Gate.mkDFF comm_next clock reset (committed_bitmap[i]!)

    acc ++ [g1, g2, g3, g4, g5, g6, g7, g8, spec_dff, comm_dff]
  ) []

  { name := "BitmapFreeList_64"
    inputs := [clock, reset, zero, one] ++
              enq_data ++ [enq_valid] ++
              [deq_ready] ++
              [flush_en] ++
              [commit_alloc_en] ++ commit_alloc_tag
    outputs := [enq_ready] ++
               deq_data ++ [deq_valid]
    gates := [enq_ready_gate, deq_valid_gate, alloc_fire_gate] ++
             deq_data_gates ++ perBitGates
    instances := [retire_dec_inst, alloc_dec_inst, commit_dec_inst, arb_inst, enc_inst]
    signalGroups := [
      { name := "enq_data", width := tagWidth, wires := enq_data },
      { name := "deq_data", width := tagWidth, wires := deq_data },
      { name := "commit_alloc_tag", width := tagWidth, wires := commit_alloc_tag },
      { name := "spec", width := n, wires := spec_bitmap },
      { name := "comm", width := n, wires := committed_bitmap }
    ]
  }

end Shoumei.RISCV.Renaming

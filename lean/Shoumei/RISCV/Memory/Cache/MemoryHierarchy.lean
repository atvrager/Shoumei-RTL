/-
RISCV/Memory/Cache/MemoryHierarchy.lean - Top-level Memory Hierarchy

Composes L1I + L1D + L2 caches into a complete memory hierarchy.
Behavioral model for end-to-end reasoning + structural circuit via CircuitInstance.

External interface: L2-miss bus to main memory.
-/

import Shoumei.DSL
import Shoumei.RISCV.Memory.Cache.CacheTypes
import Shoumei.RISCV.Memory.Cache.L1ICache
import Shoumei.RISCV.Memory.Cache.L1DCache
import Shoumei.RISCV.Memory.Cache.L2Cache

namespace Shoumei.RISCV.Memory.Cache

open Shoumei

/-! ## Behavioral Model -/

/-- Combined memory hierarchy state. -/
structure MemHierarchyState where
  l1i : L1ICacheState
  l1d : L1DCacheState
  l2  : L2CacheState

instance : Inhabited MemHierarchyState where
  default := {
    l1i := L1ICacheState.empty
    l1d := L1DCacheState.empty
    l2 := L2CacheState.empty
  }

def MemHierarchyState.empty : MemHierarchyState := default

/-- Store a word through the hierarchy (SB → L1D). -/
def MemHierarchyState.storeToL1D (s : MemHierarchyState) (addr : UInt32) (val : UInt32)
    : MemHierarchyState :=
  match s.l1d.write addr val with
  | some l1d' => { s with l1d := l1d' }
  | none => s  -- miss: would need refill first (simplified)

/-- Execute FENCE.I: drain SB (assumed), write back dirty L1D lines to L2, invalidate L1I. -/
def MemHierarchyState.executeFenceI (s : MemHierarchyState) : MemHierarchyState :=
  -- 1. Write back all dirty L1D lines to L2
  let dirtyLines := s.l1d.getAllDirtyLines
  let l2' := dirtyLines.foldl (fun l2 (addr, data) => l2.writeBack addr data) s.l2
  -- 2. Clear dirty bits in L1D
  let l1d' := s.l1d.clearAllDirty
  -- 3. Invalidate all L1I lines
  let l1i' := s.l1i.invalidateAll
  { l1i := l1i', l1d := l1d', l2 := l2' }

/-- Fetch from L1I (simplified: assumes line is available after refill). -/
def MemHierarchyState.fetchFromL1I (s : MemHierarchyState) (addr : UInt32)
    : MemHierarchyState × Option UInt32 :=
  match s.l1i.lookup addr with
  | some word => (s, some word)
  | none =>
    -- L1I miss: check L2
    match s.l2.lookup addr with
    | some (_way, lineData) =>
      -- L2 hit: refill L1I
      let l1i' := s.l1i.refill addr lineData
      let word := lineData (extractWordOffset addr)
      ({ s with l1i := l1i' }, some word)
    | none =>
      -- L2 miss: would need main memory (simplified: return none)
      (s, none)

/-! ## Structural Circuit -/

/-- Top-level memory hierarchy circuit.

    Composes L1I, L1D, and L2 via CircuitInstance.

    CPU-facing ports:
    - Fetch: ifetch_valid, ifetch_addr[31:0] → ifetch_data[31:0], ifetch_stall
    - Load/Store: dmem_req_valid, dmem_req_we, dmem_req_addr[31:0],
                  dmem_req_wdata[31:0], dmem_req_size[1:0]
                  → dmem_resp_valid, dmem_resp_data[31:0], dmem_stall

    External memory ports:
    - mem_req_valid, mem_req_addr[31:0], mem_req_we, mem_req_data[255:0]
    - mem_resp_valid, mem_resp_data[255:0]

    Control:
    - fence_i, fence_i_busy
-/
def mkMemoryHierarchy : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"

  -- Fetch interface
  let ifetch_valid := Wire.mk "ifetch_valid"
  let ifetch_addr := (List.range 32).map fun i => Wire.mk s!"ifetch_addr_{i}"
  let ifetch_data := (List.range 32).map fun i => Wire.mk s!"ifetch_data_{i}"
  let ifetch_data_1 := (List.range 32).map fun i => Wire.mk s!"ifetch_data_1_{i}"
  let ifetch_stall := Wire.mk "ifetch_stall"

  -- Data interface
  let dmem_req_valid := Wire.mk "dmem_req_valid"
  let dmem_req_we := Wire.mk "dmem_req_we"
  let dmem_req_addr := (List.range 32).map fun i => Wire.mk s!"dmem_req_addr_{i}"
  let dmem_req_wdata := (List.range 32).map fun i => Wire.mk s!"dmem_req_wdata_{i}"
  let dmem_req_size := (List.range 2).map fun i => Wire.mk s!"dmem_req_size_{i}"
  let dmem_resp_valid := Wire.mk "dmem_resp_valid"
  let dmem_resp_data := (List.range 32).map fun i => Wire.mk s!"dmem_resp_data_{i}"
  let dmem_stall := Wire.mk "dmem_stall"

  -- External memory interface
  let mem_req_valid := Wire.mk "mem_req_valid"
  let mem_req_addr := (List.range 32).map fun i => Wire.mk s!"mem_req_addr_{i}"
  let mem_req_we := Wire.mk "mem_req_we"
  let mem_req_data := (List.range 256).map fun i => Wire.mk s!"mem_req_data_{i}"
  let mem_resp_valid := Wire.mk "mem_resp_valid"
  let mem_resp_data := (List.range 256).map fun i => Wire.mk s!"mem_resp_data_{i}"

  let fence_i := Wire.mk "fence_i"
  let fence_i_busy := Wire.mk "fence_i_busy"

  -- Internal wires: L1I ↔ L2
  let l1i_miss_valid := Wire.mk "l1i_miss_valid"
  let l1i_miss_addr := (List.range 32).map fun i => Wire.mk s!"l1i_miss_addr_{i}"
  let l1i_refill_valid := Wire.mk "l1i_refill_valid"
  let l1i_refill_data := (List.range 256).map fun i => Wire.mk s!"l1i_refill_data_{i}"

  -- Internal wires: L1D ↔ L2
  let l1d_miss_valid := Wire.mk "l1d_miss_valid"
  let l1d_miss_addr := (List.range 32).map fun i => Wire.mk s!"l1d_miss_addr_{i}"
  let l1d_refill_valid := Wire.mk "l1d_refill_valid"
  let l1d_refill_data := (List.range 256).map fun i => Wire.mk s!"l1d_refill_data_{i}"
  let l1d_wb_valid := Wire.mk "l1d_wb_valid"
  let l1d_wb_addr := (List.range 32).map fun i => Wire.mk s!"l1d_wb_addr_{i}"
  let l1d_wb_data := (List.range 256).map fun i => Wire.mk s!"l1d_wb_data_{i}"
  let l1d_wb_ack := Wire.mk "l1d_wb_ack"

  -- L1I Cache instance
  let l1i_inst := CircuitInstance.mk "L1ICache" "u_l1i"
    ([("clock", clock), ("reset", reset), ("req_valid", ifetch_valid)] ++
     (List.range 32).map (fun i => (s!"req_addr_{i}", ifetch_addr[i]!)) ++
     [("refill_valid", l1i_refill_valid)] ++
     (List.range 256).map (fun i => (s!"refill_data_{i}", l1i_refill_data[i]!)) ++
     [("fence_i", fence_i),
      ("resp_valid", Wire.mk "l1i_resp_valid")] ++
     (List.range 32).map (fun i => (s!"resp_data_{i}", ifetch_data[i]!)) ++
     (List.range 32).map (fun i => (s!"resp_data_1_{i}", ifetch_data_1[i]!)) ++
     [("miss_valid", l1i_miss_valid)] ++
     (List.range 32).map (fun i => (s!"miss_addr_{i}", l1i_miss_addr[i]!)) ++
     [("stall", ifetch_stall)])

  -- L1D Cache instance
  let l1d_inst := CircuitInstance.mk "L1DCache" "u_l1d"
    ([("clock", clock), ("reset", reset),
      ("req_valid", dmem_req_valid), ("req_we", dmem_req_we)] ++
     (List.range 32).map (fun i => (s!"req_addr_{i}", dmem_req_addr[i]!)) ++
     (List.range 32).map (fun i => (s!"req_wdata_{i}", dmem_req_wdata[i]!)) ++
     (List.range 2).map (fun i => (s!"req_size_{i}", dmem_req_size[i]!)) ++
     [("refill_valid", l1d_refill_valid)] ++
     (List.range 256).map (fun i => (s!"refill_data_{i}", l1d_refill_data[i]!)) ++
     [("wb_ack", l1d_wb_ack), ("fence_i", fence_i),
      ("resp_valid", dmem_resp_valid)] ++
     (List.range 32).map (fun i => (s!"resp_data_{i}", dmem_resp_data[i]!)) ++
     [("miss_valid", l1d_miss_valid)] ++
     (List.range 32).map (fun i => (s!"miss_addr_{i}", l1d_miss_addr[i]!)) ++
     [("wb_valid", l1d_wb_valid)] ++
     (List.range 32).map (fun i => (s!"wb_addr_{i}", l1d_wb_addr[i]!)) ++
     (List.range 256).map (fun i => (s!"wb_data_{i}", l1d_wb_data[i]!)) ++
     [("stall", dmem_stall), ("fence_i_busy", fence_i_busy)])

  -- L2 Cache instance
  let l2_inst := CircuitInstance.mk "L2Cache" "u_l2"
    ([("clock", clock), ("reset", reset),
      ("l1i_req_valid", l1i_miss_valid)] ++
     (List.range 32).map (fun i => (s!"l1i_req_addr_{i}", l1i_miss_addr[i]!)) ++
     [("l1d_req_valid", l1d_miss_valid)] ++
     (List.range 32).map (fun i => (s!"l1d_req_addr_{i}", l1d_miss_addr[i]!)) ++
     [("l1d_req_we", l1d_wb_valid)] ++
     (List.range 256).map (fun i => (s!"l1d_req_data_{i}", l1d_wb_data[i]!)) ++
     [("mem_resp_valid", mem_resp_valid)] ++
     (List.range 256).map (fun i => (s!"mem_resp_data_{i}", mem_resp_data[i]!)) ++
     [("l1i_resp_valid", l1i_refill_valid)] ++
     (List.range 256).map (fun i => (s!"l1i_resp_data_{i}", l1i_refill_data[i]!)) ++
     [("l1d_resp_valid", l1d_refill_valid)] ++
     (List.range 256).map (fun i => (s!"l1d_resp_data_{i}", l1d_refill_data[i]!)) ++
     [("mem_req_valid", mem_req_valid)] ++
     (List.range 32).map (fun i => (s!"mem_req_addr_{i}", mem_req_addr[i]!)) ++
     [("mem_req_we", mem_req_we)] ++
     (List.range 256).map (fun i => (s!"mem_req_data_{i}", mem_req_data[i]!)) ++
     [("stall_i", Wire.mk "l2_stall_i"),
      ("stall_d", Wire.mk "l2_stall_d")])

  { name := "MemoryHierarchy"
    inputs := [clock, reset, ifetch_valid] ++ ifetch_addr ++
              [dmem_req_valid, dmem_req_we] ++ dmem_req_addr ++ dmem_req_wdata ++ dmem_req_size ++
              [mem_resp_valid] ++ mem_resp_data ++ [fence_i]
    outputs := ifetch_data ++ ifetch_data_1 ++ [ifetch_stall,
               dmem_resp_valid] ++ dmem_resp_data ++ [dmem_stall] ++
               [mem_req_valid] ++ mem_req_addr ++ [mem_req_we] ++ mem_req_data ++
               [fence_i_busy]
    gates := []  -- Pure hierarchical composition
    instances := [l1i_inst, l1d_inst, l2_inst]
    signalGroups := [
      { name := "ifetch_addr", width := 32, wires := ifetch_addr },
      { name := "ifetch_data", width := 32, wires := ifetch_data },
      { name := "ifetch_data_1", width := 32, wires := ifetch_data_1 },
      { name := "dmem_req_addr", width := 32, wires := dmem_req_addr },
      { name := "dmem_req_wdata", width := 32, wires := dmem_req_wdata },
      { name := "dmem_req_size", width := 2, wires := dmem_req_size },
      { name := "dmem_resp_data", width := 32, wires := dmem_resp_data },
      { name := "mem_req_addr", width := 32, wires := mem_req_addr },
      { name := "mem_req_data", width := 256, wires := mem_req_data },
      { name := "mem_resp_data", width := 256, wires := mem_resp_data }
    ]
    keepHierarchy := true
  }

end Shoumei.RISCV.Memory.Cache

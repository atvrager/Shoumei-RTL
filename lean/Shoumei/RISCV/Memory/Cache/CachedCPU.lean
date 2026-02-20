/-
RISCV/Memory/Cache/CachedCPU.lean - CPU + Cache Hierarchy Wrapper

Composes the CPU core with the L1I + L1D + L2 memory hierarchy.
The external interface changes from raw IMEM/DMEM buses to L2-miss memory bus.

CPU-facing connections (internal):
- CPU fetch_pc → MemHierarchy ifetch_addr
- MemHierarchy ifetch_data → CPU imem_resp_data
- CPU dmem_req_* → MemHierarchy dmem_req_*
- MemHierarchy dmem_resp_* → CPU dmem_resp_*
- CPU fence_i → MemHierarchy fence_i
- MemHierarchy ifetch_stall → CPU fetch_stall (OR'd into existing stall chain)

External interface:
- mem_req_valid/addr/we/data → main memory request
- mem_resp_valid/data → main memory response
- RVVI trace outputs (passed through from CPU)
-/

import Shoumei.DSL
import Shoumei.RISCV.Config
import Shoumei.RISCV.Memory.Cache.MemoryHierarchy

namespace Shoumei.RISCV.Memory.Cache

open Shoumei
open Shoumei.RISCV

private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map fun i => Wire.mk s!"{name}_{i}"

/-- CachedCPU: CPU core + L1I/L1D/L2 memory hierarchy.

    External ports:
    - Inputs: clock, reset, zero, one, mem_resp_valid, mem_resp_data[255:0]
    - Outputs: mem_req_valid, mem_req_addr[31:0], mem_req_we, mem_req_data[255:0],
               rob_empty, RVVI trace signals, fflags_acc[4:0]
-/
def mkCachedCPU (config : CPUConfig) : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- External memory interface (L2 miss bus)
  let mem_resp_valid := Wire.mk "mem_resp_valid"
  let mem_resp_data := makeIndexedWires "mem_resp_data" 256
  let mem_req_valid := Wire.mk "mem_req_valid"
  let mem_req_addr := makeIndexedWires "mem_req_addr" 32
  let mem_req_we := Wire.mk "mem_req_we"
  let mem_req_data := makeIndexedWires "mem_req_data" 256

  -- Internal wires: CPU ↔ MemoryHierarchy
  let fetch_pc := makeIndexedWires "cpu_fetch_pc" 32
  let fetch_stalled := Wire.mk "cpu_fetch_stalled"
  let global_stall_out := Wire.mk "cpu_global_stall_out"
  let imem_resp_data := makeIndexedWires "cpu_imem_resp_data" 32

  let dmem_req_valid := Wire.mk "cpu_dmem_req_valid"
  let dmem_req_we := Wire.mk "cpu_dmem_req_we"
  let dmem_req_addr := makeIndexedWires "cpu_dmem_req_addr" 32
  let dmem_req_data := makeIndexedWires "cpu_dmem_req_data" 32
  let dmem_req_size := makeIndexedWires "cpu_dmem_req_size" 2
  let dmem_resp_valid := Wire.mk "cpu_dmem_resp_valid"
  let dmem_resp_data := makeIndexedWires "cpu_dmem_resp_data" 32

  -- Cache stall signals
  let ifetch_stall := Wire.mk "cache_ifetch_stall"
  let dmem_stall := Wire.mk "cache_dmem_stall"
  let fence_i_busy := Wire.mk "cache_fence_i_busy"

  -- dmem_req_ready: driven by NOT dmem_stall
  let dmem_req_ready := Wire.mk "cpu_dmem_req_ready"
  let not_dmem_stall := Wire.mk "not_dmem_stall"

  -- CPU pass-through outputs
  let rob_empty := Wire.mk "rob_empty"
  let rvvi_valid := Wire.mk "rvvi_valid"
  let rvvi_trap := Wire.mk "rvvi_trap"
  let rvvi_pc_rdata := makeIndexedWires "rvvi_pc_rdata" 32
  let rvvi_insn := makeIndexedWires "rvvi_insn" 32
  let rvvi_rd := makeIndexedWires "rvvi_rd" 5
  let rvvi_rd_valid := Wire.mk "rvvi_rd_valid"
  let rvvi_rd_data := makeIndexedWires "rvvi_rd_data" 32
  let rvvi_frd := makeIndexedWires "rvvi_frd" 5
  let rvvi_frd_valid := Wire.mk "rvvi_frd_valid"
  let rvvi_frd_data := makeIndexedWires "rvvi_frd_data" 32
  let fflags_acc := makeIndexedWires "fflags_acc" 5

  -- Store snoop outputs (for testbench tohost detection)
  let store_snoop_valid := Wire.mk "store_snoop_valid"
  let store_snoop_addr := makeIndexedWires "store_snoop_addr" 32
  let store_snoop_data := makeIndexedWires "store_snoop_data" 32

  -- FENCE.I signal from CPU to cache hierarchy
  -- CPU exports fence_i_drain_complete: pulses when FENCE.I pipeline drain completes
  let fence_i := Wire.mk "fence_i_signal"

  -- Gate: dmem_req_ready = NOT dmem_stall
  let stall_gate := Gate.mkNOT dmem_stall not_dmem_stall
  let ready_gate := Gate.mkBUF not_dmem_stall dmem_req_ready

  -- Store snoop gates
  let snoop_valid_gate := Gate.mkAND dmem_req_valid dmem_req_we store_snoop_valid
  let snoop_addr_gates := (List.range 32).map fun i =>
    Gate.mkBUF dmem_req_addr[i]! store_snoop_addr[i]!
  let snoop_data_gates := (List.range 32).map fun i =>
    Gate.mkBUF dmem_req_data[i]! store_snoop_data[i]!

  -- CPU instance
  let cpu_inst := CircuitInstance.mk s!"CPU_{config.isaString}" "u_cpu"
    ([("clock", clock), ("reset", reset), ("zero", zero), ("one", one),
      ("fetch_stall_ext", ifetch_stall),
      ("dmem_stall_ext", dmem_stall)] ++
     (List.range 32).map (fun i => (s!"imem_resp_data_{i}", imem_resp_data[i]!)) ++
     [("dmem_req_ready", dmem_req_ready),
      ("dmem_resp_valid", dmem_resp_valid)] ++
     (List.range 32).map (fun i => (s!"dmem_resp_data_{i}", dmem_resp_data[i]!)) ++
     -- CPU outputs
     (List.range 32).map (fun i => (s!"fetch_pc_{i}", fetch_pc[i]!)) ++
     [("fetch_stalled", fetch_stalled),
      ("global_stall_out", global_stall_out),
      ("dmem_req_valid", dmem_req_valid),
      ("dmem_req_we", dmem_req_we)] ++
     (List.range 32).map (fun i => (s!"dmem_req_addr_{i}", dmem_req_addr[i]!)) ++
     (List.range 32).map (fun i => (s!"dmem_req_data_{i}", dmem_req_data[i]!)) ++
     (List.range 2).map (fun i => (s!"dmem_req_size_{i}", dmem_req_size[i]!)) ++
     [("rob_empty", rob_empty), ("fence_i_drain_complete", fence_i)] ++
     -- RVVI
     [("rvvi_valid", rvvi_valid), ("rvvi_trap", rvvi_trap)] ++
     (List.range 32).map (fun i => (s!"rvvi_pc_rdata_{i}", rvvi_pc_rdata[i]!)) ++
     (List.range 32).map (fun i => (s!"rvvi_insn_{i}", rvvi_insn[i]!)) ++
     (List.range 5).map (fun i => (s!"rvvi_rd_{i}", rvvi_rd[i]!)) ++
     [("rvvi_rd_valid", rvvi_rd_valid)] ++
     (List.range 32).map (fun i => (s!"rvvi_rd_data_{i}", rvvi_rd_data[i]!)) ++
     (List.range 5).map (fun i => (s!"rvvi_frd_{i}", rvvi_frd[i]!)) ++
     [("rvvi_frd_valid", rvvi_frd_valid)] ++
     (List.range 32).map (fun i => (s!"rvvi_frd_data_{i}", rvvi_frd_data[i]!)) ++
     (List.range 5).map (fun i => (s!"fflags_acc_{i}", fflags_acc[i]!)))

  -- MemoryHierarchy instance
  -- ifetch_valid: always 1 — CPU always presents fetch_pc, L1I always checks.
  -- This breaks the stall→ifetch_valid→req_valid feedback loop that caused
  -- the CPU to advance past un-fetched instructions.
  let ifetch_valid := Wire.mk "ifetch_valid"
  let ifetch_valid_gate := Gate.mkBUF one ifetch_valid

  let memhier_inst := CircuitInstance.mk "MemoryHierarchy" "u_memhier"
    ([("clock", clock), ("reset", reset),
      ("ifetch_valid", ifetch_valid)] ++
     (List.range 32).map (fun i => (s!"ifetch_addr_{i}", fetch_pc[i]!)) ++
     [("dmem_req_valid", dmem_req_valid),
      ("dmem_req_we", dmem_req_we)] ++
     (List.range 32).map (fun i => (s!"dmem_req_addr_{i}", dmem_req_addr[i]!)) ++
     (List.range 32).map (fun i => (s!"dmem_req_wdata_{i}", dmem_req_data[i]!)) ++
     (List.range 2).map (fun i => (s!"dmem_req_size_{i}", dmem_req_size[i]!)) ++
     [("mem_resp_valid", mem_resp_valid)] ++
     (List.range 256).map (fun i => (s!"mem_resp_data_{i}", mem_resp_data[i]!)) ++
     [("fence_i", fence_i)] ++
     -- MemHierarchy outputs
     (List.range 32).map (fun i => (s!"ifetch_data_{i}", imem_resp_data[i]!)) ++
     [("ifetch_stall", ifetch_stall),
      ("dmem_resp_valid", dmem_resp_valid)] ++
     (List.range 32).map (fun i => (s!"dmem_resp_data_{i}", dmem_resp_data[i]!)) ++
     [("dmem_stall", dmem_stall),
      ("mem_req_valid", mem_req_valid)] ++
     (List.range 32).map (fun i => (s!"mem_req_addr_{i}", mem_req_addr[i]!)) ++
     [("mem_req_we", mem_req_we)] ++
     (List.range 256).map (fun i => (s!"mem_req_data_{i}", mem_req_data[i]!)) ++
     [("fence_i_busy", fence_i_busy)])

  { name := s!"CPU_{config.isaString}_{config.cacheString}"
    inputs := [clock, reset, zero, one, mem_resp_valid] ++ mem_resp_data
    outputs := [mem_req_valid] ++ mem_req_addr ++ [mem_req_we] ++ mem_req_data ++
               [rob_empty, store_snoop_valid] ++ store_snoop_addr ++ store_snoop_data ++
               [rvvi_valid, rvvi_trap] ++ rvvi_pc_rdata ++ rvvi_insn ++
               rvvi_rd ++ [rvvi_rd_valid] ++ rvvi_rd_data ++
               rvvi_frd ++ [rvvi_frd_valid] ++ rvvi_frd_data ++
               fflags_acc
    gates := [stall_gate, ready_gate, ifetch_valid_gate, snoop_valid_gate] ++
             snoop_addr_gates ++ snoop_data_gates
    instances := [cpu_inst, memhier_inst]
    signalGroups := [
      { name := "mem_resp_data", width := 256, wires := mem_resp_data },
      { name := "mem_req_addr", width := 32, wires := mem_req_addr },
      { name := "mem_req_data", width := 256, wires := mem_req_data },
      { name := "rvvi_pc_rdata", width := 32, wires := rvvi_pc_rdata },
      { name := "rvvi_insn", width := 32, wires := rvvi_insn },
      { name := "rvvi_rd", width := 5, wires := rvvi_rd },
      { name := "rvvi_rd_data", width := 32, wires := rvvi_rd_data },
      { name := "rvvi_frd", width := 5, wires := rvvi_frd },
      { name := "rvvi_frd_data", width := 32, wires := rvvi_frd_data },
      { name := "fflags_acc", width := 5, wires := fflags_acc },
      { name := "store_snoop_addr", width := 32, wires := store_snoop_addr },
      { name := "store_snoop_data", width := 32, wires := store_snoop_data }
    ]
    keepHierarchy := true
  }

end Shoumei.RISCV.Memory.Cache

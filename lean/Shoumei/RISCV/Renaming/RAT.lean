/-
RISCV/Renaming/RAT.lean - Register Alias Table

Maps 32 architectural registers to 64 physical registers (6-bit tags).
Used in Tomasulo out-of-order execution for register renaming.

Design:
- 32 entries, each 6 bits wide (physical register tag)
- 2 read ports (for rs1, rs2 lookup)
- 1 write port (for rd allocation)
- Synchronous reset to identity mapping (arch reg i → phys reg i)

Structural components:
- Storage: 32 × 6-bit DFF registers
- Write decoder: Decoder5 (5→32 one-hot)
- Read mux 1: Mux32x6 (32:1, 6-bit wide) for rs1
- Read mux 2: Mux32x6 (32:1, 6-bit wide) for rs2
- Write enable: AND(write_en, decoder output) per entry
- Write data MUX: select between reset value and write data
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Circuits.Sequential.DFF

namespace Shoumei.RISCV.Renaming

open Shoumei
open Shoumei.Circuits.Combinational

/-! ## Behavioral Model -/

/-- RAT state: mapping from 32 architectural registers to physical registers -/
structure RATState (numPhysRegs : Nat) where
  /-- Current mapping: architectural register → physical register tag -/
  mapping : Fin 32 → Fin numPhysRegs

/-- Look up the physical register mapped to an architectural register -/
def RATState.lookup (rat : RATState n) (archReg : Fin 32) : Fin n :=
  rat.mapping archReg

/-- Allocate: map an architectural register to a new physical register -/
def RATState.allocate (rat : RATState n) (archReg : Fin 32) (physReg : Fin n) : RATState n :=
  { mapping := fun r => if r == archReg then physReg else rat.mapping r }

/-- Initialize RAT with identity mapping (arch reg i → phys reg i) -/
def RATState.init (h : n ≥ 32) : RATState n :=
  { mapping := fun r => ⟨r.val, Nat.lt_of_lt_of_le r.isLt h⟩ }

/-- Look up two registers at once (common operation for rs1, rs2) -/
def RATState.lookupPair (rat : RATState n) (rs1 rs2 : Fin 32) : Fin n × Fin n :=
  (rat.lookup rs1, rat.lookup rs2)

/-! ## Structural Circuit -/

/-- Helper: Compute log2 ceiling -/
private def log2Ceil (n : Nat) : Nat :=
  if n <= 1 then 0
  else Nat.log2 n + (if 2^(Nat.log2 n) < n then 1 else 0)

/-- Helper: convert nat to fixed-width binary (LSB first) -/
private def natToBits (n : Nat) (width : Nat) : List Bool :=
  (List.range width).map (fun i => (n >>> i) % 2 == 1)

/--
Build a Register Alias Table circuit.

Parameters:
- numPhysRegs: Number of physical registers (default 64, giving 6-bit tags)

Ports:
- Inputs: clock, reset, write_en, write_addr[4:0], write_data[tagWidth-1:0],
          rs1_addr[4:0], rs2_addr[4:0],
          restore_en, restore_data_{i}_{j} (32×6 = 192 wires)
- Outputs: rs1_data[tagWidth-1:0], rs2_data[tagWidth-1:0],
           dump_data_{i}_{j} (32×6 = 192 wires — direct DFF Q readout)

Architecture:
- 32 × tagWidth DFF registers with synchronous reset to identity mapping
- Decoder5 for write address decode
- Two Mux32x6 for read ports
-/
def mkRAT (numPhysRegs : Nat := 64) : Circuit :=
  let tagWidth := log2Ceil numPhysRegs  -- 6 for 64 phys regs
  let numArchRegs := 32
  let addrWidth := 5   -- log2(32) = 5

  -- Inputs
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let write_en := Wire.mk "write_en"
  let write_addr := (List.range addrWidth).map (fun i => Wire.mk s!"write_addr_{i}")
  let write_data := (List.range tagWidth).map (fun i => Wire.mk s!"write_data_{i}")
  let rs1_addr := (List.range addrWidth).map (fun i => Wire.mk s!"rs1_addr_{i}")
  let rs2_addr := (List.range addrWidth).map (fun i => Wire.mk s!"rs2_addr_{i}")
  let rs3_addr := (List.range addrWidth).map (fun i => Wire.mk s!"rs3_addr_{i}")
  -- Bulk restore: on restore_en, all 32 entries are overwritten from restore_data
  let restore_en := Wire.mk "restore_en"
  let restore_data := (List.range numArchRegs).map (fun i =>
    (List.range tagWidth).map (fun j => Wire.mk s!"restore_data_{i}_{j}"))

  -- Outputs
  let rs1_data := (List.range tagWidth).map (fun i => Wire.mk s!"rs1_data_{i}")
  let rs2_data := (List.range tagWidth).map (fun i => Wire.mk s!"rs2_data_{i}")
  let rs3_data := (List.range tagWidth).map (fun i => Wire.mk s!"rs3_data_{i}")
  -- Fourth read port: old mapping for write_addr (before write, for ROB oldPhysRd tracking)
  let old_rd_data := (List.range tagWidth).map (fun i => Wire.mk s!"old_rd_data_{i}")
  -- Dump: direct DFF Q readout for all 32 entries (for committed RAT → speculative RAT restore)
  let dump_data := (List.range numArchRegs).map (fun i =>
    (List.range tagWidth).map (fun j => Wire.mk s!"dump_data_{i}_{j}"))

  -- Internal: Write Decoder (5→32 one-hot)
  let write_sel := (List.range numArchRegs).map (fun i => Wire.mk s!"write_sel_{i}")

  let decoder_inst : CircuitInstance := {
    moduleName := s!"Decoder{addrWidth}"
    instName := "u_write_dec"
    portMap :=
      (write_addr.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (write_sel.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- Internal: Per-entry write enable
  -- we_i = write_en AND write_sel_i
  let we := (List.range numArchRegs).map (fun i => Wire.mk s!"we_{i}")
  let we_gates := (List.range numArchRegs).map (fun i =>
    Gate.mkAND write_en (write_sel[i]!) (we[i]!))

  -- Reset buffer tree: 2-level, reduce fanout from 1→192 to 1→4→8→~12 DFFs
  -- Level 1: 4 root buffers from reset
  -- Level 2: 16 leaf buffers (4 per root), each driving 2 arch regs × 6 bits = 12 DFFs
  let numRoots := 4
  let reset_roots := (List.range numRoots).map (fun i =>
    Wire.mk s!"reset_root_{i}")
  let reset_root_gates := (List.range numRoots).map (fun i =>
    Gate.mkBUF reset (reset_roots[i]!))
  let numResetLeaves := 16
  let reset_leaves := (List.range numResetLeaves).map (fun i =>
    Wire.mk s!"reset_buf_{i}")
  let reset_buf_gates := reset_root_gates ++ (List.range numResetLeaves).map (fun i =>
    Gate.mkBUF (reset_roots[i / 4]!) (reset_leaves[i]!))

  -- Internal: Storage registers
  -- On write, reg[i] = we[i] ? write_data : reg[i] (hold)
  -- On reset, all DFFs reset to 0 (initialization done externally via write port)
  --
  -- Identity mapping: after reset, reg[i] = i (arch reg i → phys reg i).
  -- Uses DFF_SET for bits where identity value has a 1, DFF for 0 bits.
  let getReg (i j : Nat) : Wire := Wire.mk s!"reg_{i}_{j}"
  let getNext (i j : Nat) : Wire := Wire.mk s!"next_{i}_{j}"
  let getNormalNext (i j : Nat) : Wire := Wire.mk s!"normal_next_{i}_{j}"
  let getDump (i j : Nat) : Wire := Wire.mk s!"dump_data_{i}_{j}"

  let storage_gates := (List.range numArchRegs).map (fun i =>
    let reset_leaf := reset_leaves[i / 2]!  -- 2 arch regs per leaf buffer
    (List.range tagWidth).map (fun j =>
      let reg := getReg i j
      let next := getNext i j
      let normal_next := getNormalNext i j
      let bitVal := (i >>> j) % 2  -- bit j of identity value i
      [
        -- Write data mux: normal_next = we ? write_data : reg (hold)
        Gate.mkMUX reg (write_data[j]!) (we[i]!) normal_next,
        -- Restore override: next = restore_en ? restore_data : normal_next
        Gate.mkMUX normal_next (restore_data[i]![j]!) restore_en next,
        -- Storage DFF: DFF_SET for 1-bits, DFF for 0-bits (identity reset)
        if bitVal == 1 then
          Gate.mkDFF_SET next clock reset_leaf reg
        else
          Gate.mkDFF next clock reset_leaf reg,
        -- Dump output: write-through (bypass) so committed RAT dump
        -- reflects current-cycle writes combinationally
        Gate.mkBUF normal_next (getDump i j)
      ]
    )
  ) |>.flatten |>.flatten

  -- Read Port 1 & 2: Mux32x6 for rs1/rs2
  -- Mux modules use signal groups: in0, in1, ..., sel, out
  let mux_in_map := (List.range numArchRegs).map (fun i =>
    (List.range tagWidth).map (fun j =>
      (s!"in{i}[{j}]", getReg i j)
    )
  ) |>.flatten

  let mkMuxSelMap (addr : List Wire) :=
    addr.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w))

  let mkMuxOutMap (data : List Wire) :=
    data.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w))

  let mux_rs1_inst : CircuitInstance := {
    moduleName := s!"Mux{numArchRegs}x{tagWidth}"
    instName := "u_mux_rs1"
    portMap := mux_in_map ++ mkMuxSelMap rs1_addr ++ mkMuxOutMap rs1_data
  }

  let mux_rs2_inst : CircuitInstance := {
    moduleName := s!"Mux{numArchRegs}x{tagWidth}"
    instName := "u_mux_rs2"
    portMap := mux_in_map ++ mkMuxSelMap rs2_addr ++ mkMuxOutMap rs2_data
  }

  -- Third read port: rs3 lookup
  let mux_rs3_inst : CircuitInstance := {
    moduleName := s!"Mux{numArchRegs}x{tagWidth}"
    instName := "u_mux_rs3"
    portMap := mux_in_map ++ mkMuxSelMap rs3_addr ++ mkMuxOutMap rs3_data
  }

  -- Fourth read port: read RAT[write_addr] to get old mapping before write
  let mux_old_rd_inst : CircuitInstance := {
    moduleName := s!"Mux{numArchRegs}x{tagWidth}"
    instName := "u_mux_old_rd"
    portMap := mux_in_map ++ mkMuxSelMap write_addr ++ mkMuxOutMap old_rd_data
  }

  { name := s!"RAT_{numArchRegs}x{tagWidth}"
    inputs := [clock, reset, write_en] ++ write_addr ++ write_data ++ rs1_addr ++ rs2_addr ++ rs3_addr ++
              [restore_en] ++ restore_data.flatten
    outputs := rs1_data ++ rs2_data ++ rs3_data ++ old_rd_data ++ dump_data.flatten
    gates := we_gates ++ reset_buf_gates ++ storage_gates
    instances := [decoder_inst, mux_rs1_inst, mux_rs2_inst, mux_rs3_inst, mux_old_rd_inst]
    -- V2 codegen annotations
    signalGroups := [
      { name := "write_addr", width := addrWidth, wires := write_addr },
      { name := "write_data", width := tagWidth, wires := write_data },
      { name := "rs1_addr", width := addrWidth, wires := rs1_addr },
      { name := "rs2_addr", width := addrWidth, wires := rs2_addr },
      { name := "rs3_addr", width := addrWidth, wires := rs3_addr },
      { name := "rs1_data", width := tagWidth, wires := rs1_data },
      { name := "rs2_data", width := tagWidth, wires := rs2_data },
      { name := "rs3_data", width := tagWidth, wires := rs3_data },
      { name := "write_sel", width := numArchRegs, wires := write_sel },
      { name := "we", width := numArchRegs, wires := we },
      { name := "old_rd_data", width := tagWidth, wires := old_rd_data }
    ] ++ (List.range numArchRegs).map (fun i =>
      { name := s!"restore_data_{i}", width := tagWidth, wires := restore_data[i]! }
    ) ++ (List.range numArchRegs).map (fun i =>
      { name := s!"dump_data_{i}", width := tagWidth, wires := dump_data[i]! }
    )
  }

/-- RAT with 64 physical registers (default configuration) -/
def mkRAT64 : Circuit := mkRAT 64

end Shoumei.RISCV.Renaming

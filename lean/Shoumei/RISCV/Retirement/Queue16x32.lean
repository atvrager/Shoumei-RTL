/-
RISCV/Retirement/Queue16x32.lean - 16×32-bit Register Array

Simple register file indexed by ROB slot, used for:
- PC queue: stores fetch PC at ROB allocation, read at commit for RVVI pc_rdata
- Instruction queue: stores instruction word at allocation, read at commit for RVVI insn

Design:
- 16 entries, each 32 bits wide
- 1 write port: wr_en, wr_idx[3:0], wr_data[31:0]
- 1 read port: rd_idx[3:0], rd_data[31:0]
- Synchronous write, asynchronous read
- Synchronous reset to all zeros

Structural components:
- 16× Register32 instances (storage)
- 1× Decoder4 (write address decode)
- 1× Mux16x32 (read mux)
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Circuits.Sequential.Register
import Shoumei.RISCV.Config

namespace Shoumei.RISCV.Retirement

open Shoumei
open Shoumei.Circuits.Combinational

/--
Build a Queue16x32 structural circuit.

Ports:
- Inputs: clock, reset, wr_en, wr_idx[3:0], wr_data[31:0], rd_idx[3:0]
- Outputs: rd_data[31:0]
-/
def mkQueue16x32 : Circuit :=
  let numEntries := 16
  let dataWidth := 32
  let idxWidth := 4

  -- Inputs
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let wr_en := Wire.mk "wr_en"
  let wr_idx := (List.range idxWidth).map (fun i => Wire.mk s!"wr_idx_{i}")
  let wr_data := (List.range dataWidth).map (fun i => Wire.mk s!"wr_data_{i}")
  let rd_idx := (List.range idxWidth).map (fun i => Wire.mk s!"rd_idx_{i}")

  -- Outputs
  let rd_data := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data_{i}")

  -- Internal: Write Decoder (4→16 one-hot)
  let write_sel := (List.range numEntries).map (fun i => Wire.mk s!"write_sel_{i}")

  let decoder_inst : CircuitInstance := {
    moduleName := "Decoder4"
    instName := "u_write_dec"
    portMap :=
      (wr_idx.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (write_sel.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- Per-entry write enable: we_i = wr_en AND write_sel_i
  let we := (List.range numEntries).map (fun i => Wire.mk s!"we_{i}")
  let we_gates := (List.range numEntries).map (fun i =>
    Gate.mkAND wr_en (write_sel[i]!) (we[i]!))

  -- Storage: internal register wires
  let getReg (i j : Nat) : Wire := Wire.mk s!"reg_{i}_{j}"
  let getNext (i j : Nat) : Wire := Wire.mk s!"next_{i}_{j}"

  -- Write-enable mux: next = we[i] ? wr_data[j] : reg[i][j]
  let write_mux_gates := (List.range numEntries).map (fun i =>
    (List.range dataWidth).map (fun j =>
      Gate.mkMUX (getReg i j) (wr_data[j]!) (we[i]!) (getNext i j)
    )
  ) |>.flatten

  -- Register32 instances for storage
  let storage_instances := (List.range numEntries).map (fun i =>
    { moduleName := "Register32"
      instName := s!"u_reg_{i}"
      portMap :=
        (List.range dataWidth).map (fun j =>
          (s!"d_{j}", getNext i j)) ++
        [("clock", clock), ("reset", reset)] ++
        (List.range dataWidth).map (fun j =>
          (s!"q_{j}", getReg i j))
    })

  -- Read mux: Mux16x32
  let mux_in_map := (List.range numEntries).map (fun i =>
    (List.range dataWidth).map (fun j =>
      (s!"in{i}_{j}", getReg i j)
    )
  ) |>.flatten

  let mux_rd_inst : CircuitInstance := {
    moduleName := "Mux16x32"
    instName := "u_mux_rd"
    portMap := mux_in_map ++
      (rd_idx.enum.map (fun ⟨i, w⟩ => (s!"sel_{i}", w))) ++
      (rd_data.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- Signal groups for next and reg internal wires
  let next_groups := (List.range numEntries).map (fun i =>
    { name := s!"next_{i}",
      width := dataWidth,
      wires := (List.range dataWidth).map (fun j => getNext i j) })
  let reg_groups := (List.range numEntries).map (fun i =>
    { name := s!"reg_{i}",
      width := dataWidth,
      wires := (List.range dataWidth).map (fun j => getReg i j) })

  { name := "Queue16x32"
    inputs := [clock, reset, wr_en] ++ wr_idx ++ wr_data ++ rd_idx
    outputs := rd_data
    gates := we_gates ++ write_mux_gates
    instances := [decoder_inst] ++ storage_instances ++ [mux_rd_inst]
    signalGroups := [
      { name := "wr_idx", width := idxWidth, wires := wr_idx },
      { name := "wr_data", width := dataWidth, wires := wr_data },
      { name := "rd_idx", width := idxWidth, wires := rd_idx },
      { name := "rd_data", width := dataWidth, wires := rd_data },
      { name := "write_sel", width := numEntries, wires := write_sel },
      { name := "we", width := numEntries, wires := we }
    ] ++ next_groups ++ reg_groups
  }

/-- Config-driven RVVI queue (currently only supports 16 entries matching ROB depth) -/
def mkRVVIQueueFromConfig (_config : Shoumei.RISCV.CPUConfig) : Circuit :=
  mkQueue16x32

/--
Build a Queue16x32_DualPort structural circuit.

Dual write-port, dual read-port 16×32 register file for W=2 RVVI:
- 2 write ports: wr_en_0/1, wr_idx_0/1[3:0], wr_data_0/1[31:0]
- 2 read ports: rd_idx_0/1[3:0], rd_data_0/1[31:0]
- Per-entry write enable: we[i] = (wr_en_0 AND dec0[i]) OR (wr_en_1 AND dec1[i])
- Write-data priority: slot 1 wins on conflict (unlikely with sequential ROB alloc)

Structural components:
- 16× Register32 instances (storage)
- 2× Decoder4 (write address decode)
- 2× Mux16x32 (read mux)
-/
def mkQueue16x32_DualPort : Circuit :=
  let numEntries := 16
  let dataWidth := 32
  let idxWidth := 4

  -- Inputs
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let wr_en_0 := Wire.mk "wr_en_0"
  let wr_idx_0 := (List.range idxWidth).map (fun i => Wire.mk s!"wr_idx_0_{i}")
  let wr_data_0 := (List.range dataWidth).map (fun i => Wire.mk s!"wr_data_0_{i}")
  let wr_en_1 := Wire.mk "wr_en_1"
  let wr_idx_1 := (List.range idxWidth).map (fun i => Wire.mk s!"wr_idx_1_{i}")
  let wr_data_1 := (List.range dataWidth).map (fun i => Wire.mk s!"wr_data_1_{i}")
  let rd_idx_0 := (List.range idxWidth).map (fun i => Wire.mk s!"rd_idx_0_{i}")
  let rd_idx_1 := (List.range idxWidth).map (fun i => Wire.mk s!"rd_idx_1_{i}")

  -- Outputs
  let rd_data_0 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data_0_{i}")
  let rd_data_1 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data_1_{i}")

  -- Write decoders (2× Decoder4)
  let write_sel_0 := (List.range numEntries).map (fun i => Wire.mk s!"wsel0_{i}")
  let write_sel_1 := (List.range numEntries).map (fun i => Wire.mk s!"wsel1_{i}")

  let dec0_inst : CircuitInstance := {
    moduleName := "Decoder4"
    instName := "u_write_dec0"
    portMap :=
      (wr_idx_0.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (write_sel_0.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }
  let dec1_inst : CircuitInstance := {
    moduleName := "Decoder4"
    instName := "u_write_dec1"
    portMap :=
      (wr_idx_1.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (write_sel_1.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- Per-entry write enable: we[i] = (wr_en_0 AND wsel0[i]) OR (wr_en_1 AND wsel1[i])
  let we := (List.range numEntries).map (fun i => Wire.mk s!"we_{i}")
  let we1_hit := (List.range numEntries).map (fun i => Wire.mk s!"we1_hit_{i}")
  let we_gates := (List.range numEntries).map (fun i =>
    [Gate.mkAND wr_en_0 (write_sel_0[i]!) (Wire.mk s!"we0_hit_{i}"),
     Gate.mkAND wr_en_1 (write_sel_1[i]!) (we1_hit[i]!),
     Gate.mkOR (Wire.mk s!"we0_hit_{i}") (we1_hit[i]!) (we[i]!)]
  ) |>.flatten

  -- Storage wires
  let getReg (i j : Nat) : Wire := Wire.mk s!"reg_{i}_{j}"
  let getNext (i j : Nat) : Wire := Wire.mk s!"next_{i}_{j}"

  -- Write-data mux: per entry, select wr_data_1 if we1_hit, else wr_data_0
  -- Then gate with we[i]: next[i][j] = we[i] ? selected_data[j] : reg[i][j]
  let write_mux_gates := (List.range numEntries).map (fun i =>
    (List.range dataWidth).map (fun j =>
      let sel_data := Wire.mk s!"wdata_sel_{i}_{j}"
      [Gate.mkMUX (wr_data_0[j]!) (wr_data_1[j]!) (we1_hit[i]!) sel_data,
       Gate.mkMUX (getReg i j) sel_data (we[i]!) (getNext i j)]
    ) |>.flatten
  ) |>.flatten

  -- Register32 instances
  let storage_instances := (List.range numEntries).map (fun i =>
    { moduleName := "Register32"
      instName := s!"u_reg_{i}"
      portMap :=
        (List.range dataWidth).map (fun j =>
          (s!"d_{j}", getNext i j)) ++
        [("clock", clock), ("reset", reset)] ++
        (List.range dataWidth).map (fun j =>
          (s!"q_{j}", getReg i j))
    })

  -- Read mux 0
  let mux_in_map := (List.range numEntries).map (fun i =>
    (List.range dataWidth).map (fun j =>
      (s!"in{i}_{j}", getReg i j)
    )
  ) |>.flatten

  let mux_rd0_inst : CircuitInstance := {
    moduleName := "Mux16x32"
    instName := "u_mux_rd0"
    portMap := mux_in_map ++
      (rd_idx_0.enum.map (fun ⟨i, w⟩ => (s!"sel_{i}", w))) ++
      (rd_data_0.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- Read mux 1
  let mux_rd1_inst : CircuitInstance := {
    moduleName := "Mux16x32"
    instName := "u_mux_rd1"
    portMap := mux_in_map ++
      (rd_idx_1.enum.map (fun ⟨i, w⟩ => (s!"sel_{i}", w))) ++
      (rd_data_1.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- Signal groups
  let next_groups := (List.range numEntries).map (fun i =>
    { name := s!"next_{i}",
      width := dataWidth,
      wires := (List.range dataWidth).map (fun j => getNext i j) })
  let reg_groups := (List.range numEntries).map (fun i =>
    { name := s!"reg_{i}",
      width := dataWidth,
      wires := (List.range dataWidth).map (fun j => getReg i j) })

  { name := "Queue16x32_DualPort"
    inputs := [clock, reset, wr_en_0] ++ wr_idx_0 ++ wr_data_0 ++
              [wr_en_1] ++ wr_idx_1 ++ wr_data_1 ++ rd_idx_0 ++ rd_idx_1
    outputs := rd_data_0 ++ rd_data_1
    gates := we_gates ++ write_mux_gates
    instances := [dec0_inst, dec1_inst] ++ storage_instances ++ [mux_rd0_inst, mux_rd1_inst]
    signalGroups := [
      { name := "wr_idx_0", width := idxWidth, wires := wr_idx_0 },
      { name := "wr_data_0", width := dataWidth, wires := wr_data_0 },
      { name := "wr_idx_1", width := idxWidth, wires := wr_idx_1 },
      { name := "wr_data_1", width := dataWidth, wires := wr_data_1 },
      { name := "rd_idx_0", width := idxWidth, wires := rd_idx_0 },
      { name := "rd_idx_1", width := idxWidth, wires := rd_idx_1 },
      { name := "rd_data_0", width := dataWidth, wires := rd_data_0 },
      { name := "rd_data_1", width := dataWidth, wires := rd_data_1 },
      { name := "write_sel_0", width := numEntries, wires := write_sel_0 },
      { name := "write_sel_1", width := numEntries, wires := write_sel_1 },
      { name := "we", width := numEntries, wires := we }
    ] ++ next_groups ++ reg_groups
  }

end Shoumei.RISCV.Retirement

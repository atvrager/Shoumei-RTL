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
          (s!"d[{j}]", getNext i j)) ++
        [("clock", clock), ("reset", reset)] ++
        (List.range dataWidth).map (fun j =>
          (s!"q[{j}]", getReg i j))
    })

  -- Read mux: Mux16x32
  let mux_in_map := (List.range numEntries).map (fun i =>
    (List.range dataWidth).map (fun j =>
      (s!"in{i}[{j}]", getReg i j)
    )
  ) |>.flatten

  let mux_rd_inst : CircuitInstance := {
    moduleName := "Mux16x32"
    instName := "u_mux_rd"
    portMap := mux_in_map ++
      (rd_idx.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w))) ++
      (rd_data.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w)))
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

end Shoumei.RISCV.Retirement

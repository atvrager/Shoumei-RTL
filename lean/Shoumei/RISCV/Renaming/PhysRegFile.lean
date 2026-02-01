/-
RISCV/Renaming/PhysRegFile.lean - Physical Register File

Stores 64 physical registers, each 32 bits wide.
Used in Tomasulo out-of-order execution to hold renamed register values.

Design:
- 64 entries, each 32 bits wide (full RISC-V word)
- 2 read ports (asynchronous, for rs1/rs2 operand fetch)
- 1 write port (synchronous, from CDB writeback)
- Synchronous reset to all zeros

Structural components:
- Storage: 64 × 32-bit DFF registers
- Write decoder: Decoder6 (6→64 one-hot)
- Read mux 1: Mux64x32 (64:1, 32-bit wide) for rd_tag1
- Read mux 2: Mux64x32 (64:1, 32-bit wide) for rd_tag2
- Write enable: AND(wr_en, decoder output) per entry
- Write data MUX: select between hold value and write data
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Circuits.Sequential.DFF

namespace Shoumei.RISCV.Renaming

open Shoumei
open Shoumei.Circuits.Combinational

/-! ## Behavioral Model -/

/-- Physical register file state: 64 registers of 32 bits each -/
structure PhysRegFileState (numRegs : Nat) where
  /-- Register contents: physical register tag → 32-bit value -/
  regs : Fin numRegs → UInt32

/-- Read a physical register (asynchronous) -/
def PhysRegFileState.read (prf : PhysRegFileState n) (tag : Fin n) : UInt32 :=
  prf.regs tag

/-- Write a value to a physical register (synchronous) -/
def PhysRegFileState.write (prf : PhysRegFileState n) (tag : Fin n) (val : UInt32) : PhysRegFileState n :=
  { regs := fun i => if i == tag then val else prf.regs i }

/-- Initialize all registers to zero -/
def PhysRegFileState.init (n : Nat) : PhysRegFileState n :=
  { regs := fun _ => 0 }

/-- Read two registers simultaneously (common operation for rs1, rs2) -/
def PhysRegFileState.readPair (prf : PhysRegFileState n) (tag1 tag2 : Fin n) : UInt32 × UInt32 :=
  (prf.read tag1, prf.read tag2)

/-! ## Structural Circuit -/

/-- Helper: Compute log2 ceiling -/
private def log2Ceil (n : Nat) : Nat :=
  if n <= 1 then 0
  else Nat.log2 n + (if 2^(Nat.log2 n) < n then 1 else 0)

/--
Build a Physical Register File circuit.

Parameters:
- numRegs: Number of physical registers (default 64)
- dataWidth: Width of each register in bits (default 32)

Ports:
- Inputs: clock, reset, wr_en, rd_tag1[tagWidth-1:0], rd_tag2[tagWidth-1:0],
          wr_tag[tagWidth-1:0], wr_data[dataWidth-1:0]
- Outputs: rd_data1[dataWidth-1:0], rd_data2[dataWidth-1:0]

Architecture:
- 64 × 32-bit DFF registers with synchronous reset to zero
- Decoder6 for write address decode
- Two Mux64x32 for read ports
-/
def mkPhysRegFile (numRegs : Nat := 64) (dataWidth : Nat := 32) : Circuit :=
  let tagWidth := log2Ceil numRegs  -- 6 for 64 regs

  -- Inputs
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let wr_en := Wire.mk "wr_en"
  let rd_tag1 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag1_{i}")
  let rd_tag2 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag2_{i}")
  let wr_tag := (List.range tagWidth).map (fun i => Wire.mk s!"wr_tag_{i}")
  let wr_data := (List.range dataWidth).map (fun i => Wire.mk s!"wr_data_{i}")

  -- Outputs
  let rd_data1 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data1_{i}")
  let rd_data2 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data2_{i}")

  -- Internal: Write Decoder (6→64 one-hot)
  let write_sel := (List.range numRegs).map (fun i => Wire.mk s!"write_sel_{i}")

  let decoder_inst : CircuitInstance := {
    moduleName := s!"Decoder{tagWidth}"
    instName := "u_write_dec"
    portMap :=
      (wr_tag.enum.map (fun ⟨i, w⟩ => (s!"in{i}", w))) ++
      (write_sel.enum.map (fun ⟨i, w⟩ => (s!"out{i}", w)))
  }

  -- Internal: Per-entry write enable
  -- we_i = wr_en AND write_sel_i
  let we := (List.range numRegs).map (fun i => Wire.mk s!"we_{i}")
  let we_gates := (List.range numRegs).map (fun i =>
    Gate.mkAND wr_en (write_sel.get! i) (we.get! i))

  -- Internal: Storage registers with write muxes
  -- On write: reg[i][j] = we[i] ? wr_data[j] : reg[i][j] (hold)
  -- On reset: all DFFs reset to 0
  let getReg (i j : Nat) : Wire := Wire.mk s!"reg_{i}_{j}"
  let getNext (i j : Nat) : Wire := Wire.mk s!"next_{i}_{j}"

  let storage_gates := (List.range numRegs).map (fun i =>
    (List.range dataWidth).map (fun j =>
      let reg := getReg i j
      let next := getNext i j
      [
        -- Write data mux: next = we ? wr_data : reg (hold)
        Gate.mkMUX reg (wr_data.get! j) (we.get! i) next,
        -- Storage DFF (resets to 0)
        Gate.mkDFF next clock reset reg
      ]
    )
  ) |>.flatten |>.flatten

  -- Read Ports: Mux64x32 for rd_tag1/rd_tag2
  -- Mux64x32 uses bundled ports (>200 ports): inputs[idx], outputs[idx]
  let totalMuxPorts := numRegs * dataWidth + tagWidth + dataWidth
  let useBundle := totalMuxPorts > 200

  let mux_in_map := if useBundle then
      (List.range numRegs).map (fun i =>
        (List.range dataWidth).map (fun j =>
          let idx := i * dataWidth + j
          (s!"inputs[{idx}]", getReg i j)
        )
      ) |>.flatten
    else
      (List.range numRegs).map (fun i =>
        (List.range dataWidth).map (fun j =>
          (s!"in{i}_b{j}", getReg i j)
        )
      ) |>.flatten

  let mkMuxSelMap (addr : List Wire) := if useBundle then
      addr.enum.map (fun ⟨i, w⟩ =>
        let idx := numRegs * dataWidth + i
        (s!"inputs[{idx}]", w))
    else
      addr.enum.map (fun ⟨i, w⟩ => (s!"sel{i}", w))

  let mkMuxOutMap (data : List Wire) := if useBundle then
      data.enum.map (fun ⟨i, w⟩ => (s!"outputs[{i}]", w))
    else
      data.enum.map (fun ⟨i, w⟩ => (s!"out{i}", w))

  let mux_rd1_inst : CircuitInstance := {
    moduleName := s!"Mux{numRegs}x{dataWidth}"
    instName := "u_mux_rd1"
    portMap := mux_in_map ++ mkMuxSelMap rd_tag1 ++ mkMuxOutMap rd_data1
  }

  let mux_rd2_inst : CircuitInstance := {
    moduleName := s!"Mux{numRegs}x{dataWidth}"
    instName := "u_mux_rd2"
    portMap := mux_in_map ++ mkMuxSelMap rd_tag2 ++ mkMuxOutMap rd_data2
  }

  { name := s!"PhysRegFile_{numRegs}x{dataWidth}"
    inputs := [clock, reset, wr_en] ++ rd_tag1 ++ rd_tag2 ++ wr_tag ++ wr_data
    outputs := rd_data1 ++ rd_data2
    gates := we_gates ++ storage_gates
    instances := [decoder_inst, mux_rd1_inst, mux_rd2_inst]
  }

/-- Physical Register File with 64 registers × 32 bits (default configuration) -/
def mkPhysRegFile64 : Circuit := mkPhysRegFile 64 32

/-- Small Physical Register File for proof testing (4 registers × 8 bits) -/
def mkPhysRegFile4x8 : Circuit := mkPhysRegFile 4 8

end Shoumei.RISCV.Renaming

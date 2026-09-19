/-
RISCV/Renaming/PhysRegFile.lean - Physical Register File

Stores 64 physical registers, each 32 bits wide.
Used in dynamic out-of-order execution to hold renamed register values.

Design:
- 64 entries, each 32 bits wide (full RISC-V word)
- 4 read ports (asynchronous, for rs1/rs2 operand fetch + RVVI commit readback + RVVI FP readback)
- 1 write port (synchronous, from CDB writeback)
- Synchronous reset to all zeros

Structural components:
- Storage: 64 × 32-bit DFF registers
- Write decoder: Decoder6 (6→64 one-hot)
- Read mux 1: Mux64x32 (64:1, 32-bit wide) for rd_tag1
- Read mux 2: Mux64x32 (64:1, 32-bit wide) for rd_tag2
- Read mux 3: Mux64x32 (64:1, 32-bit wide) for rd_tag3 (RVVI commit readback)
- Write enable: AND(wr_en, decoder output) per entry
- Write data MUX: select between hold value and write data
-/

import Shoumei.DSL
import Shoumei.RISCV.Config
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Circuits.Sequential.DFF
import Shoumei.Circuits.Sequential.Register

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
          rd_tag3[tagWidth-1:0], wr_tag[tagWidth-1:0], wr_data[dataWidth-1:0]
- Outputs: rd_data1[dataWidth-1:0], rd_data2[dataWidth-1:0], rd_data3[dataWidth-1:0]

Architecture:
- 64 × 32-bit DFF registers with synchronous reset to zero
- Decoder6 for write address decode
- Three Mux64x32 for read ports (rs1, rs2, RVVI commit readback)
-/
def mkPhysRegFile (numRegs : Nat := 64) (dataWidth : Nat := 64) : Circuit :=
  let tagWidth := log2Ceil numRegs  -- 6 for 64 regs

  -- Common inputs
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"

  -- Dual write port W=2.
  -- Write port 1 has priority over port 0 if they target the same register in the same cycle.
  let wr_en_0 := Wire.mk "wr_en_0"
  let wr_tag_0 := (List.range tagWidth).map (fun i => Wire.mk s!"wr_tag_0_{i}")
  let wr_data_0 := (List.range dataWidth).map (fun i => Wire.mk s!"wr_data_0_{i}")

    let wr_en_1 := Wire.mk "wr_en_1"
    let wr_tag_1 := (List.range tagWidth).map (fun i => Wire.mk s!"wr_tag_1_{i}")
    let wr_data_1 := (List.range dataWidth).map (fun i => Wire.mk s!"wr_data_1_{i}")

    let rd_tag1 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag1_{i}")
    let rd_tag2 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag2_{i}")
    let rd_tag3 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag3_{i}")
    let rd_tag4 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag4_{i}")
    let rd_tag5 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag5_{i}")
    let rd_tag6 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag6_{i}")
    let rd_tag7 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag7_{i}")

    -- Outputs
    let rd_data1 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data1_{i}")
    let rd_data2 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data2_{i}")
    let rd_data3 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data3_{i}")
    let rd_data4 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data4_{i}")
    let rd_data5 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data5_{i}")
    let rd_data6 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data6_{i}")
    let rd_data7 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data7_{i}")

    -- Decoders: one per write port
    let write_sel_0 := (List.range numRegs).map (fun i => Wire.mk s!"write_sel_0_{i}")
    let decoder0_inst : CircuitInstance := {
      moduleName := s!"Decoder{tagWidth}"
      instName := "u_write_dec_0"
      portMap := (wr_tag_0.enum.map fun ⟨i,w⟩ => (s!"in_{i}", w)) ++
                 (write_sel_0.enum.map fun ⟨i,w⟩ => (s!"out_{i}", w))
    }

    let write_sel_1 := (List.range numRegs).map (fun i => Wire.mk s!"write_sel_1_{i}")
    let decoder1_inst : CircuitInstance := {
      moduleName := s!"Decoder{tagWidth}"
      instName := "u_write_dec_1"
      portMap := (wr_tag_1.enum.map fun ⟨i,w⟩ => (s!"in_{i}", w)) ++
                 (write_sel_1.enum.map fun ⟨i,w⟩ => (s!"out_{i}", w))
    }

    -- Per-entry write enable and data muxing
    let we0 := (List.range numRegs).map (fun i => Wire.mk s!"we0_{i}")
    let we1 := (List.range numRegs).map (fun i => Wire.mk s!"we1_{i}")
    let we_any := (List.range numRegs).map (fun i => Wire.mk s!"we_any_{i}")

    let we_gates := (List.range numRegs).map (fun i =>
      [Gate.mkAND wr_en_0 (write_sel_0[i]!) (we0[i]!),
       Gate.mkAND wr_en_1 (write_sel_1[i]!) (we1[i]!),
       Gate.mkOR  (we0[i]!) (we1[i]!) (we_any[i]!)]
    ) |>.flatten

    let getReg (i j : Nat) : Wire := Wire.mk s!"reg_{i}_{j}"
    let getNext (i j : Nat) : Wire := Wire.mk s!"next_{i}_{j}"
    let getMux0 (i j : Nat) : Wire := Wire.mk s!"mux0_{i}_{j}"

    let write_mux_gates := (List.range numRegs).map (fun i =>
      (List.range dataWidth).map (fun j =>
        [-- 1. If we0, take wr_data_0, else hold reg
         Gate.mkMUX (getReg i j) (wr_data_0[j]!) (we0[i]!) (getMux0 i j),
         -- 2. If we1, take wr_data_1, else take result of mux0 (Priority to Port 1)
         Gate.mkMUX (getMux0 i j) (wr_data_1[j]!) (we1[i]!) (getNext i j)]
      ) |>.flatten
    ) |>.flatten

    -- Reset tree (same structure as W=1)
    let numRoots := 16
    let reset_roots := (List.range numRoots).map (fun i => Wire.mk s!"reset_root_{i}")
    let rr_gates := (List.range numRoots).map (fun i => Gate.mkBUF reset (reset_roots[i]!))
    let reset_leaves := (List.range numRegs).map (fun i => Wire.mk s!"reset_leaf_{i}")
    let rl_gates := (List.range numRegs).map (fun i => Gate.mkBUF (reset_roots[i/4]!) (reset_leaves[i]!))

    -- Storage
    let storage_instances := (List.range numRegs).map (fun i =>
      { moduleName := s!"Register{dataWidth}", instName := s!"u_reg_{i}",
        portMap := (List.range dataWidth).map (fun j => (s!"d[{j}]", getNext i j)) ++
                   [("clock", clock), ("reset", reset_leaves[i]!)] ++
                   (List.range dataWidth).map (fun j => (s!"q[{j}]", getReg i j)) }
    )

    -- Read Muxes
    let mux_in_map := (List.range numRegs).map (fun i =>
      (List.range dataWidth).map (fun j => (s!"in{i}[{j}]", getReg i j))
    ) |>.flatten

    let mkMux (instName : String) (sel : List Wire) (out : List Wire) : CircuitInstance := {
      moduleName := s!"Mux{numRegs}x{dataWidth}"
      instName := instName
      portMap := mux_in_map ++
                 sel.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w)) ++
                 out.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w))
    }

    { name := s!"PhysRegFile_{numRegs}x{dataWidth}"
      inputs := [clock, reset, wr_en_0, wr_en_1] ++ wr_tag_0 ++ wr_data_0 ++ wr_tag_1 ++ wr_data_1 ++
                rd_tag1 ++ rd_tag2 ++ rd_tag3 ++ rd_tag4 ++ rd_tag5 ++ rd_tag6 ++ rd_tag7
      outputs := rd_data1 ++ rd_data2 ++ rd_data3 ++ rd_data4 ++ rd_data5 ++ rd_data6 ++ rd_data7
      gates := we_gates ++ write_mux_gates ++ rr_gates ++ rl_gates
      instances := [decoder0_inst, decoder1_inst] ++ storage_instances ++
                   [mkMux "u_mux_rd1" rd_tag1 rd_data1,
                    mkMux "u_mux_rd2" rd_tag2 rd_data2,
                    mkMux "u_mux_rd3" rd_tag3 rd_data3,
                    mkMux "u_mux_rd4" rd_tag4 rd_data4,
                    mkMux "u_mux_rd5" rd_tag5 rd_data5,
                    mkMux "u_mux_rd6" rd_tag6 rd_data6,
                    mkMux "u_mux_rd7" rd_tag7 rd_data7]
    }

/-- Physical Register File with 64 registers × 32 bits, superscalar (dual write ports) -/
def mkPhysRegFile64 : Circuit := mkPhysRegFile 64 32

/-- Physical Register File with 64 registers × 64 bits, superscalar (dual write ports) -/
def mkPhysRegFile64x64 : Circuit := mkPhysRegFile 64 64

/-- Integer Physical Register File: 2 write ports, 6 read ports (rs1_0, rs2_0, rs1_1, rs2_1, rvvi_0, rvvi_1; no rs3). -/
def mkIntPhysRegFile (numRegs : Nat := 64) (dataWidth : Nat := 64) : Circuit :=
  let tagWidth := log2Ceil numRegs

  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"

  let wr_en_0 := Wire.mk "wr_en_0"
  let wr_tag_0 := (List.range tagWidth).map (fun i => Wire.mk s!"wr_tag_0_{i}")
  let wr_data_0 := (List.range dataWidth).map (fun i => Wire.mk s!"wr_data_0_{i}")

  let wr_en_1 := Wire.mk "wr_en_1"
  let wr_tag_1 := (List.range tagWidth).map (fun i => Wire.mk s!"wr_tag_1_{i}")
  let wr_data_1 := (List.range dataWidth).map (fun i => Wire.mk s!"wr_data_1_{i}")

  let rd_tag1 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag1_{i}")
  let rd_tag2 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag2_{i}")
  let rd_tag4 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag4_{i}")
  let rd_tag5 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag5_{i}")
  let rd_tag6 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag6_{i}")
  let rd_tag7 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag7_{i}")

  let rd_data1 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data1_{i}")
  let rd_data2 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data2_{i}")
  let rd_data4 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data4_{i}")
  let rd_data5 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data5_{i}")
  let rd_data6 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data6_{i}")
  let rd_data7 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data7_{i}")

  let write_sel_0 := (List.range numRegs).map (fun i => Wire.mk s!"write_sel_0_{i}")
  let decoder0_inst : CircuitInstance := {
    moduleName := s!"Decoder{tagWidth}"
    instName := "u_write_dec_0"
    portMap := (wr_tag_0.enum.map fun ⟨i,w⟩ => (s!"in_{i}", w)) ++
               (write_sel_0.enum.map fun ⟨i,w⟩ => (s!"out_{i}", w))
  }

  let write_sel_1 := (List.range numRegs).map (fun i => Wire.mk s!"write_sel_1_{i}")
  let decoder1_inst : CircuitInstance := {
    moduleName := s!"Decoder{tagWidth}"
    instName := "u_write_dec_1"
    portMap := (wr_tag_1.enum.map fun ⟨i,w⟩ => (s!"in_{i}", w)) ++
               (write_sel_1.enum.map fun ⟨i,w⟩ => (s!"out_{i}", w))
  }

  let we0 := (List.range numRegs).map (fun i => Wire.mk s!"we0_{i}")
  let we1 := (List.range numRegs).map (fun i => Wire.mk s!"we1_{i}")
  let we_any := (List.range numRegs).map (fun i => Wire.mk s!"we_any_{i}")

  let we_gates := (List.range numRegs).map (fun i =>
    [Gate.mkAND wr_en_0 (write_sel_0[i]!) (we0[i]!),
     Gate.mkAND wr_en_1 (write_sel_1[i]!) (we1[i]!),
     Gate.mkOR  (we0[i]!) (we1[i]!) (we_any[i]!)]
  ) |>.flatten

  let getReg (i j : Nat) : Wire := Wire.mk s!"reg_{i}_{j}"
  let getNext (i j : Nat) : Wire := Wire.mk s!"next_{i}_{j}"
  let getMux0 (i j : Nat) : Wire := Wire.mk s!"mux0_{i}_{j}"

  let write_mux_gates := (List.range numRegs).map (fun i =>
    (List.range dataWidth).map (fun j =>
      [Gate.mkMUX (getReg i j) (wr_data_0[j]!) (we0[i]!) (getMux0 i j),
       Gate.mkMUX (getMux0 i j) (wr_data_1[j]!) (we1[i]!) (getNext i j)]
    ) |>.flatten
  ) |>.flatten

  let numRoots := 16
  let reset_roots := (List.range numRoots).map (fun i => Wire.mk s!"reset_root_{i}")
  let rr_gates := (List.range numRoots).map (fun i => Gate.mkBUF reset (reset_roots[i]!))
  let reset_leaves := (List.range numRegs).map (fun i => Wire.mk s!"reset_leaf_{i}")
  let rl_gates := (List.range numRegs).map (fun i => Gate.mkBUF (reset_roots[i/4]!) (reset_leaves[i]!))

  let storage_instances := (List.range numRegs).map (fun i =>
    { moduleName := s!"Register{dataWidth}", instName := s!"u_reg_{i}",
      portMap := (List.range dataWidth).map (fun j => (s!"d[{j}]", getNext i j)) ++
                 [("clock", clock), ("reset", reset_leaves[i]!)] ++
                 (List.range dataWidth).map (fun j => (s!"q[{j}]", getReg i j)) }
  )

  let mux_in_map := (List.range numRegs).map (fun i =>
    (List.range dataWidth).map (fun j => (s!"in{i}[{j}]", getReg i j))
  ) |>.flatten

  let mkMux (instName : String) (sel : List Wire) (out : List Wire) : CircuitInstance := {
    moduleName := s!"Mux{numRegs}x{dataWidth}"
    instName := instName
    portMap := mux_in_map ++
               sel.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w)) ++
               out.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w))
  }

  { name := s!"IntPhysRegFile_{numRegs}x{dataWidth}"
    inputs := [clock, reset, wr_en_0, wr_en_1] ++ wr_tag_0 ++ wr_data_0 ++ wr_tag_1 ++ wr_data_1 ++
              rd_tag1 ++ rd_tag2 ++ rd_tag4 ++ rd_tag5 ++ rd_tag6 ++ rd_tag7
    outputs := rd_data1 ++ rd_data2 ++ rd_data4 ++ rd_data5 ++ rd_data6 ++ rd_data7
    gates := we_gates ++ write_mux_gates ++ rr_gates ++ rl_gates
    instances := [decoder0_inst, decoder1_inst] ++ storage_instances ++
                 [mkMux "u_mux_rd1" rd_tag1 rd_data1,
                  mkMux "u_mux_rd2" rd_tag2 rd_data2,
                  mkMux "u_mux_rd4" rd_tag4 rd_data4,
                  mkMux "u_mux_rd5" rd_tag5 rd_data5,
                  mkMux "u_mux_rd6" rd_tag6 rd_data6,
                  mkMux "u_mux_rd7" rd_tag7 rd_data7]
  }

/-- Floating-Point Physical Register File: 1 write port (CDB), 3 read ports (rs1, rs2, rs3). -/
def mkFPPhysRegFile (numRegs : Nat := 64) (dataWidth : Nat := 64) : Circuit :=
  let tagWidth := log2Ceil numRegs

  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"

  let wr_en := Wire.mk "wr_en"
  let wr_tag := (List.range tagWidth).map (fun i => Wire.mk s!"wr_tag_{i}")
  let wr_data := (List.range dataWidth).map (fun i => Wire.mk s!"wr_data_{i}")

  let rd_tag1 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag1_{i}")
  let rd_tag2 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag2_{i}")
  let rd_tag3 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag3_{i}")

  let rd_data1 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data1_{i}")
  let rd_data2 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data2_{i}")
  let rd_data3 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data3_{i}")

  let write_sel := (List.range numRegs).map (fun i => Wire.mk s!"write_sel_{i}")
  let decoder_inst : CircuitInstance := {
    moduleName := s!"Decoder{tagWidth}"
    instName := "u_write_dec"
    portMap := (wr_tag.enum.map fun ⟨i,w⟩ => (s!"in_{i}", w)) ++
               (write_sel.enum.map fun ⟨i,w⟩ => (s!"out_{i}", w))
  }

  let we := (List.range numRegs).map (fun i => Wire.mk s!"we_{i}")
  let we_gates := (List.range numRegs).map (fun i =>
    Gate.mkAND wr_en (write_sel[i]!) (we[i]!))

  let getReg (i j : Nat) : Wire := Wire.mk s!"reg_{i}_{j}"
  let getNext (i j : Nat) : Wire := Wire.mk s!"next_{i}_{j}"

  let write_mux_gates := (List.range numRegs).map (fun i =>
    (List.range dataWidth).map (fun j =>
      Gate.mkMUX (getReg i j) (wr_data[j]!) (we[i]!) (getNext i j)
    )
  ) |>.flatten

  let numRoots := 16
  let reset_roots := (List.range numRoots).map (fun i => Wire.mk s!"reset_root_{i}")
  let rr_gates := (List.range numRoots).map (fun i => Gate.mkBUF reset (reset_roots[i]!))
  let reset_leaves := (List.range numRegs).map (fun i => Wire.mk s!"reset_leaf_{i}")
  let rl_gates := (List.range numRegs).map (fun i => Gate.mkBUF (reset_roots[i/4]!) (reset_leaves[i]!))

  let storage_instances := (List.range numRegs).map (fun i =>
    { moduleName := s!"Register{dataWidth}", instName := s!"u_reg_{i}",
      portMap := (List.range dataWidth).map (fun j => (s!"d[{j}]", getNext i j)) ++
                 [("clock", clock), ("reset", reset_leaves[i]!)] ++
                 (List.range dataWidth).map (fun j => (s!"q[{j}]", getReg i j)) }
  )

  let mux_in_map := (List.range numRegs).map (fun i =>
    (List.range dataWidth).map (fun j => (s!"in{i}[{j}]", getReg i j))
  ) |>.flatten

  let mkMux (instName : String) (sel : List Wire) (out : List Wire) : CircuitInstance := {
    moduleName := s!"Mux{numRegs}x{dataWidth}"
    instName := instName
    portMap := mux_in_map ++
               sel.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w)) ++
               out.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w))
  }

  { name := s!"FPPhysRegFile_{numRegs}x{dataWidth}"
    inputs := [clock, reset, wr_en] ++ wr_tag ++ wr_data ++
              rd_tag1 ++ rd_tag2 ++ rd_tag3
    outputs := rd_data1 ++ rd_data2 ++ rd_data3
    gates := we_gates ++ write_mux_gates ++ rr_gates ++ rl_gates
    instances := [decoder_inst] ++ storage_instances ++
                 [mkMux "u_mux_rd1" rd_tag1 rd_data1,
                  mkMux "u_mux_rd2" rd_tag2 rd_data2,
                  mkMux "u_mux_rd3" rd_tag3 rd_data3]
  }

/-- Config-driven Physical Register File -/
def mkPhysRegFileFromConfig (config : Shoumei.RISCV.CPUConfig) : Circuit :=
  mkPhysRegFile config.numPhysRegs config.xlen

end Shoumei.RISCV.Renaming

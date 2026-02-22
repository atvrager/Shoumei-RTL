/-
RISCV/Renaming/PhysRegFile.lean - Physical Register File

Stores 64 physical registers, each 32 bits wide.
Used in Tomasulo out-of-order execution to hold renamed register values.

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
def mkPhysRegFile (numRegs : Nat := 64) (dataWidth : Nat := 32) (writeWidth : Nat := 2) : Circuit :=
  let tagWidth := log2Ceil numRegs  -- 6 for 64 regs

  -- Common inputs
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"

  if writeWidth == 1 then
    -- Single write port (original implementation)
    let wr_en := Wire.mk "wr_en"
    let rd_tag1 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag1_{i}")
    let rd_tag2 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag2_{i}")
    let rd_tag3 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag3_{i}")
    let rd_tag4 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag4_{i}")
    let wr_tag := (List.range tagWidth).map (fun i => Wire.mk s!"wr_tag_{i}")
    let wr_data := (List.range dataWidth).map (fun i => Wire.mk s!"wr_data_{i}")

    -- Outputs
    let rd_data1 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data1_{i}")
    let rd_data2 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data2_{i}")
    let rd_data3 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data3_{i}")
    let rd_data4 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data4_{i}")

    -- Internal: Write Decoder (6→64 one-hot)
    let write_sel := (List.range numRegs).map (fun i => Wire.mk s!"write_sel_{i}")

    let decoder_inst : CircuitInstance := {
      moduleName := s!"Decoder{tagWidth}"
      instName := "u_write_dec"
      portMap :=
        (wr_tag.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
        (write_sel.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
    }

    -- Internal: Per-entry write enable
    -- we_i = wr_en AND write_sel_i
    let we := (List.range numRegs).map (fun i => Wire.mk s!"we_{i}")
    let we_gates := (List.range numRegs).map (fun i =>
      Gate.mkAND wr_en (write_sel[i]!) (we[i]!))

    -- Internal: Storage registers with write muxes
    -- On write: reg[i][j] = we[i] ? wr_data[j] : reg[i][j] (hold)
    -- On reset: all DFFs reset to 0
    let getReg (i j : Nat) : Wire := Wire.mk s!"reg_{i}_{j}"
    let getNext (i j : Nat) : Wire := Wire.mk s!"next_{i}_{j}"

    -- Write-enable mux gates: next = we[i] ? wr_data[j] : reg[i][j] (hold)
    let write_mux_gates := (List.range numRegs).map (fun i =>
      (List.range dataWidth).map (fun j =>
        let reg := getReg i j
        let next := getNext i j
        Gate.mkMUX reg (wr_data[j]!) (we[i]!) next
      )
    ) |>.flatten

    -- Reset buffer tree: 2-level, reduce fanout from 1→64 to 1→16→4→1
    -- Level 1: 16 root buffers from reset
    -- Level 2: 64 leaf buffers (4 per root), each driving 1 Register32 (32 DFFs)
    let numRoots := 16
    let reset_roots := (List.range numRoots).map (fun i =>
      Wire.mk s!"reset_root_{i}")
    let reset_root_gates := (List.range numRoots).map (fun i =>
      Gate.mkBUF reset (reset_roots[i]!))
    let numResetLeaves := numRegs  -- 64 leaves, one per register
    let reset_leaves := (List.range numResetLeaves).map (fun i =>
      Wire.mk s!"reset_buf_{i}")
    let reset_buf_gates := reset_root_gates ++ (List.range numResetLeaves).map (fun i =>
      Gate.mkBUF (reset_roots[i / 4]!) (reset_leaves[i]!))

    -- Storage instances: 64× Register32 (hierarchical, not inline DFFs)
    let storage_instances := (List.range numRegs).map (fun i =>
      let reset_leaf := reset_leaves[i]!  -- 1 reg per leaf buffer
      {
        moduleName := s!"Register{dataWidth}"
        instName := s!"u_reg_{i}"
        portMap :=
          -- Connect d inputs (from write mux outputs) - use bracket notation for Cat grouping
          (List.range dataWidth).map (fun j =>
            (s!"d[{j}]", getNext i j)
          ) ++
          -- Connect clock and reset (via buffered reset tree)
          [("clock", clock), ("reset", reset_leaf)] ++
          -- Connect q outputs - use bracket notation for Cat grouping
          (List.range dataWidth).map (fun j =>
            (s!"q[{j}]", getReg i j)
          )
      }
    )

    -- Read Ports: Mux64x32 for rd_tag1/rd_tag2
    -- Mux64x32 uses signal groups: in0, in1, ..., in63 (each 32 bits), sel (6 bits), out (32 bits)
    let mux_in_map := (List.range numRegs).map (fun i =>
      (List.range dataWidth).map (fun j =>
        (s!"in{i}[{j}]", getReg i j)
      )
    ) |>.flatten

    let mkMuxSelMap (addr : List Wire) :=
      addr.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w))

    let mkMuxOutMap (data : List Wire) :=
      data.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w))

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

    let mux_rd3_inst : CircuitInstance := {
      moduleName := s!"Mux{numRegs}x{dataWidth}"
      instName := "u_mux_rd3"
      portMap := mux_in_map ++ mkMuxSelMap rd_tag3 ++ mkMuxOutMap rd_data3
    }

    let mux_rd4_inst : CircuitInstance := {
      moduleName := s!"Mux{numRegs}x{dataWidth}"
      instName := "u_mux_rd4"
      portMap := mux_in_map ++ mkMuxSelMap rd_tag4 ++ mkMuxOutMap rd_data4
    }

    -- Signal groups for next and reg internal wires (for Vec grouping in Chisel)
    let next_groups := (List.range numRegs).map (fun i =>
      { name := s!"next_{i}",
        width := dataWidth,
        wires := (List.range dataWidth).map (fun j => getNext i j) })
    let reg_groups := (List.range numRegs).map (fun i =>
      { name := s!"reg_{i}",
        width := dataWidth,
        wires := (List.range dataWidth).map (fun j => getReg i j) })

    { name := s!"PhysRegFile_{numRegs}x{dataWidth}"
      inputs := [clock, reset, wr_en] ++ rd_tag1 ++ rd_tag2 ++ rd_tag3 ++ rd_tag4 ++ wr_tag ++ wr_data
      outputs := rd_data1 ++ rd_data2 ++ rd_data3 ++ rd_data4
      gates := we_gates ++ reset_buf_gates ++ write_mux_gates
      instances := [decoder_inst] ++ storage_instances ++ [mux_rd1_inst, mux_rd2_inst, mux_rd3_inst, mux_rd4_inst]
      -- V2 codegen annotations
      signalGroups := [
        { name := "rd_tag1", width := tagWidth, wires := rd_tag1 },
        { name := "rd_tag2", width := tagWidth, wires := rd_tag2 },
        { name := "rd_tag3", width := tagWidth, wires := rd_tag3 },
        { name := "rd_tag4", width := tagWidth, wires := rd_tag4 },
        { name := "wr_tag", width := tagWidth, wires := wr_tag },
        { name := "wr_data", width := dataWidth, wires := wr_data },
        { name := "rd_data1", width := dataWidth, wires := rd_data1 },
        { name := "rd_data2", width := dataWidth, wires := rd_data2 },
        { name := "rd_data3", width := dataWidth, wires := rd_data3 },
        { name := "rd_data4", width := dataWidth, wires := rd_data4 },
        { name := "write_sel", width := numRegs, wires := write_sel },
        { name := "we", width := numRegs, wires := we }
      ] ++ next_groups ++ reg_groups
    }
  else
    -- Dual write port W=2 (from PhysRegFile_W2.lean).
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

    -- Outputs
    let rd_data1 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data1_{i}")
    let rd_data2 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data2_{i}")
    let rd_data3 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data3_{i}")
    let rd_data4 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data4_{i}")

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
                rd_tag1 ++ rd_tag2 ++ rd_tag3 ++ rd_tag4
      outputs := rd_data1 ++ rd_data2 ++ rd_data3 ++ rd_data4
      gates := we_gates ++ write_mux_gates ++ rr_gates ++ rl_gates
      instances := [decoder0_inst, decoder1_inst] ++ storage_instances ++
                   [mkMux "u_mux_rd1" rd_tag1 rd_data1,
                    mkMux "u_mux_rd2" rd_tag2 rd_data2,
                    mkMux "u_mux_rd3" rd_tag3 rd_data3,
                    mkMux "u_mux_rd4" rd_tag4 rd_data4]
    }

/-- Physical Register File with 64 registers × 32 bits, superscalar (dual write ports) -/
def mkPhysRegFile64 : Circuit := mkPhysRegFile 64 32 2

/-- Small Physical Register File for proof testing (4 registers × 8 bits) -/
def mkPhysRegFile4x8 : Circuit := mkPhysRegFile 4 8 1

/-- Config-driven Physical Register File -/
def mkPhysRegFileFromConfig (config : Shoumei.RISCV.CPUConfig) : Circuit :=
  mkPhysRegFile config.numPhysRegs 32 config.dispatchWidth

end Shoumei.RISCV.Renaming

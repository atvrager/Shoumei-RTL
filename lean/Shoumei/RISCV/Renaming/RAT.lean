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
          rs1_addr[4:0], rs2_addr[4:0]
- Outputs: rs1_data[tagWidth-1:0], rs2_data[tagWidth-1:0]

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

  -- Outputs
  let rs1_data := (List.range tagWidth).map (fun i => Wire.mk s!"rs1_data_{i}")
  let rs2_data := (List.range tagWidth).map (fun i => Wire.mk s!"rs2_data_{i}")

  -- Internal: Write Decoder (5→32 one-hot)
  let write_sel := (List.range numArchRegs).map (fun i => Wire.mk s!"write_sel_{i}")

  let decoder_inst : CircuitInstance := {
    moduleName := s!"Decoder{addrWidth}"
    instName := "u_write_dec"
    portMap :=
      (write_addr.enum.map (fun ⟨i, w⟩ => (s!"in{i}", w))) ++
      (write_sel.enum.map (fun ⟨i, w⟩ => (s!"out{i}", w)))
  }

  -- Internal: Per-entry write enable
  -- we_i = write_en AND write_sel_i
  let we := (List.range numArchRegs).map (fun i => Wire.mk s!"we_{i}")
  let we_gates := (List.range numArchRegs).map (fun i =>
    Gate.mkAND write_en (write_sel[i]!) (we[i]!))

  -- Internal: Storage registers
  -- On write, reg[i] = we[i] ? write_data : reg[i] (hold)
  -- On reset, all DFFs reset to 0 (initialization done externally via write port)
  --
  -- Note: After reset, all regs map to phys reg 0. The CPU pipeline must
  -- initialize the identity mapping (reg[i] = i) before dispatching instructions.
  -- This matches standard hardware practice where RAT init is a startup sequence.
  let getReg (i j : Nat) : Wire := Wire.mk s!"reg_{i}_{j}"
  let getNext (i j : Nat) : Wire := Wire.mk s!"next_{i}_{j}"

  let storage_gates := (List.range numArchRegs).map (fun i =>
    (List.range tagWidth).map (fun j =>
      let reg := getReg i j
      let next := getNext i j
      [
        -- Write data mux: next = we ? write_data : reg (hold)
        Gate.mkMUX reg (write_data[j]!) (we[i]!) next,
        -- Storage DFF (resets to 0)
        Gate.mkDFF next clock reset reg
      ]
    )
  ) |>.flatten |>.flatten

  -- Read Port 1 & 2: Mux32x6 for rs1/rs2
  -- Mux32x6 uses bundled ports (>100 ports): inputs[idx], outputs[idx]
  let totalMuxPorts := numArchRegs * tagWidth + addrWidth + tagWidth
  let useBundle := totalMuxPorts > 100

  let mux_in_map := if useBundle then
      (List.range numArchRegs).map (fun i =>
        (List.range tagWidth).map (fun j =>
          let idx := i * tagWidth + j
          (s!"inputs[{idx}]", getReg i j)
        )
      ) |>.flatten
    else
      (List.range numArchRegs).map (fun i =>
        (List.range tagWidth).map (fun j =>
          (s!"in{i}_b{j}", getReg i j)
        )
      ) |>.flatten

  let mkMuxSelMap (addr : List Wire) := if useBundle then
      addr.enum.map (fun ⟨i, w⟩ =>
        let idx := numArchRegs * tagWidth + i
        (s!"inputs[{idx}]", w))
    else
      addr.enum.map (fun ⟨i, w⟩ => (s!"sel{i}", w))

  let mkMuxOutMap (data : List Wire) := if useBundle then
      data.enum.map (fun ⟨i, w⟩ => (s!"outputs[{i}]", w))
    else
      data.enum.map (fun ⟨i, w⟩ => (s!"out{i}", w))

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

  { name := s!"RAT_{numArchRegs}x{tagWidth}"
    inputs := [clock, reset, write_en] ++ write_addr ++ write_data ++ rs1_addr ++ rs2_addr
    outputs := rs1_data ++ rs2_data
    gates := we_gates ++ storage_gates
    instances := [decoder_inst, mux_rs1_inst, mux_rs2_inst]
  }

/-- RAT with 64 physical registers (default configuration) -/
def mkRAT64 : Circuit := mkRAT 64

end Shoumei.RISCV.Renaming

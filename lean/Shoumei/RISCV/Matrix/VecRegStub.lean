/-
RISCV/Matrix/VecRegStub.lean - Vector Register File Stub for VME

Temporary stand-in for the full vector register file (V extension).
Provides 32 registers × VLEN bits each with 2 read ports and 1 write port.
When the V extension branch merges, replace this with the real vector register file.

Design follows PhysRegFile pattern:
- Storage: 32 × VLEN-bit DFF registers
- Write decoder: Decoder5 (5→32 one-hot)
- Read mux 1: Mux tree for vs1 read port
- Read mux 2: Mux tree for vs2 read port
- Write enable: AND(wr_en, decoder output) per entry
-/

import Shoumei.DSL
import Shoumei.RISCV.Config
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Sequential.Register

namespace Shoumei.RISCV.Matrix

open Shoumei
open Shoumei.Circuits.Combinational

/-! ## Behavioral Model -/

/-- Vector register file state: 32 registers of VLEN bits each.
    Each register is represented as a list of UInt32 words. -/
structure VecRegStubState (numRegs : Nat) (vlen : Nat) where
  /-- Register contents: vreg index → bit position → Bool -/
  regs : Fin numRegs → Fin vlen → Bool

/-- Read a vector register (asynchronous) -/
def VecRegStubState.read (vrf : VecRegStubState n v) (idx : Fin n) : Fin v → Bool :=
  vrf.regs idx

/-- Write a vector register (synchronous) -/
def VecRegStubState.write (vrf : VecRegStubState n v) (idx : Fin n) (val : Fin v → Bool)
    : VecRegStubState n v :=
  { regs := fun i => if i == idx then val else vrf.regs i }

/-- Initialize all registers to zero -/
def VecRegStubState.init (n v : Nat) : VecRegStubState n v :=
  { regs := fun _ _ => false }

/-- Read two registers simultaneously (for vs1, vs2 operand fetch) -/
def VecRegStubState.readPair (vrf : VecRegStubState n v) (idx1 idx2 : Fin n)
    : (Fin v → Bool) × (Fin v → Bool) :=
  (vrf.read idx1, vrf.read idx2)

/-! ## Structural Circuit -/

/-- Helper: compute log2 ceiling -/
private def log2Ceil (n : Nat) : Nat :=
  if n <= 1 then 0
  else Nat.log2 n + (if 2^(Nat.log2 n) < n then 1 else 0)

/-- Build a Vector Register File Stub circuit.

    Parameters:
    - numRegs: Number of vector registers (default 32)
    - vlen: Vector length in bits (default 128)

    Ports:
    - Inputs: clock, reset, wr_en, rd_idx1[4:0], rd_idx2[4:0],
              wr_idx[4:0], wr_data[vlen-1:0]
    - Outputs: rd_data1[vlen-1:0], rd_data2[vlen-1:0]

    Architecture:
    - 32 × 128-bit RegisterN instances (hierarchical)
    - Decoder5 for write address decode
    - Two read mux trees for vs1/vs2 read ports
-/
def mkVecRegStub (numRegs : Nat := 32) (vlen : Nat := 128) : Circuit :=
  let idxWidth := log2Ceil numRegs  -- 5 for 32 regs

  -- Inputs
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let wr_en := Wire.mk "wr_en"
  let rd_idx1 := (List.range idxWidth).map (fun i => Wire.mk s!"rd_idx1_{i}")
  let rd_idx2 := (List.range idxWidth).map (fun i => Wire.mk s!"rd_idx2_{i}")
  let wr_idx := (List.range idxWidth).map (fun i => Wire.mk s!"wr_idx_{i}")
  let wr_data := (List.range vlen).map (fun i => Wire.mk s!"wr_data_{i}")

  -- Outputs
  let rd_data1 := (List.range vlen).map (fun i => Wire.mk s!"rd_data1_{i}")
  let rd_data2 := (List.range vlen).map (fun i => Wire.mk s!"rd_data2_{i}")

  -- Write decoder (5→32 one-hot)
  let write_sel := (List.range numRegs).map (fun i => Wire.mk s!"write_sel_{i}")
  let decoder_inst : CircuitInstance := {
    moduleName := s!"Decoder{idxWidth}"
    instName := "u_write_dec"
    portMap :=
      (wr_idx.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (write_sel.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- Per-entry write enable: we_i = wr_en AND write_sel_i
  let we := (List.range numRegs).map (fun i => Wire.mk s!"we_{i}")
  let we_gates := (List.range numRegs).map (fun i =>
    Gate.mkAND wr_en (write_sel[i]!) (we[i]!))

  -- Storage registers (each RegisterN_128 or hierarchical)
  -- For each register entry, we need a RegisterN with write enable mux
  let reg_out : List (List Wire) := (List.range numRegs).map (fun r =>
    (List.range vlen).map (fun b => Wire.mk s!"reg_{r}_{b}"))

  -- Write data mux: for each entry, select between hold (reg_out) and new data (wr_data)
  let mux_out : List (List Wire) := (List.range numRegs).map (fun r =>
    (List.range vlen).map (fun b => Wire.mk s!"mux_{r}_{b}"))

  let write_mux_gates : List Gate := (List.range numRegs).flatMap (fun r =>
    (List.range vlen).map (fun b =>
      Gate.mkMUX ((reg_out[r]!)[b]!) (wr_data[b]!) (we[r]!) ((mux_out[r]!)[b]!)))

  -- DFF storage
  let dff_gates : List Gate := (List.range numRegs).flatMap (fun r =>
    (List.range vlen).map (fun b =>
      Gate.mkDFF ((mux_out[r]!)[b]!) clock reset ((reg_out[r]!)[b]!)))

  -- Read mux for port 1: for each output bit, 32:1 mux selected by rd_idx1
  -- Use simple gate-level mux (AND-OR tree)
  let rd1_and : List (List Wire) := (List.range vlen).map (fun b =>
    (List.range numRegs).map (fun r => Wire.mk s!"rd1_and_{b}_{r}"))

  -- Decode rd_idx1 to one-hot
  let rd1_sel := (List.range numRegs).map (fun i => Wire.mk s!"rd1_sel_{i}")
  let rd1_dec_inst : CircuitInstance := {
    moduleName := s!"Decoder{idxWidth}"
    instName := "u_rd1_dec"
    portMap :=
      (rd_idx1.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (rd1_sel.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- AND each reg output with its select, then OR-reduce
  let rd1_and_gates : List Gate := (List.range vlen).flatMap (fun b =>
    (List.range numRegs).map (fun r =>
      Gate.mkAND ((reg_out[r]!)[b]!) (rd1_sel[r]!) ((rd1_and[b]!)[r]!)))

  -- OR-reduce for read port 1 (chain of ORs)
  let rd1_or : List (List Wire) := (List.range vlen).map (fun b =>
    (List.range numRegs).map (fun r => Wire.mk s!"rd1_or_{b}_{r}"))

  let rd1_or_gates : List Gate := (List.range vlen).flatMap (fun b =>
    (List.range numRegs).map (fun r =>
      if r == 0 then
        Gate.mkBUF ((rd1_and[b]!)[0]!) ((rd1_or[b]!)[0]!)
      else
        Gate.mkOR ((rd1_or[b]!)[r - 1]!) ((rd1_and[b]!)[r]!) ((rd1_or[b]!)[r]!)))

  -- Connect last OR output to rd_data1
  let rd1_out_gates := (List.range vlen).map (fun b =>
    Gate.mkBUF ((rd1_or[b]!)[numRegs - 1]!) (rd_data1[b]!))

  -- Same for read port 2
  let rd2_sel := (List.range numRegs).map (fun i => Wire.mk s!"rd2_sel_{i}")
  let rd2_dec_inst : CircuitInstance := {
    moduleName := s!"Decoder{idxWidth}"
    instName := "u_rd2_dec"
    portMap :=
      (rd_idx2.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (rd2_sel.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  let rd2_and : List (List Wire) := (List.range vlen).map (fun b =>
    (List.range numRegs).map (fun r => Wire.mk s!"rd2_and_{b}_{r}"))

  let rd2_and_gates : List Gate := (List.range vlen).flatMap (fun b =>
    (List.range numRegs).map (fun r =>
      Gate.mkAND ((reg_out[r]!)[b]!) (rd2_sel[r]!) ((rd2_and[b]!)[r]!)))

  let rd2_or : List (List Wire) := (List.range vlen).map (fun b =>
    (List.range numRegs).map (fun r => Wire.mk s!"rd2_or_{b}_{r}"))

  let rd2_or_gates : List Gate := (List.range vlen).flatMap (fun b =>
    (List.range numRegs).map (fun r =>
      if r == 0 then
        Gate.mkBUF ((rd2_and[b]!)[0]!) ((rd2_or[b]!)[0]!)
      else
        Gate.mkOR ((rd2_or[b]!)[r - 1]!) ((rd2_and[b]!)[r]!) ((rd2_or[b]!)[r]!)))

  let rd2_out_gates := (List.range vlen).map (fun b =>
    Gate.mkBUF ((rd2_or[b]!)[numRegs - 1]!) (rd_data2[b]!))

  { name := s!"VecRegStub{numRegs}x{vlen}"
    inputs := [clock, reset, wr_en] ++ rd_idx1 ++ rd_idx2 ++ wr_idx ++ wr_data
    outputs := rd_data1 ++ rd_data2
    gates := we_gates ++ write_mux_gates ++ dff_gates ++
             rd1_and_gates ++ rd1_or_gates ++ rd1_out_gates ++
             rd2_and_gates ++ rd2_or_gates ++ rd2_out_gates
    instances := [decoder_inst, rd1_dec_inst, rd2_dec_inst]
    signalGroups := [
      { name := "rd_idx1", width := idxWidth, wires := rd_idx1 },
      { name := "rd_idx2", width := idxWidth, wires := rd_idx2 },
      { name := "wr_idx", width := idxWidth, wires := wr_idx },
      { name := "wr_data", width := vlen, wires := wr_data },
      { name := "rd_data1", width := vlen, wires := rd_data1 },
      { name := "rd_data2", width := vlen, wires := rd_data2 }
    ]
  }

/-- Default vector register stub: 32 regs × 128 bits -/
def mkVecRegStub32x128 : Circuit := mkVecRegStub 32 128

/-- Convenience alias -/
def vecRegStub : Circuit := mkVecRegStub32x128

end Shoumei.RISCV.Matrix

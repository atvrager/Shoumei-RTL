/-
RISCV/Matrix/VecRegStub.lean - Vector Register File Stub for VME

Temporary stand-in for the full vector register file (V extension).
Provides 32 registers × VLEN bits each with 2 read ports and 1 write port.
When the V extension branch merges, replace this with the real vector register file.

Design follows PhysRegFile pattern (hierarchical):
- Storage: 32 × RegisterN(VLEN) instances
- Write decoder: Decoder5 (5→32 one-hot)
- Read: Decoder5 for each read port + AND-OR mux per bit
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

/-! ## Structural Circuit (Hierarchical) -/

/-- Helper: compute log2 ceiling -/
private def log2Ceil (n : Nat) : Nat :=
  if n <= 1 then 0
  else Nat.log2 n + (if 2^(Nat.log2 n) < n then 1 else 0)

private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map fun i => Wire.mk s!"{name}_{i}"

/-- Build a Vector Register File Stub circuit (hierarchical).

    Parameters:
    - numRegs: Number of vector registers (default 32)
    - vlen: Vector length in bits (default 128)

    Ports:
    - Inputs: clock, reset, wr_en, rd_idx1[4:0], rd_idx2[4:0],
              wr_idx[4:0], wr_data[vlen-1:0]
    - Outputs: rd_data1[vlen-1:0], rd_data2[vlen-1:0]

    Architecture (hierarchical):
    - 32 × RegisterN(vlen) sub-instances for storage
    - 3 × Decoder5 instances (write decode, read1 decode, read2 decode)
    - Glue gates: write-enable AND, read AND-OR muxes
-/
def mkVecRegStub (numRegs : Nat := 32) (vlen : Nat := 128) : Circuit :=
  let idxWidth := log2Ceil numRegs  -- 5 for 32 regs

  -- Inputs
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let wr_en := Wire.mk "wr_en"
  let rd_idx1 := makeIndexedWires "rd_idx1" idxWidth
  let rd_idx2 := makeIndexedWires "rd_idx2" idxWidth
  let wr_idx := makeIndexedWires "wr_idx" idxWidth
  let wr_data := makeIndexedWires "wr_data" vlen

  -- Outputs
  let rd_data1 := makeIndexedWires "rd_data1" vlen
  let rd_data2 := makeIndexedWires "rd_data2" vlen

  -- Write decoder (5→32 one-hot)
  let write_sel := makeIndexedWires "write_sel" numRegs
  let decoder_inst : CircuitInstance := {
    moduleName := s!"Decoder{idxWidth}"
    instName := "u_write_dec"
    portMap :=
      (List.range idxWidth).map (fun i => (s!"in_{i}", wr_idx[i]!)) ++
      (List.range numRegs).map (fun i => (s!"out_{i}", write_sel[i]!))
  }

  -- Per-entry write enable: we_i = wr_en AND write_sel_i
  let we := makeIndexedWires "we" numRegs
  let we_gates := (List.range numRegs).map (fun i =>
    Gate.mkAND wr_en (write_sel[i]!) (we[i]!))

  -- Storage: hierarchical RegisterN instances
  -- Each register has: clock, reset, en (=we_i), d[vlen-1:0] (=wr_data), q[vlen-1:0]
  let reg_out : List (List Wire) := (List.range numRegs).map (fun r =>
    makeIndexedWires s!"reg_{r}" vlen)

  let reg_instances : List CircuitInstance := (List.range numRegs).map (fun r =>
    { moduleName := s!"Register{vlen}"
      instName := s!"u_reg_{r}"
      portMap :=
        [("clock", clock), ("reset", reset), ("en", we[r]!)] ++
        (List.range vlen).map (fun b => (s!"d_{b}", wr_data[b]!)) ++
        (List.range vlen).map (fun b => (s!"q_{b}", (reg_out[r]!)[b]!))
    })

  -- Read port 1: decoder + AND-OR mux
  let rd1_sel := makeIndexedWires "rd1_sel" numRegs
  let rd1_dec_inst : CircuitInstance := {
    moduleName := s!"Decoder{idxWidth}"
    instName := "u_rd1_dec"
    portMap :=
      (List.range idxWidth).map (fun i => (s!"in_{i}", rd_idx1[i]!)) ++
      (List.range numRegs).map (fun i => (s!"out_{i}", rd1_sel[i]!))
  }

  -- AND each reg output with its select, then OR-reduce
  let rd1_and_gates : List Gate := (List.range vlen).flatMap (fun b =>
    (List.range numRegs).map (fun r =>
      Gate.mkAND ((reg_out[r]!)[b]!) (rd1_sel[r]!)
        (Wire.mk s!"rd1_and_{b}_{r}")))

  let rd1_or_gates : List Gate := (List.range vlen).flatMap (fun b =>
    (List.range numRegs).map (fun r =>
      if r == 0 then
        Gate.mkBUF (Wire.mk s!"rd1_and_{b}_0") (Wire.mk s!"rd1_or_{b}_0")
      else
        Gate.mkOR (Wire.mk s!"rd1_or_{b}_{r-1}") (Wire.mk s!"rd1_and_{b}_{r}")
          (Wire.mk s!"rd1_or_{b}_{r}")))

  let rd1_out_gates := (List.range vlen).map (fun b =>
    Gate.mkBUF (Wire.mk s!"rd1_or_{b}_{numRegs-1}") (rd_data1[b]!))

  -- Read port 2: decoder + AND-OR mux
  let rd2_sel := makeIndexedWires "rd2_sel" numRegs
  let rd2_dec_inst : CircuitInstance := {
    moduleName := s!"Decoder{idxWidth}"
    instName := "u_rd2_dec"
    portMap :=
      (List.range idxWidth).map (fun i => (s!"in_{i}", rd_idx2[i]!)) ++
      (List.range numRegs).map (fun i => (s!"out_{i}", rd2_sel[i]!))
  }

  let rd2_and_gates : List Gate := (List.range vlen).flatMap (fun b =>
    (List.range numRegs).map (fun r =>
      Gate.mkAND ((reg_out[r]!)[b]!) (rd2_sel[r]!)
        (Wire.mk s!"rd2_and_{b}_{r}")))

  let rd2_or_gates : List Gate := (List.range vlen).flatMap (fun b =>
    (List.range numRegs).map (fun r =>
      if r == 0 then
        Gate.mkBUF (Wire.mk s!"rd2_and_{b}_0") (Wire.mk s!"rd2_or_{b}_0")
      else
        Gate.mkOR (Wire.mk s!"rd2_or_{b}_{r-1}") (Wire.mk s!"rd2_and_{b}_{r}")
          (Wire.mk s!"rd2_or_{b}_{r}")))

  let rd2_out_gates := (List.range vlen).map (fun b =>
    Gate.mkBUF (Wire.mk s!"rd2_or_{b}_{numRegs-1}") (rd_data2[b]!))

  { name := s!"VecRegStub{numRegs}x{vlen}"
    inputs := [clock, reset, wr_en] ++ rd_idx1 ++ rd_idx2 ++ wr_idx ++ wr_data
    outputs := rd_data1 ++ rd_data2
    gates := we_gates ++
             rd1_and_gates ++ rd1_or_gates ++ rd1_out_gates ++
             rd2_and_gates ++ rd2_or_gates ++ rd2_out_gates
    instances := [decoder_inst, rd1_dec_inst, rd2_dec_inst] ++ reg_instances
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

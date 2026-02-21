import Shoumei.DSL
import Shoumei.RISCV.Config
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Circuits.Sequential.DFF
import Shoumei.Circuits.Sequential.Register

namespace Shoumei.RISCV.Renaming

open Shoumei
open Shoumei.Circuits.Combinational

/--
Build a Physical Register File circuit with 2 write ports (W=2).

Parameters:
- numRegs: Number of physical registers (default 64)
- dataWidth: Width of each register in bits (default 32)

Ports:
- Inputs: clock, reset
- Write Port 0: wr_en_0, wr_tag_0[5:0], wr_data_0[31:0]
- Write Port 1: wr_en_1, wr_tag_1[5:0], wr_data_1[31:0]
- Read Ports: rd_tag1..rd_tag4 [5:0]
- Outputs: rd_data1..rd_data4 [31:0]

Note: Write port 1 has priority over write port 0 if they target the same register in the same cycle.
-/
def mkPhysRegFile_W2 (numRegs : Nat := 64) (dataWidth : Nat := 32) : Circuit :=
  let tagWidth := 6

  -- Inputs
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
  let rd_tag3 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag3_{i}")
  let rd_tag4 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag4_{i}")

  -- Outputs
  let rd_data1 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data1_{i}")
  let rd_data2 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data2_{i}")
  let rd_data3 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data3_{i}")
  let rd_data4 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data4_{i}")

  -- Decoders
  let write_sel_0 := (List.range numRegs).map (fun i => Wire.mk s!"write_sel_0_{i}")
  let decoder0_inst : CircuitInstance := {
    moduleName := s!"Decoder{tagWidth}"
    instName := "u_write_dec_0"
    portMap := (wr_tag_0.enum.map fun ⟨i,w⟩ => (s!"in_{i}", w)) ++ (write_sel_0.enum.map fun ⟨i,w⟩ => (s!"out_{i}", w))
  }
  
  let write_sel_1 := (List.range numRegs).map (fun i => Wire.mk s!"write_sel_1_{i}")
  let decoder1_inst : CircuitInstance := {
    moduleName := s!"Decoder{tagWidth}"
    instName := "u_write_dec_1"
    portMap := (wr_tag_1.enum.map fun ⟨i,w⟩ => (s!"in_{i}", w)) ++ (write_sel_1.enum.map fun ⟨i,w⟩ => (s!"out_{i}", w))
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
    )
  ) |>.flatten

  -- Reset tree
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

  { name := s!"PhysRegFile_{numRegs}x{dataWidth}_W2"
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

def physRegFile64W2 : Circuit := mkPhysRegFile_W2 64 32

end Shoumei.RISCV.Renaming

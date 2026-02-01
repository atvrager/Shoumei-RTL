/-
Circuits/Sequential/QueueComponents.lean - Helper components for QueueN
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Circuits.Combinational.RippleCarryAdder
import Shoumei.Circuits.Sequential.DFF

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Circuits.Combinational

-- Helper: Compute log2 ceiling
private def log2Ceil (n : Nat) : Nat :=
  if n <= 1 then 0
  else Nat.log2 n + (if 2^(Nat.log2 n) < n then 1 else 0)

-- Multi-port RAM (1 Read, 1 Write)
-- Inputs: clock, reset, write_en, write_addr, write_data, read_addr
-- Outputs: read_data
def mkQueueRAM (depth width : Nat) : Circuit :=
  let addrWidth := log2Ceil depth
  
  -- Inputs
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let write_en := Wire.mk "write_en"
  let write_addr := (List.range addrWidth).map (fun i => Wire.mk s!"write_addr_{i}")
  let write_data := (List.range width).map (fun i => Wire.mk s!"write_data_{i}")
  let read_addr := (List.range addrWidth).map (fun i => Wire.mk s!"read_addr_{i}")
  
  -- Outputs
  let read_data := (List.range width).map (fun i => Wire.mk s!"read_data_{i}")

  -- Internal Logic
  -- 1. Write Decoder Instance
  let write_sel := (List.range depth).map (fun i => Wire.mk s!"write_sel_{i}")
  let decoderName := s!"Decoder{addrWidth}"
  
  let decoder_inst : CircuitInstance := {
    moduleName := decoderName
    instName := "u_dec"
    portMap := 
      (write_addr.enum.map (fun ⟨i, w⟩ => (s!"in{i}", w))) ++ 
      (write_sel.enum.map (fun ⟨i, w⟩ => (s!"out{i}", w)))
  }

  -- 2. Write Enable Logic
  -- write_en_i = write_en && write_sel_i
  let write_en_i := (List.range depth).map (fun i => Wire.mk s!"we_{i}")
  let we_gates := (List.range depth).map (fun i =>
    Gate.mkAND write_en (write_sel.get! i) (write_en_i.get! i))

  -- 3. Storage Elements
  -- We need to access storage wires easily, so helper function
  let getReg (i j : Nat) : Wire := Wire.mk s!"mem_{i}_{j}"
  let getNext (i j : Nat) : Wire := Wire.mk s!"next_{i}_{j}"

  let storage_logic := (List.range depth).map (fun i =>
    (List.range width).map (fun j =>
      let reg := getReg i j
      let next := getNext i j
      [
        Gate.mkMUX reg (write_data.get! j) (write_en_i.get! i) next,
        Gate.mkDFF next clock reset reg
      ]
    )
  ) |>.flatten |>.flatten

  -- 4. Read MuxTree Instance
  let muxTreeName := s!"Mux{depth}x{width}"
  let totalMuxPorts := depth * width + addrWidth + width
  let useBundle := totalMuxPorts > 100

  let mux_in_map := if useBundle then
      (List.range depth).map (fun i =>
        (List.range width).map (fun j =>
           let idx := i * width + j
           (s!"inputs[{idx}]", getReg i j)
        )
      ) |>.flatten
    else
      (List.range depth).map (fun i =>
          (List.range width).map (fun j =>
            (s!"in{i}_b{j}", getReg i j)
          )
      ) |>.flatten
  
  let mux_sel_map := if useBundle then
      read_addr.enum.map (fun ⟨i, w⟩ => 
        let idx := depth * width + i
        (s!"inputs[{idx}]", w))
    else
      read_addr.enum.map (fun ⟨i, w⟩ => (s!"sel{i}", w))

  let mux_out_map := if useBundle then
      read_data.enum.map (fun ⟨i, w⟩ => (s!"outputs[{i}]", w))
    else
      read_data.enum.map (fun ⟨i, w⟩ => (s!"out{i}", w))
  
  let mux_inst : CircuitInstance := {
    moduleName := muxTreeName
    instName := "u_mux"
    portMap := mux_in_map ++ mux_sel_map ++ mux_out_map
  }

  { name := s!"QueueRAM_{depth}x{width}"
    inputs := [clock, reset, write_en] ++ write_addr ++ write_data ++ read_addr
    outputs := read_data
    gates := we_gates ++ storage_logic
    instances := [decoder_inst, mux_inst]
  }

-- Simple Up Counter with Enable and Wrap
-- Inputs: clock, reset, en
-- Outputs: count
def mkQueuePointer (width : Nat) : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let en := Wire.mk "en"
  let count := (List.range width).map (fun i => Wire.mk s!"count_{i}")
  
  -- Constants
  let one := Wire.mk "one"
  let zero := Wire.mk "zero"
  
  -- Logic
  -- next = en ? count + 1 : count
  -- Adder
  let inc := (List.range width).map (fun i => Wire.mk s!"inc_{i}")
  let carries := (List.range (width + 1)).map (fun i => Wire.mk s!"c_{i}")
  
  -- Create constant 1 vector: [1, 0, 0...]
  let one_vec := one :: (List.range (width - 1)).map (fun _ => zero)
  
  let adder_gates := buildFullAdderChain count one_vec carries inc "add_"
  
  -- Mux next
  let next := (List.range width).map (fun i => Wire.mk s!"next_{i}")
  let mux_gates := (List.range width).map (fun i =>
    Gate.mkMUX (count.get! i) (inc.get! i) en (next.get! i))
    
  -- DFFs
  let dff_gates := (List.range width).map (fun i =>
    Gate.mkDFF (next.get! i) clock reset (count.get! i))
    
  { name := s!"QueuePointer_{width}"
    inputs := [clock, reset, en, one, zero]
    outputs := count
    gates := [Gate.mkBUF one (carries.get! 0)] ++ adder_gates ++ mux_gates ++ dff_gates
    instances := []
  }


-- Up/Down Counter with Enable
-- Inputs: clock, reset, inc, dec
-- Outputs: count
-- Logic:
-- inc=1, dec=0 -> count + 1
-- inc=0, dec=1 -> count - 1
-- otherwise -> count
def mkQueueCounterUpDown (width : Nat) : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let inc_en := Wire.mk "inc"
  let dec_en := Wire.mk "dec"
  let count := (List.range width).map (fun i => Wire.mk s!"count_{i}")
  
  -- Constants
  let one := Wire.mk "one"
  let zero := Wire.mk "zero"
  
  -- +1 Logic
  let val_plus := (List.range width).map (fun i => Wire.mk s!"plus_{i}")
  let c_plus := (List.range (width + 1)).map (fun i => Wire.mk s!"cp_{i}")
  let one_vec := one :: (List.range (width - 1)).map (fun _ => zero)
  let add_gates := buildFullAdderChain count one_vec c_plus val_plus "add_"

  -- -1 Logic
  -- val - 1 = val + 111...1
  let all_ones := (List.range width).map (fun _ => one)
  let val_minus := (List.range width).map (fun i => Wire.mk s!"minus_{i}")
  let c_minus := (List.range (width + 1)).map (fun i => Wire.mk s!"cm_{i}")
  -- We assume cin=0 for this addition (carries.get! 0 needs to be 0)
  -- But buildFullAdderChain connects carries[0].
  -- So we pass zero as carries[0].
  
  let sub_gates := buildFullAdderChain count all_ones c_minus val_minus "sub_"
  
  -- Mux Logic
  -- next = (inc & !dec) ? val_plus : ((dec & !inc) ? val_minus : val)
  
  let next := (List.range width).map (fun i => Wire.mk s!"next_{i}")
  let do_inc := Wire.mk "do_inc"
  let do_dec := Wire.mk "do_dec"
  let not_dec := Wire.mk "not_dec"
  let not_inc := Wire.mk "not_inc"
  
  let ctrl_gates := [
    Gate.mkNOT dec_en not_dec,
    Gate.mkAND inc_en not_dec do_inc, -- inc & !dec
    Gate.mkNOT inc_en not_inc,
    Gate.mkAND dec_en not_inc do_dec  -- dec & !inc
  ]
  
  -- Mux tree:
  -- m1 = do_dec ? val_minus : val
  -- next = do_inc ? val_plus : m1
  let mux_gates := (List.range width).map (fun i =>
    let m1 := Wire.mk s!"m1_{i}"
    [
      Gate.mkMUX (count.get! i) (val_minus.get! i) do_dec m1,
      Gate.mkMUX m1 (val_plus.get! i) do_inc (next.get! i)
    ]
  ) |>.flatten
  
  -- DFFs
  let dff_gates := (List.range width).map (fun i =>
    Gate.mkDFF (next.get! i) clock reset (count.get! i))
    
  { name := s!"QueueCounterUpDown_{width}"
    inputs := [clock, reset, inc_en, dec_en, one, zero]
    outputs := count
    gates := [Gate.mkBUF one (c_plus.get! 0), Gate.mkBUF zero (c_minus.get! 0)] ++ 
             add_gates ++ sub_gates ++ ctrl_gates ++ mux_gates ++ dff_gates
    instances := []
  }

end Shoumei.Circuits.Sequential

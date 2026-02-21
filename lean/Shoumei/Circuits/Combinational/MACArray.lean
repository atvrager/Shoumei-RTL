/-
Circuits/Combinational/MACArray.lean - MAC Array for VME

Grid of MAC units for parallel outer-product computation.
Parameterized by rows × cols and input element width.

For VLEN=128:
- MACArray16x16_8:  16×16 grid of MACUnit8 (int8 outer product)
- MACArray8x8_16:   8×8 grid of MACUnit16 (int16 outer product)

Architecture:
- rows × cols MACUnit instances (via CircuitInstance)
- Input vs1 is distributed across rows (element i → row i)
- Input vs2 is distributed across columns (element j → col j)
- acc_in and acc_out are flattened: acc[i*cols+j] maps to MACUnit[i][j]
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.MACUnit

namespace Shoumei.Circuits.Combinational

open Shoumei

/-- Build a parameterized MAC array.

    Parameters:
    - rows: Number of rows (elements from vs1)
    - cols: Number of columns (elements from vs2)
    - inputWidth: Element width in bits (8 or 16)

    Inputs:
    - vs1[rows*inputWidth-1:0]: Source vector 1 (packed elements)
    - vs2[cols*inputWidth-1:0]: Source vector 2 (packed elements)
    - acc_in[rows*cols*32-1:0]: Accumulator input (flattened 2D array)
    - zero: Constant 0

    Outputs:
    - acc_out[rows*cols*32-1:0]: Accumulator output (flattened 2D array)
-/
def mkMACArray (rows cols inputWidth : Nat) : Circuit :=
  let vs1Bits := rows * inputWidth
  let vs2Bits := cols * inputWidth
  let accBits := rows * cols * 32

  -- Inputs
  let vs1 := makeIndexedWires "vs1" vs1Bits
  let vs2 := makeIndexedWires "vs2" vs2Bits
  let acc_in := makeIndexedWires "acc_in" accBits
  let zero := Wire.mk "zero"

  -- Outputs
  let acc_out := makeIndexedWires "acc_out" accBits

  -- Module name for the MAC unit
  let macModuleName := s!"MACUnit{inputWidth}"

  -- Instantiate rows × cols MAC units
  let mac_instances : List CircuitInstance := (List.range rows).flatMap (fun i =>
    (List.range cols).map (fun j =>
      let flatIdx := i * cols + j
      -- Extract element i from vs1: bits [i*inputWidth+inputWidth-1 : i*inputWidth]
      let a_wires := (List.range inputWidth).map (fun k => vs1[i * inputWidth + k]!)
      -- Extract element j from vs2: bits [j*inputWidth+inputWidth-1 : j*inputWidth]
      let b_wires := (List.range inputWidth).map (fun k => vs2[j * inputWidth + k]!)
      -- Extract acc_in[flatIdx]: bits [flatIdx*32+31 : flatIdx*32]
      let acc_in_wires := (List.range 32).map (fun k => acc_in[flatIdx * 32 + k]!)
      -- acc_out[flatIdx]: bits [flatIdx*32+31 : flatIdx*32]
      let acc_out_wires := (List.range 32).map (fun k => acc_out[flatIdx * 32 + k]!)

      { moduleName := macModuleName
        instName := s!"u_mac_{i}_{j}"
        portMap :=
          (a_wires.enum.map (fun ⟨k, w⟩ => (s!"a_{k}", w))) ++
          (b_wires.enum.map (fun ⟨k, w⟩ => (s!"b_{k}", w))) ++
          (acc_in_wires.enum.map (fun ⟨k, w⟩ => (s!"acc_in_{k}", w))) ++
          [("zero", zero)] ++
          (acc_out_wires.enum.map (fun ⟨k, w⟩ => (s!"result_{k}", w)))
      }))

  { name := s!"MACArray{rows}x{cols}_{inputWidth}"
    inputs := vs1 ++ vs2 ++ acc_in ++ [zero]
    outputs := acc_out
    gates := []
    instances := mac_instances
    signalGroups := [
      { name := "vs1", width := vs1Bits, wires := vs1 },
      { name := "vs2", width := vs2Bits, wires := vs2 },
      { name := "acc_in", width := accBits, wires := acc_in },
      { name := "acc_out", width := accBits, wires := acc_out }
    ]
  }

/-- 16×16 int8 MAC array for VLEN=128 -/
def mkMACArray16x16_8 : Circuit := mkMACArray 16 16 8

/-- 8×8 int16 MAC array for VLEN=128 -/
def mkMACArray8x8_16 : Circuit := mkMACArray 8 8 16

end Shoumei.Circuits.Combinational

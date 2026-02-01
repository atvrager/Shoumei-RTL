import Shoumei.Circuits.Combinational.MuxTree

open Shoumei.Circuits.Combinational

#eval s!"Mux2x8 gates: {mkMux2x8.gates.length}"
#eval s!"Mux2x8 inputs: {mkMux2x8.inputs.length}"
#eval s!"Mux2x8 outputs: {mkMux2x8.outputs.length}"

#eval s!"Mux4x8 gates: {mkMux4x8.gates.length}"
#eval s!"Mux4x8 inputs: {mkMux4x8.inputs.length}"
#eval s!"Mux4x8 outputs: {mkMux4x8.outputs.length}"

#eval s!"Mux32x6 gates: {mkMux32x6.gates.length}"
#eval s!"Mux32x6 inputs: {mkMux32x6.inputs.length}"
#eval s!"Mux32x6 outputs: {mkMux32x6.outputs.length}"

#eval s!"Mux64x32 gates: {mkMux64x32.gates.length}"
#eval s!"Mux64x32 inputs: {mkMux64x32.inputs.length}"
#eval s!"Mux64x32 outputs: {mkMux64x32.outputs.length}"

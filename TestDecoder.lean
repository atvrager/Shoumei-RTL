import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.DecoderProofs

open Shoumei.Circuits.Combinational

#eval s!"Decoder2: {mkDecoder2.gates.length} gates"
#eval s!"Decoder3: {mkDecoder3.gates.length} gates"
#eval s!"Decoder5: {mkDecoder5.gates.length} gates"
#eval s!"Decoder6: {mkDecoder6.gates.length} gates"

-- Sample output structure
#eval s!"Decoder2 inputs: {mkDecoder2.inputs.length}, outputs: {mkDecoder2.outputs.length}"
#eval s!"Decoder5 inputs: {mkDecoder5.inputs.length}, outputs: {mkDecoder5.outputs.length}"

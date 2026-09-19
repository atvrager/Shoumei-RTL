/-
Interconnect/TileLink/TLTypes.lean - TileLink TL-UH (Uncached Heavyweight) Definitions

TileLink is the open-source, scalable chip-scale interconnect standard for RISC-V.
TL-UH supports:
- Get (read single beat / burst)
- PutFullData / PutPartialData (write single beat / burst with byte masks)
- ArithmeticData / LogicalData (atomic operations: ADD, SWAP, XOR, OR, AND, MIN, MAX)
- In-order responses with decoupled valid/ready handshakes.
-/

import Shoumei.DSL

namespace Shoumei.Interconnect.TileLink

open Shoumei

/-- TL-UH Channel A (Master -> Slave Request) Opcode constants -/
inductive TLOpcodeA where
  | PutFullData    : TLOpcodeA  -- 3'b000
  | PutPartialData : TLOpcodeA  -- 3'b001
  | ArithmeticData : TLOpcodeA  -- 3'b010 (Atomic)
  | LogicalData    : TLOpcodeA  -- 3'b011 (Atomic)
  | Get            : TLOpcodeA  -- 3'b100
  | Intent         : TLOpcodeA  -- 3'b101
deriving Repr, DecidableEq

def TLOpcodeA.toNat : TLOpcodeA → Nat
  | .PutFullData    => 0
  | .PutPartialData => 1
  | .ArithmeticData => 2
  | .LogicalData    => 3
  | .Get            => 4
  | .Intent         => 5

/-- TL-UH Channel D (Slave -> Master Response) Opcode constants -/
inductive TLOpcodeD where
  | AccessAck     : TLOpcodeD  -- 3'b000
  | AccessAckData : TLOpcodeD  -- 3'b001
deriving Repr, DecidableEq

def TLOpcodeD.toNat : TLOpcodeD → Nat
  | .AccessAck     => 0
  | .AccessAckData => 1

/-- Channel A wire bundle representation -/
structure ChannelAWires where
  valid   : Wire
  ready   : Wire
  opcode  : List Wire  -- 3 bits
  param   : List Wire  -- 3 bits
  size    : List Wire  -- 3 bits
  source  : List Wire  -- 4 bits
  address : List Wire  -- 32 bits
  mask    : List Wire  -- 8 bits
  data    : List Wire  -- 64 bits

/-- Channel D wire bundle representation -/
structure ChannelDWires where
  valid   : Wire
  ready   : Wire
  opcode  : List Wire  -- 3 bits
  param   : List Wire  -- 2 bits
  size    : List Wire  -- 3 bits
  source  : List Wire  -- 4 bits
  sink    : List Wire  -- 4 bits
  data    : List Wire  -- 64 bits
  denied  : Wire

/-- Helper to allocate Channel A wires with a prefix name -/
def makeChannelAWires (pfx : String) : ChannelAWires := {
  valid   := Wire.mk s!"{pfx}_a_valid"
  ready   := Wire.mk s!"{pfx}_a_ready"
  opcode  := (List.range 3).map fun i => Wire.mk s!"{pfx}_a_opcode_{i}"
  param   := (List.range 3).map fun i => Wire.mk s!"{pfx}_a_param_{i}"
  size    := (List.range 3).map fun i => Wire.mk s!"{pfx}_a_size_{i}"
  source  := (List.range 4).map fun i => Wire.mk s!"{pfx}_a_source_{i}"
  address := (List.range 32).map fun i => Wire.mk s!"{pfx}_a_address_{i}"
  mask    := (List.range 8).map fun i => Wire.mk s!"{pfx}_a_mask_{i}"
  data    := (List.range 64).map fun i => Wire.mk s!"{pfx}_a_data_{i}"
}

instance : Inhabited ChannelAWires where
  default := makeChannelAWires ""

/-- Helper to allocate Channel D wires with a prefix name -/
def makeChannelDWires (pfx : String) : ChannelDWires := {
  valid   := Wire.mk s!"{pfx}_d_valid"
  ready   := Wire.mk s!"{pfx}_d_ready"
  opcode  := (List.range 3).map fun i => Wire.mk s!"{pfx}_d_opcode_{i}"
  param   := (List.range 2).map fun i => Wire.mk s!"{pfx}_d_param_{i}"
  size    := (List.range 3).map fun i => Wire.mk s!"{pfx}_d_size_{i}"
  source  := (List.range 4).map fun i => Wire.mk s!"{pfx}_d_source_{i}"
  sink    := (List.range 4).map fun i => Wire.mk s!"{pfx}_d_sink_{i}"
  data    := (List.range 64).map fun i => Wire.mk s!"{pfx}_d_data_{i}"
  denied  := Wire.mk s!"{pfx}_d_denied"
}

instance : Inhabited ChannelDWires where
  default := makeChannelDWires ""

end Shoumei.Interconnect.TileLink

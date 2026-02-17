/-
RISCV/Memory/Cache/CacheTypes.lean - Cache Type Definitions

Address decomposition, FSM enums, and CacheLine types shared across L1I, L1D, and L2 caches.

Address layout (32-bit, 32B cache lines = 8 words):
  | Tag       | Index     | Offset (5 bits)           |
  |           |           | word[2:0] | byte[1:0]     |

  L1I: 24-bit tag, 3-bit index (8 sets), 5-bit offset
  L1D: 25-bit tag, 2-bit index (4 sets), 5-bit offset
  L2:  24-bit tag, 3-bit index (8 sets), 5-bit offset
-/

import Shoumei.DSL

namespace Shoumei.RISCV.Memory.Cache

open Shoumei

/-! ## Constants -/

abbrev L1ITagBits := 24
abbrev L1DTagBits := 25
abbrev L2TagBits  := 24

abbrev L1ISets := 8
abbrev L1DSets := 4
abbrev L2Sets  := 8

abbrev L1DWays := 2
abbrev L2Ways  := 2

abbrev CacheLineWords := 8  -- 8 words per cache line = 32 bytes

/-! ## Address Decomposition -/

/-- Extract the 3-bit word offset (bits [4:2]) from a 32-bit address. -/
def extractWordOffset (addr : UInt32) : Fin 8 :=
  ⟨(addr >>> 2).toNat % 8, Nat.mod_lt _ (by decide)⟩

/-- Extract the byte offset (bits [1:0]) from a 32-bit address. -/
def extractByteOffset (addr : UInt32) : Fin 4 :=
  ⟨addr.toNat % 4, Nat.mod_lt _ (by decide)⟩

/-- Extract the set index for L1I (3-bit, bits [7:5]). -/
def extractL1IIndex (addr : UInt32) : Fin 8 :=
  ⟨(addr >>> 5).toNat % 8, Nat.mod_lt _ (by decide)⟩

def extractL1ITag (addr : UInt32) : BitVec 24 :=
  (addr.toBitVec >>> 8).truncate 24

def extractL1DIndex (addr : UInt32) : Fin 4 :=
  ⟨(addr >>> 5).toNat % 4, Nat.mod_lt _ (by decide)⟩

def extractL1DTag (addr : UInt32) : BitVec 25 :=
  (addr.toBitVec >>> 7).truncate 25

def extractL2Index (addr : UInt32) : Fin 8 :=
  ⟨(addr >>> 5).toNat % 8, Nat.mod_lt _ (by decide)⟩

def extractL2Tag (addr : UInt32) : BitVec 24 :=
  (addr.toBitVec >>> 8).truncate 24

/-- Reconstruct the base address of a cache line from L1I tag + index. -/
def reconstructL1IAddr (tag : BitVec 24) (idx : Fin 8) : UInt32 :=
  ((tag.toNat <<< 8) ||| (idx.val <<< 5)).toUInt32

/-- Reconstruct the base address of a cache line from L1D tag + index. -/
def reconstructL1DAddr (tag : BitVec 25) (idx : Fin 4) : UInt32 :=
  ((tag.toNat <<< 7) ||| (idx.val <<< 5)).toUInt32

/-! ## Cache Line -/

/-- A single cache line with parameterized tag width. -/
structure CacheLine (tagBits : Nat) where
  /-- Line is valid (contains data) -/
  valid : Bool
  /-- Line is dirty (modified, needs writeback) -/
  dirty : Bool
  /-- Tag bits for address matching -/
  tag : BitVec tagBits
  /-- Data: 8 words (32 bytes) -/
  data : Fin 8 → UInt32

instance {n : Nat} : Inhabited (CacheLine n) where
  default := { valid := false, dirty := false, tag := 0, data := fun _ => 0 }

/-- Create an empty (invalid) cache line. -/
def CacheLine.empty {n : Nat} : CacheLine n := default

/-! ## FSM States -/

/-- L1 Instruction Cache FSM states. -/
inductive L1ICacheFSM where
  | IDLE        -- Ready for lookups
  | REFILL_REQ  -- Sending refill request to L2
  | REFILL_WAIT -- Waiting for L2 response (8 words)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- L1 Data Cache FSM states. -/
inductive L1DCacheFSM where
  | IDLE          -- Ready for lookups
  | WB_REQ        -- Sending writeback request to L2 (dirty eviction)
  | WB_WAIT       -- Waiting for writeback acknowledgement
  | REFILL_REQ    -- Sending refill request to L2
  | REFILL_WAIT   -- Waiting for L2 response
  | FENCE_I_WB    -- FENCE.I: writing back all dirty lines
  deriving Repr, BEq, DecidableEq, Inhabited

/-- L2 Cache FSM states. -/
inductive L2CacheFSM where
  | IDLE        -- Ready for requests
  | SERVE_I     -- Serving L1I miss
  | SERVE_D     -- Serving L1D miss/writeback
  | MEM_REQ     -- Sending request to main memory
  | MEM_WAIT    -- Waiting for main memory response
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Which L1 initiated an L2 request. -/
inductive CacheSource where
  | ICache  -- Request from L1I
  | DCache  -- Request from L1D
  deriving Repr, BEq, DecidableEq, Inhabited

end Shoumei.RISCV.Memory.Cache

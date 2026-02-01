/-
RISCV/Execution/MemoryExecUnit.lean - Memory/Load-Store Unit for RV32I

Calculates memory addresses for loads and stores.

Supported operations:
**Loads:**
- LB: Load byte (sign-extended)
- LH: Load halfword (sign-extended)
- LW: Load word
- LBU: Load byte unsigned
- LHU: Load halfword unsigned

**Stores:**
- SB: Store byte
- SH: Store halfword
- SW: Store word

Address calculation:
- Load: addr = rs1 + sign_extend(imm12)
- Store: addr = rs1 + sign_extend(imm12)

For RV32I, all memory operations:
1. Calculate effective address (base + offset)
2. For loads: issue memory read request, wait for data
3. For stores: issue memory write request with data

Note: Actual memory access is handled by the Memory System (Phase 7).
This unit only calculates addresses and prepares requests.

CDB Broadcast:
- Loads: Broadcast (dest_tag, loaded_data) when memory responds
- Stores: No CDB broadcast (write memory, no register result)

Simplified model:
- For now, assume synchronous memory (1-cycle latency)
- Phase 7 will add proper memory interface, store buffer, etc.
-/

import Shoumei.RISCV.ISA

namespace Shoumei.RISCV.Execution

open Shoumei.RISCV

/-! ## Address Calculation -/

/-- Calculate memory address.

    addr = base + offset

    Both loads and stores use the same address calculation.
-/
def calculateMemoryAddress
    (base : UInt32)  -- rs1 value
    (offset : Int)   -- Sign-extended immediate
    : UInt32 :=
  let offset_u32 := offset.toNat.toUInt32
  base + offset_u32

/-! ## Load Operations -/

/-- Memory access size. -/
inductive MemSize where
  | Byte      -- 8 bits
  | Halfword  -- 16 bits
  | Word      -- 32 bits
  deriving Repr, BEq

/-- Memory access type. -/
inductive MemAccessType where
  | Load   -- Read from memory
  | Store  -- Write to memory
  deriving Repr, BEq

/-- Memory request.

    Sent to memory system for processing.
-/
structure MemoryRequest where
  /-- Access type (load or store) -/
  access_type : MemAccessType
  /-- Access size (byte, halfword, word) -/
  size : MemSize
  /-- Sign-extend result? (only for loads) -/
  sign_extend : Bool
  /-- Memory address -/
  address : UInt32
  /-- Data to write (for stores) -/
  write_data : UInt32
  /-- Destination tag (for loads, ROB entry for stores) -/
  dest_tag : Fin 64
  deriving Repr

/-- Execute load instruction.

    Creates memory request for load operation.
-/
def executeLoad
    (opcode : OpType)
    (base : UInt32)      -- rs1 value
    (offset : Int)       -- Immediate offset
    (dest_tag : Fin 64)  -- Destination physical register
    : MemoryRequest :=
  let addr := calculateMemoryAddress base offset
  let (size, sign_ext) := match opcode with
    | .LB  => (MemSize.Byte, true)       -- Load byte, sign-extend
    | .LH  => (MemSize.Halfword, true)   -- Load halfword, sign-extend
    | .LW  => (MemSize.Word, false)      -- Load word (no extension needed)
    | .LBU => (MemSize.Byte, false)      -- Load byte unsigned
    | .LHU => (MemSize.Halfword, false)  -- Load halfword unsigned
    | _ => (MemSize.Word, false)         -- Invalid (shouldn't happen)

  { access_type := MemAccessType.Load
    size := size
    sign_extend := sign_ext
    address := addr
    write_data := 0  -- Unused for loads
    dest_tag := dest_tag
  }

/-! ## Store Operations -/

/-- Execute store instruction.

    Creates memory request for store operation.
-/
def executeStore
    (opcode : OpType)
    (base : UInt32)      -- rs1 value (address base)
    (offset : Int)       -- Immediate offset
    (data : UInt32)      -- rs2 value (data to store)
    (rob_tag : Fin 64)   -- ROB entry tag
    : MemoryRequest :=
  let addr := calculateMemoryAddress base offset
  let size := match opcode with
    | .SB => MemSize.Byte       -- Store byte
    | .SH => MemSize.Halfword   -- Store halfword
    | .SW => MemSize.Word       -- Store word
    | _ => MemSize.Word         -- Invalid (shouldn't happen)

  { access_type := MemAccessType.Store
    size := size
    sign_extend := false  -- Unused for stores
    address := addr
    write_data := data
    dest_tag := rob_tag
  }

/-! ## Memory Response Processing -/

/-- Process load response from memory.

    Performs sign/zero extension based on load type.
-/
def processLoadResponse
    (raw_data : UInt32)
    (size : MemSize)
    (sign_extend : Bool)
    : UInt32 :=
  match size with
  | MemSize.Byte =>
      let byte_val := raw_data % 256
      if sign_extend && byte_val >= 128 then
        -- Sign-extend: set upper 24 bits to 1
        byte_val ||| 0xFFFFFF00
      else
        byte_val
  | MemSize.Halfword =>
      let half_val := raw_data % 65536
      if sign_extend && half_val >= 32768 then
        -- Sign-extend: set upper 16 bits to 1
        half_val ||| 0xFFFF0000
      else
        half_val
  | MemSize.Word =>
      raw_data  -- No extension needed

/-! ## Simplified Memory Model (for testing) -/

/-- Simple memory model: byte-addressable RAM.

    For testing purposes. Phase 7 will implement proper memory system.
-/
structure SimpleMemory where
  /-- Memory contents (address -> value) -/
  mem : Fin 1024 → UInt8  -- 1KB memory for testing

namespace SimpleMemory

/-- Initialize empty memory (all zeros). -/
def init : SimpleMemory :=
  { mem := fun _ => 0 }

/-- Read byte from memory. -/
def readByte (m : SimpleMemory) (addr : Nat) (_h : addr < 1024 := by omega) : UInt8 :=
  m.mem ⟨addr, _h⟩

/-- Write byte to memory. -/
def writeByte (m : SimpleMemory) (addr : Nat) (value : UInt8) (_h : addr < 1024 := by omega) : SimpleMemory :=
  { m with mem := fun i => if i.val == addr then value else m.mem i }

/-- Read word (32 bits, little-endian). -/
def readWord (m : SimpleMemory) (addr : Nat) : UInt32 :=
  if h0 : addr < 1024 then
    if h1 : addr + 1 < 1024 then
      if h2 : addr + 2 < 1024 then
        if h3 : addr + 3 < 1024 then
          let b0 := (m.readByte addr h0).toNat
          let b1 := (m.readByte (addr + 1) h1).toNat
          let b2 := (m.readByte (addr + 2) h2).toNat
          let b3 := (m.readByte (addr + 3) h3).toNat
          (b0 + (b1 <<< 8) + (b2 <<< 16) + (b3 <<< 24)).toUInt32
        else 0
      else 0
    else 0
  else 0

end SimpleMemory

/-! ## Verification Helpers -/

/-- Verify load byte address calculation. -/
def verifyLoadAddress (base : UInt32) (offset : Int) : Bool :=
  let req := executeLoad OpType.LB base offset 0
  req.address == calculateMemoryAddress base offset

/-- Verify store word address calculation. -/
def verifyStoreAddress (base : UInt32) (offset : Int) : Bool :=
  let req := executeStore OpType.SW base offset 0 0
  req.address == calculateMemoryAddress base offset

end Shoumei.RISCV.Execution

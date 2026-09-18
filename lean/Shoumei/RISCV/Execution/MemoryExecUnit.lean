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
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.RISCV.Execution

open Shoumei.RISCV

/-! ## Address Calculation -/

/-- Calculate memory address.

    addr = base + offset

    Both loads and stores use the same address calculation.

    For negative offsets, converts to two's complement representation:
    - offset = -100 → 0xFFFFFF9C (4294967196 in decimal)
    - Then performs 32-bit modular addition
-/
def calculateMemoryAddress
    (base : UInt64)  -- rs1 value
    (offset : Int)   -- Sign-extended immediate
    : UInt64 :=
  let offset_u64 :=
    if offset >= 0 then
      offset.toNat.toUInt64
    else
      -- Two's complement: 2^64 + offset (when offset is negative)
      (18446744073709551616 + offset).toNat.toUInt64
  base + offset_u64

/-! ## Load Operations -/

/-- Memory access size. -/
inductive MemSize where
  | Byte        -- 8 bits
  | Halfword    -- 16 bits
  | Word        -- 32 bits
  | Doubleword  -- 64 bits
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
  /-- Access size (byte, halfword, word, doubleword) -/
  size : MemSize
  /-- Sign-extend result? (only for loads) -/
  sign_extend : Bool
  /-- Memory address -/
  address : UInt64
  /-- Data to write (for stores) -/
  write_data : UInt64
  /-- Destination tag (for loads, ROB entry for stores) -/
  dest_tag : Fin 64
  deriving Repr

/-- Execute load instruction.

    Creates memory request for load operation.
-/
def executeLoad
    (opcode : OpType)
    (base : UInt64)      -- rs1 value
    (offset : Int)       -- Immediate offset
    (dest_tag : Fin 64)  -- Destination physical register
    : MemoryRequest :=
  let addr := calculateMemoryAddress base offset
  let (size, sign_ext) := match opcode with
    | .LB  => (MemSize.Byte, true)
    | .LH  => (MemSize.Halfword, true)
    | .LW  => (MemSize.Word, true)
    | .LBU => (MemSize.Byte, false)
    | .LHU => (MemSize.Halfword, false)
    | .LWU => (MemSize.Word, false)
    | .LD  => (MemSize.Doubleword, false)
    | _ => (MemSize.Doubleword, false)

  { access_type := MemAccessType.Load
    size := size
    sign_extend := sign_ext
    address := addr
    write_data := 0
    dest_tag := dest_tag
  }

/-! ## Store Operations -/

/-- Execute store instruction.

    Creates memory request for store operation.
-/
def executeStore
    (opcode : OpType)
    (base : UInt64)      -- rs1 value (address base)
    (offset : Int)       -- Immediate offset
    (data : UInt64)      -- rs2 value (data to store)
    (rob_tag : Fin 64)   -- ROB entry tag
    : MemoryRequest :=
  let addr := calculateMemoryAddress base offset
  let size := match opcode with
    | .SB => MemSize.Byte
    | .SH => MemSize.Halfword
    | .SW => MemSize.Word
    | .SD => MemSize.Doubleword
    | _ => MemSize.Doubleword

  { access_type := MemAccessType.Store
    size := size
    sign_extend := false
    address := addr
    write_data := data
    dest_tag := rob_tag
  }

/-! ## Memory Response Processing -/

/-- Process load response from memory.

    Performs sign/zero extension based on load type.
-/
def processLoadResponse
    (raw_data : UInt64)
    (size : MemSize)
    (sign_extend : Bool)
    : UInt64 :=
  match size with
  | MemSize.Byte =>
      let byte_val := raw_data % 256
      if sign_extend && byte_val >= 128 then
        byte_val ||| 0xFFFFFFFFFFFFFF00
      else
        byte_val
  | MemSize.Halfword =>
      let half_val := raw_data % 65536
      if sign_extend && half_val >= 32768 then
        half_val ||| 0xFFFFFFFFFFFF0000
      else
        half_val
  | MemSize.Word =>
      let word_val := raw_data % 4294967296
      if sign_extend && word_val >= 2147483648 then
        word_val ||| 0xFFFFFFFF00000000
      else
        word_val
  | MemSize.Doubleword =>
      raw_data

/-! ## Structural Circuit -/

open Shoumei
open Shoumei.Circuits.Combinational

/-- Build Memory Execution Unit structural circuit (Address Generation Unit).

    **Architecture:**
    - Computes effective address: base + offset (64-bit)
    - Uses KoggeStoneAdder64
    - Adds tag pass-through for CDB broadcast
    - Single-cycle combinational execution

    **Inputs:**
    - base[63:0]: Source operand 1 (rs1 value, base address)
    - offset[63:0]: Immediate offset (sign-extended to 64 bits)
    - dest_tag[5:0]: Physical register tag for load result (or ROB tag for store)
    - zero: Constant input (for adder carry-in)

    **Outputs:**
    - address[63:0]: Computed memory address (base + offset)
    - tag_out[5:0]: Pass-through of dest_tag (for CDB broadcast)

    **Instances:**
    - KoggeStoneAdder64: 64-bit adder
-/
def mkMemoryExecUnit : Circuit :=
  let base := makeIndexedWires "base" 64
  let offset := makeIndexedWires "offset" 32
  let dest_tag := makeIndexedWires "dest_tag" 6

  let a := makeIndexedWires "a" 64
  let b := makeIndexedWires "b" 64
  let sum := makeIndexedWires "sum" 64

  let address := makeIndexedWires "address" 64
  let tag_out := makeIndexedWires "tag_out" 6

  let base_to_a := List.zipWith Gate.mkBUF base a
  let sign_n := (List.range 32).map (fun i => Wire.mk s!"sign_n_{i}")
  let offset_to_b :=
    (List.range 32).map (fun i => Gate.mkBUF offset[i]! b[i]!) ++
    (List.range 32).flatMap (fun i =>
      [Gate.mkNOT offset[31]! sign_n[i]!,
       Gate.mkNOT sign_n[i]! b[32 + i]!])

  let adder_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder64NoCin"
    instName := "u_adder"
    portMap :=
      (a.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (b.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      (sum.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }

  let sum_to_address := List.zipWith Gate.mkBUF sum address
  let not_tag := makeIndexedWires "not_dt" 6
  let not_not_tag := makeIndexedWires "not_not_dt" 6
  let tag_passthrough := (List.range 6).flatMap fun i =>
    [Gate.mkNOT (dest_tag[i]!) (not_tag[i]!),
     Gate.mkNOT (not_tag[i]!) (not_not_tag[i]!),
     Gate.mkAND (dest_tag[i]!) (not_not_tag[i]!) (tag_out[i]!)]

  { name := "MemoryExecUnit"
    inputs := base ++ offset ++ dest_tag
    outputs := address ++ tag_out
    gates := base_to_a ++ offset_to_b ++ sum_to_address ++ tag_passthrough
    instances := [adder_inst]
    signalGroups := [
      { name := "base", width := 64, wires := base },
      { name := "offset", width := 32, wires := offset },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "a", width := 64, wires := a },
      { name := "b", width := 64, wires := b },
      { name := "sum", width := 64, wires := sum },
      { name := "address", width := 64, wires := address },
      { name := "tag_out", width := 6, wires := tag_out }
    ]
  }

/-- Convenience constructor for Memory Execution Unit -/
def memoryExecUnit : Circuit := mkMemoryExecUnit

end Shoumei.RISCV.Execution

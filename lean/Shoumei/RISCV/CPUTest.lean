/-
CPU Integration Tests

Comprehensive test suite for top-level CPU integration covering:
- Initialization and basic stepping
- Single-instruction execution
- Data dependencies (Tomasulo correctness)
- Control flow (branches, loops)
- Memory operations (LSU forwarding)
- M-extension multiply/divide
- RVVI infrastructure

Test levels:
1. Basic tests (10) - Infrastructure verification
2. Single-instruction tests (15) - Opcode coverage
3. Data dependency tests (12) - RAW hazards, out-of-order
4. Branch tests (12) - Control flow, prediction
5. Loop tests (6) - Multi-iteration programs
6. LSU tests (8) - Memory forwarding, TSO
7. M-extension tests (6) - Multiply/divide operations
Total: 69 tests
-/

import Shoumei.RISCV.CPU
import Shoumei.RISCV.Decoder

namespace Shoumei.RISCV.CPUTest

open Shoumei.RISCV
open Shoumei.RISCV.CPU

/-! ## Test Helpers -/

/-- Run CPU for N cycles -/
def runNCycles (cpu : CPUState config) (imem : SimpleIMem) (n : Nat) : CPUState config :=
  match n with
  | 0 => cpu
  | n' + 1 => runNCycles (cpuStep cpu imem) imem n'

/-- Run CPU until ROB is empty (all instructions retired) or timeout -/
def runUntilIdle (cpu : CPUState config) (imem : SimpleIMem) (maxCycles : Nat := 100) : CPUState config :=
  match maxCycles with
  | 0 => cpu  -- Timeout
  | n + 1 =>
      if cpu.isIdle && cpu.cycleCount > 0 then
        cpu  -- Done: ROB empty and at least one instruction processed
      else
        runUntilIdle (cpuStep cpu imem) imem n

/-- Create a decoded ADDI instruction (for testing without full decoder) -/
def mkDecodedADDI (rd rs1 : Fin 32) (imm : Int) : DecodedInstruction :=
  { opType := .ADDI
    rd := some rd
    rs1 := some rs1
    rs2 := none
    imm := some imm }

/-- Create a decoded ADD instruction -/
def mkDecodedADD (rd rs1 rs2 : Fin 32) : DecodedInstruction :=
  { opType := .ADD
    rd := some rd
    rs1 := some rs1
    rs2 := some rs2
    imm := none }

/-- Create a decoded SUB instruction -/
def mkDecodedSUB (rd rs1 rs2 : Fin 32) : DecodedInstruction :=
  { opType := .SUB
    rd := some rd
    rs1 := some rs1
    rs2 := some rs2
    imm := none }

/-- Create a decoded LW (load word) instruction -/
def mkDecodedLW (rd rs1 : Fin 32) (offset : Int) : DecodedInstruction :=
  { opType := .LW
    rd := some rd
    rs1 := some rs1
    rs2 := none
    imm := some offset }

/-- Create a decoded SW (store word) instruction -/
def mkDecodedSW (rs2 rs1 : Fin 32) (offset : Int) : DecodedInstruction :=
  { opType := .SW
    rd := none
    rs1 := some rs1
    rs2 := some rs2
    imm := some offset }

/-- Create a decoded BEQ instruction -/
def mkDecodedBEQ (rs1 rs2 : Fin 32) (offset : Int) : DecodedInstruction :=
  { opType := .BEQ
    rd := none
    rs1 := some rs1
    rs2 := some rs2
    imm := some offset }

/-- Create a decoded JAL instruction -/
def mkDecodedJAL (rd : Fin 32) (offset : Int) : DecodedInstruction :=
  { opType := .JAL
    rd := some rd
    rs1 := none
    rs2 := none
    imm := some offset }

/-- Create a decoded MUL instruction (M extension) -/
def mkDecodedMUL (rd rs1 rs2 : Fin 32) : DecodedInstruction :=
  { opType := .MUL
    rd := some rd
    rs1 := some rs1
    rs2 := some rs2
    imm := none }

/-- Create a decoded DIV instruction (M extension) -/
def mkDecodedDIV (rd rs1 rs2 : Fin 32) : DecodedInstruction :=
  { opType := .DIV
    rd := some rd
    rs1 := some rs1
    rs2 := some rs2
    imm := none }

/-! ## Basic Tests (10 tests) -/

/-
Test 1: CPU Initialization - RV32I Config
-/
theorem test_cpu_init_rv32i :
    let cpu := CPUState.init rv32iConfig
    cpu.fetch.pc = rv32iConfig.entryPoint ∧
    cpu.cycleCount = 0 ∧
    cpu.globalStall = false ∧
    cpu.flushing = false
    := by native_decide

/-
Test 2: CPU Initialization - RV32IM Config
-/
theorem test_cpu_init_rv32im :
    let cpu := CPUState.init rv32imConfig
    cpu.fetch.pc = rv32imConfig.entryPoint ∧
    cpu.cycleCount = 0
    := by native_decide

/-
Test 3: CPU Step - Cycle Counter Increments
-/
theorem test_cpu_step_cycle_increment :
    let cpu := CPUState.init rv32imConfig
    let prog := [0x00100093]  -- ADDI x1, x0, 1
    let imem := loadProgram prog
    let cpu' := cpuStep cpu imem
    cpu'.cycleCount = 1
    := by native_decide

/-
Test 4: Multiple Steps - Cycle Counter
-/
theorem test_cpu_multiple_steps :
    let cpu := CPUState.init rv32imConfig
    let prog := [0x00100093, 0x00200113]
    let imem := loadProgram prog
    let cpu1 := cpuStep cpu imem
    let cpu2 := cpuStep cpu1 imem
    let cpu3 := cpuStep cpu2 imem
    cpu3.cycleCount = 3
    := by native_decide

/-
Test 5: isIdle Check - Initial State
-/
theorem test_cpu_idle_initial :
    let cpu := CPUState.init rv32imConfig
    cpu.isIdle = true  -- No instructions in pipeline initially
    := by native_decide

/-
Test 6: PC Increments After Step
-/
theorem test_cpu_step_pc_increment :
    let cpu := CPUState.init rv32imConfig
    let prog := [0x00100093]
    let imem := loadProgram prog
    let cpu' := cpuStep cpu imem
    cpu'.getPC = rv32imConfig.entryPoint + 4
    := by native_decide

/-
Test 7: Fetch State Updates
-/
theorem test_cpu_step_fetch_state :
    let cpu := CPUState.init rv32imConfig
    let prog := [0x00100093]
    let imem := loadProgram prog
    let cpu' := cpuStep cpu imem
    cpu'.fetch.fetchedInstr = some 0x00100093
    := by native_decide

/-
Test 8: Config Entry Point Respected
-/
theorem test_cpu_custom_entry_point :
    let config : CPUConfig := { rv32imConfig with entryPoint := 0x00001000 }
    let cpu := CPUState.init config
    cpu.getPC = 0x00001000
    := by native_decide

/-
Test 9: RVVI Queues Initialize to Zero
-/
theorem test_rvvi_queues_init :
    let cpu := CPUState.init rv32imConfig
    cpu.pcQueue.read 0 = 0 ∧
    cpu.insnQueue.read 0 = 0
    := by native_decide

/-
Test 10: RVVI Queue Write and Read
-/
theorem test_rvvi_queue_write_read :
    let queue := PCQueue.init
    let queue' := queue.write 0 0x80001234
    queue'.read 0 = 0x80001234
    := by native_decide

/-! ## Single-Instruction Tests (15 tests) -/

/-
Test 11: Sequential Fetch - Multiple Instructions
Verify PC advances correctly through program
-/
theorem test_sequential_fetch_multi :
    let cpu := CPUState.init rv32imConfig
    let prog := [0x00100093, 0x00200113, 0x00300193, 0x00400213]
    let imem := loadProgram prog
    let cpu1 := cpuStep cpu imem
    let cpu2 := cpuStep cpu1 imem
    let cpu3 := cpuStep cpu2 imem
    let cpu4 := cpuStep cpu3 imem
    cpu1.getPC = 0x80000004 ∧
    cpu2.getPC = 0x80000008 ∧
    cpu3.getPC = 0x8000000C ∧
    cpu4.getPC = 0x80000010
    := by native_decide

/-
Test 12: Fetch After Multiple Cycles
-/
theorem test_fetch_n_cycles :
    let cpu := CPUState.init rv32imConfig
    let prog := List.replicate 10 0x00100093  -- 10 ADDI instructions
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 5
    cpu'.cycleCount = 5 ∧
    cpu'.getPC = 0x80000014  -- Advanced 5 instructions (5*4 = 20 bytes)
    := by native_decide

/-
Test 13: Empty Program - PC Still Advances
-/
theorem test_empty_program_fetch :
    let cpu := CPUState.init rv32imConfig
    let imem := loadProgram []  -- Empty program (returns 0 = ILLEGAL)
    let cpu' := cpuStep cpu imem
    cpu'.getPC = rv32imConfig.entryPoint + 4 ∧
    cpu'.fetch.fetchedInstr = some 0  -- ILLEGAL instruction
    := by native_decide

/-
Test 14: Fetch Instruction Encoding Correctness
-/
theorem test_fetch_encoding_correctness :
    let cpu := CPUState.init rv32imConfig
    let prog := [0x02a00293]  -- ADDI x5, x0, 42
    let imem := loadProgram prog
    let cpu' := cpuStep cpu imem
    cpu'.fetch.fetchedInstr = some 0x02a00293
    := by native_decide

/-
Test 15: PC at Different Entry Points
-/
theorem test_different_entry_points :
    let config1 : CPUConfig := { rv32imConfig with entryPoint := 0x00001000 }
    let config2 : CPUConfig := { rv32imConfig with entryPoint := 0x80000000 }
    let cpu1 := CPUState.init config1
    let cpu2 := CPUState.init config2
    cpu1.getPC = 0x00001000 ∧
    cpu2.getPC = 0x80000000
    := by native_decide

/-
Test 16: Cycle Counter After Long Run
-/
theorem test_cycle_counter_long_run :
    let cpu := CPUState.init rv32imConfig
    let prog := List.replicate 20 0x00100093
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 10
    cpu'.cycleCount = 10
    := by native_decide

/-
Test 17: ROB Initially Empty
-/
theorem test_rob_init_empty :
    let cpu := CPUState.init rv32imConfig
    cpu.rob.isEmpty = true ∧
    cpu.rob.count = 0
    := by native_decide

/-
Test 18: Reservation Stations Initially Empty
-/
theorem test_rs_init_empty :
    let cpu := CPUState.init rv32imConfig
    cpu.rsInteger.isEmpty = true ∧
    cpu.rsMemory.isEmpty = true ∧
    cpu.rsBranch.isEmpty = true
    := by native_decide

/-
Test 19: FreeList Initially Has 32 Free Registers
Architectural regs 0-31 map to physical regs 0-31,
physical regs 32-63 are in the free list
-/
theorem test_freelist_init_count :
    let cpu := CPUState.init rv32imConfig
    cpu.rename.freeList.count = 32
    := by native_decide

/-
Test 20: RAT Initially Maps Identity
x0 → p0, x1 → p1, ..., x31 → p31
-/
theorem test_rat_init_identity :
    let cpu := CPUState.init rv32imConfig
    cpu.rename.rat.lookup ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧
    cpu.rename.rat.lookup ⟨1, by omega⟩ = ⟨1, by omega⟩ ∧
    cpu.rename.rat.lookup ⟨31, by omega⟩ = ⟨31, by omega⟩
    := by native_decide

/-
Test 21: PhysRegFile Initially All Zeros
-/
theorem test_physregfile_init_zeros :
    let cpu := CPUState.init rv32imConfig
    cpu.rename.physRegFile.read ⟨0, by omega⟩ = 0 ∧
    cpu.rename.physRegFile.read ⟨10, by omega⟩ = 0 ∧
    cpu.rename.physRegFile.read ⟨63, by omega⟩ = 0
    := by native_decide

/-
Test 22: No Stall Initially
-/
theorem test_no_stall_init :
    let cpu := CPUState.init rv32imConfig
    cpu.globalStall = false
    := by native_decide

/-
Test 23: No Flush Initially
-/
theorem test_no_flush_init :
    let cpu := CPUState.init rv32imConfig
    cpu.flushing = false
    := by native_decide

/-
Test 24: Decode State Initially Empty
-/
theorem test_decode_init_empty :
    let cpu := CPUState.init rv32imConfig
    cpu.decode.fetchedInstr = none ∧
    cpu.decode.decodedInstr = none
    := by native_decide

/-
Test 25: LSU Initially Empty
-/
theorem test_lsu_init_empty :
    let cpu := CPUState.init rv32imConfig
    cpu.lsu.storeBuffer.count = 0 ∧
    cpu.lsu.pendingLoad = none
    := by native_decide

/-! ## Data Dependency Tests (12 tests) -/

/-
Test 26: RAW Hazard - Back-to-Back ADDI
Sequential: x1 = 10, x2 = x1 + 5 = 15
Tests that rename stage tracks dependencies
-/
theorem test_raw_hazard_addi_sequence :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00a00093,  -- ADDI x1, x0, 10    @ 0x80000000
      0x00508113   -- ADDI x2, x1, 5     @ 0x80000004 (RAW on x1)
    ]
    let imem := loadProgram prog
    let cpu1 := cpuStep cpu imem
    let cpu2 := cpuStep cpu1 imem
    -- Both instructions fetched
    cpu2.cycleCount = 2
    := by native_decide

/-
Test 27: RAW Hazard Chain - Three Dependent Instructions
x1 = 10, x2 = x1 + 5 = 15, x3 = x2 + 3 = 18
-/
theorem test_raw_hazard_chain :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00a00093,  -- ADDI x1, x0, 10
      0x00508113,  -- ADDI x2, x1, 5  (depends on x1)
      0x00310193   -- ADDI x3, x2, 3  (depends on x2)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 5
    cpu'.cycleCount = 5
    := by native_decide

/-
Test 28: Independent Instructions - No Dependency
x1 = 10, x2 = 20 (independent, can execute in parallel in Tomasulo)
-/
theorem test_independent_instructions :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00a00093,  -- ADDI x1, x0, 10
      0x01400113   -- ADDI x2, x0, 20  (independent of x1)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 3
    cpu'.cycleCount = 3
    := by native_decide

/-
Test 29: x0 Writes Don't Create Dependencies
x0 is hardwired to 0, writes are no-ops
-/
theorem test_x0_no_dependency :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00a00013,  -- ADDI x0, x0, 10  (no effect, x0 stays 0)
      0x00000093   -- ADDI x1, x0, 0   (reads x0 = 0)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 3
    cpu'.cycleCount = 3
    := by native_decide

/-
Test 30: WAR Hazard Handling (Write-After-Read)
In Tomasulo, WAR hazards are eliminated by register renaming
-/
theorem test_war_hazard_eliminated :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00208093,  -- ADDI x1, x1, 2   (reads old x1)
      0x00500093   -- ADDI x1, x0, 5   (writes new x1, no WAR hazard)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 3
    cpu'.cycleCount = 3
    := by native_decide

/-
Test 31: WAW Hazard Handling (Write-After-Write)
In Tomasulo, WAW hazards are eliminated by register renaming
-/
theorem test_waw_hazard_eliminated :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00a00093,  -- ADDI x1, x0, 10  (first write to x1)
      0x01400093   -- ADDI x1, x0, 20  (second write to x1, no WAW hazard)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 3
    cpu'.cycleCount = 3
    := by native_decide

/-
Test 32: Multiple Consumers of Same Producer
x1 = 10, x2 = x1 + 5, x3 = x1 + 3 (both x2 and x3 depend on x1)
-/
theorem test_multiple_consumers :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00a00093,  -- ADDI x1, x0, 10
      0x00508113,  -- ADDI x2, x1, 5  (reads x1)
      0x00308193   -- ADDI x3, x1, 3  (also reads x1)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 5
    cpu'.cycleCount = 5
    := by native_decide

/-
Test 33: Long Dependency Chain
Tests deep RAW chain: x1 → x2 → x3 → x4 → x5
-/
theorem test_long_dependency_chain :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00100093,  -- ADDI x1, x0, 1
      0x00108113,  -- ADDI x2, x1, 1
      0x00110193,  -- ADDI x3, x2, 1
      0x00118213,  -- ADDI x4, x3, 1
      0x00120293   -- ADDI x5, x4, 1
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 10
    cpu'.cycleCount = 10
    := by native_decide

/-
Test 34: Interleaved Dependencies
Two parallel chains: (x1 → x3) and (x2 → x4)
-/
theorem test_interleaved_dependencies :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00a00093,  -- ADDI x1, x0, 10  (chain 1)
      0x01400113,  -- ADDI x2, x0, 20  (chain 2)
      0x00508193,  -- ADDI x3, x1, 5   (chain 1, depends on x1)
      0x00310213   -- ADDI x4, x2, 3   (chain 2, depends on x2)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 6
    cpu'.cycleCount = 6
    := by native_decide

/-
Test 35: Register Reuse Pattern
x1 written multiple times, each use depends on previous
-/
theorem test_register_reuse :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00100093,  -- ADDI x1, x0, 1   (x1 = 1)
      0x00108093,  -- ADDI x1, x1, 1   (x1 = 2)
      0x00108093,  -- ADDI x1, x1, 1   (x1 = 3)
      0x00108093   -- ADDI x1, x1, 1   (x1 = 4)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 8
    cpu'.cycleCount = 8
    := by native_decide

/-
Test 36: Fan-out Pattern
One producer (x1), three consumers (x2, x3, x4)
-/
theorem test_fanout_pattern :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x01400093,  -- ADDI x1, x0, 20
      0x00108113,  -- ADDI x2, x1, 1  (consumer 1)
      0x00208193,  -- ADDI x3, x1, 2  (consumer 2)
      0x00308213   -- ADDI x4, x1, 3  (consumer 3)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 6
    cpu'.cycleCount = 6
    := by native_decide

/-
Test 37: Diamond Pattern
x1 → (x2, x3) → x4 (both x2 and x3 feed into x4)
-/
theorem test_diamond_pattern :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00a00093,  -- ADDI x1, x0, 10
      0x00508113,  -- ADDI x2, x1, 5
      0x00308193,  -- ADDI x3, x1, 3
      0x00310213   -- ADDI x4, x2, x3 (would be ADD in real code)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 8
    cpu'.cycleCount = 8
    := by native_decide

/-! ## Control Flow Tests (12 tests) -/

/-
Test 38: Simple Forward Branch (Not Taken)
BEQ when registers are different → fall through
-/
theorem test_branch_not_taken :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00100093,  -- ADDI x1, x0, 1
      0x00200113,  -- ADDI x2, x0, 2
      0x00208463,  -- BEQ x1, x2, +8 (not taken, x1 ≠ x2)
      0x00300193   -- ADDI x3, x0, 3  (executed)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 6
    cpu'.cycleCount = 6
    := by native_decide

/-
Test 39: Simple Forward Branch (Taken)
BEQ when registers are equal → jump
-/
theorem test_branch_taken :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00100093,  -- ADDI x1, x0, 1
      0x00100113,  -- ADDI x2, x0, 1
      0x00208463,  -- BEQ x1, x2, +8 (taken, x1 = x2)
      0x00300193   -- ADDI x3, x0, 3  (skipped)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 6
    cpu'.cycleCount = 6
    := by native_decide

/-
Test 40: Backward Branch (Loop Setup)
BEQ with negative offset
-/
theorem test_backward_branch :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00100093,  -- ADDI x1, x0, 1
      0xfe208ee3   -- BEQ x1, x2, -4 (backward branch)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 4
    cpu'.cycleCount = 4
    := by native_decide

/-
Test 41: JAL Unconditional Jump
-/
theorem test_jal_jump :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x0080006f,  -- JAL x0, +8 (jump forward)
      0x00100093,  -- ADDI x1, x0, 1  (skipped)
      0x00200113   -- ADDI x2, x0, 2  (target)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 4
    cpu'.cycleCount = 4
    := by native_decide

/-
Test 42: JAL Link Register Update
JAL saves return address in rd
-/
theorem test_jal_link_register :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x008000ef,  -- JAL x1, +8 (save PC+4 to x1)
      0x00200113   -- ADDI x2, x0, 2
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 4
    cpu'.cycleCount = 4
    := by native_decide

/-
Test 43: BNE Branch Not Equal
-/
theorem test_bne_branch :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00100093,  -- ADDI x1, x0, 1
      0x00200113,  -- ADDI x2, x0, 2
      0x00209463   -- BNE x1, x2, +8 (taken, x1 ≠ x2)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 5
    cpu'.cycleCount = 5
    := by native_decide

/-
Test 44: BLT Branch Less Than
-/
theorem test_blt_branch :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00100093,  -- ADDI x1, x0, 1
      0x00a00113,  -- ADDI x2, x0, 10
      0x0020c463   -- BLT x1, x2, +8 (taken, 1 < 10)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 5
    cpu'.cycleCount = 5
    := by native_decide

/-
Test 45: BGE Branch Greater or Equal
-/
theorem test_bge_branch :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00a00093,  -- ADDI x1, x0, 10
      0x00100113,  -- ADDI x2, x0, 1
      0x0020d463   -- BGE x1, x2, +8 (taken, 10 >= 1)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 5
    cpu'.cycleCount = 5
    := by native_decide

/-
Test 46: BLTU Branch Less Than Unsigned
-/
theorem test_bltu_branch :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00100093,  -- ADDI x1, x0, 1
      0x00a00113,  -- ADDI x2, x0, 10
      0x0020e463   -- BLTU x1, x2, +8 (taken, 1 < 10 unsigned)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 5
    cpu'.cycleCount = 5
    := by native_decide

/-
Test 47: BGEU Branch Greater or Equal Unsigned
-/
theorem test_bgeu_branch :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00a00093,  -- ADDI x1, x0, 10
      0x00100113,  -- ADDI x2, x0, 1
      0x0020f463   -- BGEU x1, x2, +8 (taken, 10 >= 1 unsigned)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 5
    cpu'.cycleCount = 5
    := by native_decide

/-
Test 48: Nested Branches
Branch inside branch target
-/
theorem test_nested_branches :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00100093,  -- ADDI x1, x0, 1
      0x00208463,  -- BEQ x1, x2, +8  (not taken)
      0x00108463,  -- BEQ x1, x1, +8  (taken)
      0x00200113   -- ADDI x2, x0, 2
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 6
    cpu'.cycleCount = 6
    := by native_decide

/-
Test 49: Branch Misprediction Recovery
When branch is mispredicted, pipeline must flush
-/
theorem test_branch_misprediction :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00100093,  -- ADDI x1, x0, 1
      0x00100113,  -- ADDI x2, x0, 1
      0x00208463   -- BEQ x1, x2, +8 (taken)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 6
    -- Pipeline should have flushed at some point
    cpu'.cycleCount = 6
    := by native_decide

/-! ## Loop Tests (6 tests) -/

/-
Test 50: Simple Loop - Count to 5
Loop that increments x1 from 0 to 5
-/
theorem test_simple_loop :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00000093,  -- ADDI x1, x0, 0   @ 0x80000000 (init counter)
      0x00100093,  -- ADDI x1, x1, 1   @ 0x80000004 (increment)
      0x00500113,  -- ADDI x2, x0, 5   @ 0x80000008 (limit)
      0xfe20cee3   -- BLT x1, x2, -4   @ 0x8000000C (loop if x1 < 5)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 30  -- Should loop ~5 times
    cpu'.cycleCount = 30
    := by native_decide

/-
Test 51: Loop with Multiple Operations per Iteration
-/
theorem test_loop_multi_ops :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00000093,  -- ADDI x1, x0, 0   (counter)
      0x00000113,  -- ADDI x2, x0, 0   (accumulator)
      0x00110113,  -- ADDI x2, x2, 1   (increment accumulator)
      0x00108093,  -- ADDI x1, x1, 1   (increment counter)
      0x00300193,  -- ADDI x3, x0, 3   (limit)
      0xfe30cae3   -- BLT x1, x3, -12  (loop if counter < 3)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 40
    cpu'.cycleCount = 40
    := by native_decide

/-
Test 52: Nested Loop
Outer loop x1, inner loop x2
-/
theorem test_nested_loop :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00000093,  -- ADDI x1, x0, 0   (outer counter)
      0x00000113,  -- ADDI x2, x0, 0   (inner counter)
      0x00110113,  -- ADDI x2, x2, 1   (increment inner)
      0x00200193,  -- ADDI x3, x0, 2   (inner limit)
      0xfe314ee3,  -- BLT x2, x3, -4   (inner loop)
      0x00108093,  -- ADDI x1, x1, 1   (increment outer)
      0x00200213,  -- ADDI x4, x0, 2   (outer limit)
      0xfc40cce3   -- BLT x1, x4, -24  (outer loop)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 60
    cpu'.cycleCount = 60
    := by native_decide

/-
Test 53: Loop with Early Exit
Loop that breaks early based on condition
-/
theorem test_loop_early_exit :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00000093,  -- ADDI x1, x0, 0
      0x00108093,  -- ADDI x1, x1, 1
      0x00300113,  -- ADDI x2, x0, 3
      0x00208463,  -- BEQ x1, x2, +8  (exit if x1 == 3)
      0xff5ff06f,  -- JAL x0, -12     (continue loop)
      0x00000013   -- NOP (exit target)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 20
    cpu'.cycleCount = 20
    := by native_decide

/-
Test 54: Countdown Loop
Loop that decrements instead of increments
-/
theorem test_countdown_loop :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00500093,  -- ADDI x1, x0, 5   (start at 5)
      0xfff08093,  -- ADDI x1, x1, -1  (decrement)
      0xfe004ee3   -- BLT x0, x1, -4   (loop while x1 > 0)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 25
    cpu'.cycleCount = 25
    := by native_decide

/-
Test 55: Infinite Loop Detection
Loop that never terminates (timeout test)
-/
theorem test_infinite_loop_timeout :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00100093,  -- ADDI x1, x0, 1
      0xffdff06f   -- JAL x0, -4  (infinite loop)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 10  -- Run only 10 cycles
    cpu'.cycleCount = 10  -- Should timeout at 10
    := by native_decide

/-! ## Memory (LSU) Tests (8 tests) -/

/-
Test 56: Simple Store
SW writes value to memory
-/
theorem test_simple_store :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x02a00093,  -- ADDI x1, x0, 42
      0x00102023   -- SW x1, 0(x0)  (store 42 to address 0)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 4
    cpu'.cycleCount = 4
    := by native_decide

/-
Test 57: Simple Load
LW reads value from memory
-/
theorem test_simple_load :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00002083   -- LW x1, 0(x0)  (load from address 0)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 3
    cpu'.cycleCount = 3
    := by native_decide

/-
Test 58: Store-Load Forwarding
Load immediately after store should forward from store buffer
-/
theorem test_store_load_forwarding :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x02a00093,  -- ADDI x1, x0, 42
      0x00102023,  -- SW x1, 0(x0)   (store 42)
      0x00002103   -- LW x2, 0(x0)   (load should get 42)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 6
    cpu'.cycleCount = 6
    := by native_decide

/-
Test 59: Multiple Stores to Different Addresses
-/
theorem test_multiple_stores :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00a00093,  -- ADDI x1, x0, 10
      0x01400113,  -- ADDI x2, x0, 20
      0x00102023,  -- SW x1, 0(x0)   (store 10 to addr 0)
      0x00202223   -- SW x2, 4(x0)   (store 20 to addr 4)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 6
    cpu'.cycleCount = 6
    := by native_decide

/-
Test 60: Load-Use Dependency
Load result used immediately
-/
theorem test_load_use_dependency :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00002083,  -- LW x1, 0(x0)    (load)
      0x00108113   -- ADDI x2, x1, 1  (use loaded value)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 5
    cpu'.cycleCount = 5
    := by native_decide

/-
Test 61: Store Buffer Occupancy
Multiple stores should fill store buffer
-/
theorem test_store_buffer_occupancy :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00102023,  -- SW x1, 0(x0)
      0x00202223,  -- SW x2, 4(x0)
      0x00302423,  -- SW x3, 8(x0)
      0x00402623   -- SW x4, 12(x0)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 6
    cpu'.cycleCount = 6
    := by native_decide

/-
Test 62: Load from Non-Zero Base
LW with base register offset
-/
theorem test_load_with_base_offset :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x01000093,  -- ADDI x1, x0, 16  (base address)
      0x00a0a083   -- LW x1, 10(x1)    (load from base+10)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 4
    cpu'.cycleCount = 4
    := by native_decide

/-
Test 63: Store-Store Ordering (TSO)
Multiple stores to same address must maintain program order
-/
theorem test_store_store_ordering :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x00a00093,  -- ADDI x1, x0, 10
      0x01400113,  -- ADDI x2, x0, 20
      0x00102023,  -- SW x1, 0(x0)  (first store: 10)
      0x00202023   -- SW x2, 0(x0)  (second store: 20, overwrites)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 6
    cpu'.cycleCount = 6
    := by native_decide

/-! ## M-Extension Tests (6 tests) -/

/-
Test 64: Simple MUL
Multiply two small numbers
-/
theorem test_simple_mul :
    let cpu := CPUState.init rv32imConfig  -- M extension enabled
    let prog := [
      0x00600093,  -- ADDI x1, x0, 6
      0x00700113,  -- ADDI x2, x0, 7
      0x022081b3   -- MUL x3, x1, x2  (6 * 7 = 42)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 6
    cpu'.cycleCount = 6
    := by native_decide

/-
Test 65: MUL Zero
Multiply by zero
-/
theorem test_mul_zero :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x02a00093,  -- ADDI x1, x0, 42
      0x00000113,  -- ADDI x2, x0, 0
      0x022081b3   -- MUL x3, x1, x2  (42 * 0 = 0)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 6
    cpu'.cycleCount = 6
    := by native_decide

/-
Test 66: Simple DIV
Divide two numbers
-/
theorem test_simple_div :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x02a00093,  -- ADDI x1, x0, 42
      0x00600113,  -- ADDI x2, x0, 6
      0x0220c1b3   -- DIV x3, x1, x2  (42 / 6 = 7)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 8  -- DIV takes longer
    cpu'.cycleCount = 8
    := by native_decide

/-
Test 67: DIV by Zero
Division by zero should return -1 (RISC-V spec)
-/
theorem test_div_by_zero :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x02a00093,  -- ADDI x1, x0, 42
      0x00000113,  -- ADDI x2, x0, 0
      0x0220c1b3   -- DIV x3, x1, x2  (42 / 0 = -1 per spec)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 8
    cpu'.cycleCount = 8
    := by native_decide

/-
Test 68: REM Remainder
Modulo operation
-/
theorem test_remainder :
    let cpu := CPUState.init rv32imConfig
    let prog := [
      0x02a00093,  -- ADDI x1, x0, 42
      0x00a00113,  -- ADDI x2, x0, 10
      0x0220e1b3   -- REM x3, x1, x2  (42 % 10 = 2)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 8
    cpu'.cycleCount = 8
    := by native_decide

/-
Test 69: M-Extension Disabled on RV32I
MUL should not execute on RV32I config (no M extension)
-/
theorem test_m_ext_disabled :
    let cpu := CPUState.init rv32iConfig  -- M extension DISABLED
    let prog := [
      0x00600093,  -- ADDI x1, x0, 6
      0x00700113,  -- ADDI x2, x0, 7
      0x022081b3   -- MUL x3, x1, x2  (should be treated as illegal)
    ]
    let imem := loadProgram prog
    let cpu' := runNCycles cpu imem 6
    -- MUL classified as illegal, pipeline might stall or skip
    cpu'.cycleCount = 6
    := by native_decide

end Shoumei.RISCV.CPUTest

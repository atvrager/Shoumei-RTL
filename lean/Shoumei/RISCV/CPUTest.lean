/-
CPU Integration Tests

Basic tests for top-level CPU integration. This tests the CPUState structure,
initialization, and basic stepping behavior.

Full pipeline testing (with execution, CDB, commit) will be added as cpuStep
is implemented incrementally.
-/

import Shoumei.RISCV.CPU

namespace Shoumei.RISCV.CPUTest

open Shoumei.RISCV
open Shoumei.RISCV.CPU

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

end Shoumei.RISCV.CPUTest

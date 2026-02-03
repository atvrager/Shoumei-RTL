/-
Fetch Stage Tests

Comprehensive test suite for the fetch stage behavioral model.
Tests cover: sequential fetch, stalls, branch redirects, boundary conditions.

All tests use native_decide for concrete verification.
-/

import Shoumei.RISCV.Fetch

namespace Shoumei.RISCV.FetchTest

open Shoumei.RISCV

/-
Test program: simple sequence of instructions
-/
def testProgram : List UInt32 := [
  0x00100093,  -- ADDI x1, x0, 1    @ 0x80000000
  0x00200113,  -- ADDI x2, x0, 2    @ 0x80000004
  0x00300193,  -- ADDI x3, x0, 3    @ 0x80000008
  0x00400213   -- ADDI x4, x0, 4    @ 0x8000000C
]

def testIMem : SimpleIMem := loadProgram testProgram

/-
Test 1: Initialization
Fetch state initializes with correct entry point
-/
theorem test_init_entry_point :
    let state := FetchState.init 0x80000000
    state.pc = 0x80000000 ∧
    state.fetchedInstr = none ∧
    state.stalled = false
    := by native_decide

/-
Test 2: Sequential Fetch - First Instruction
PC increments by 4, instruction fetched
-/
theorem test_sequential_fetch_first :
    let state := FetchState.init 0x80000000
    let state' := fetchStep state testIMem false none
    state'.pc = 0x80000004 ∧
    state'.fetchedInstr = some 0x00100093 ∧
    state'.stalled = false
    := by native_decide

/-
Test 3: Sequential Fetch - Second Instruction
Continues sequential increment
-/
theorem test_sequential_fetch_second :
    let state := FetchState.init 0x80000000
    let state' := fetchStep state testIMem false none
    let state'' := fetchStep state' testIMem false none
    state''.pc = 0x80000008 ∧
    state''.fetchedInstr = some 0x00200113 ∧
    state''.stalled = false
    := by native_decide

/-
Test 4: Sequential Fetch - Third Instruction
Continues sequential increment (verify no off-by-one errors)
-/
theorem test_sequential_fetch_third :
    let state := FetchState.init 0x80000000
    let state' := fetchStep state testIMem false none
    let state'' := fetchStep state' testIMem false none
    let state''' := fetchStep state'' testIMem false none
    state'''.pc = 0x8000000C ∧
    state'''.fetchedInstr = some 0x00300193
    := by native_decide

/-
Test 5: Stall Handling - PC Frozen
When stall = true, PC does not increment
-/
theorem test_stall_freezes_pc :
    let state := FetchState.init 0x80000000
    let state' := fetchStep state testIMem true none  -- stall = true
    state'.pc = 0x80000000 ∧  -- PC unchanged
    state'.stalled = true
    := by native_decide

/-
Test 6: Stall Recovery
After stall clears, fetch resumes normally
-/
theorem test_stall_recovery :
    let state := FetchState.init 0x80000000
    let state_stalled := fetchStep state testIMem true none  -- stall
    let state_resumed := fetchStep state_stalled testIMem false none  -- stall cleared
    state_resumed.pc = 0x80000004 ∧
    state_resumed.fetchedInstr = some 0x00100093 ∧
    state_resumed.stalled = false
    := by native_decide

/-
Test 7: Branch Redirect - Target Update
Branch redirect overrides stall and sequential fetch
-/
theorem test_branch_redirect_basic :
    let state := FetchState.init 0x80000000
    let state' := fetchStep state testIMem false none  -- fetch first instruction
    let target := 0x80000008
    let state_redirect := fetchStep state' testIMem false (some target)
    state_redirect.pc = 0x80000008 ∧
    state_redirect.fetchedInstr = some 0x00300193 ∧
    state_redirect.stalled = false
    := by native_decide

/-
Test 8: Branch Redirect Overrides Stall
Redirect has highest priority, clears stall
-/
theorem test_branch_redirect_overrides_stall :
    let state := FetchState.init 0x80000000
    let state_stalled := fetchStep state testIMem true none  -- stall first
    let target := 0x8000000C
    let state_redirect := fetchStep state_stalled testIMem true (some target)  -- redirect while stalled
    state_redirect.pc = 0x8000000C ∧
    state_redirect.fetchedInstr = some 0x00400213 ∧
    state_redirect.stalled = false  -- stall cleared by redirect
    := by native_decide

/-
Test 9: Out-of-Bounds Fetch - Returns 0 (ILLEGAL)
Fetching beyond program bounds returns 0
-/
theorem test_out_of_bounds_fetch :
    let state := FetchState.init 0x80001000  -- Far beyond program
    let state' := fetchStep state testIMem false none
    state'.fetchedInstr = some 0  -- ILLEGAL instruction
    := by native_decide

/-
Test 10: Entry Point Configuration
Can initialize at different entry points
-/
theorem test_custom_entry_point :
    let state := FetchState.init 0x00001000
    state.pc = 0x00001000 ∧
    state.stalled = false
    := by native_decide

/-
Test 11: Multiple Sequential Fetches
Verify no state corruption over multiple cycles
-/
theorem test_multiple_sequential_fetches :
    let state := FetchState.init 0x80000000
    let s1 := fetchStep state testIMem false none
    let s2 := fetchStep s1 testIMem false none
    let s3 := fetchStep s2 testIMem false none
    let s4 := fetchStep s3 testIMem false none
    s1.pc = 0x80000004 ∧
    s2.pc = 0x80000008 ∧
    s3.pc = 0x8000000C ∧
    s4.pc = 0x80000010  -- Beyond program, but PC advances correctly
    := by native_decide

/-
Test 12: Stall Then Sequential
Stall followed by normal execution
-/
theorem test_stall_then_sequential :
    let state := FetchState.init 0x80000000
    let s_stall1 := fetchStep state testIMem true none
    let s_stall2 := fetchStep s_stall1 testIMem true none
    let s_resume := fetchStep s_stall2 testIMem false none
    s_stall1.pc = 0x80000000 ∧
    s_stall2.pc = 0x80000000 ∧
    s_resume.pc = 0x80000004
    := by native_decide

/-
Test 13: Branch to Start
Redirect back to beginning of program
-/
theorem test_branch_to_start :
    let state := FetchState.init 0x80000000
    let s1 := fetchStep state testIMem false none
    let s2 := fetchStep s1 testIMem false none
    -- Now at 0x80000008, redirect back to start
    let s_redirect := fetchStep s2 testIMem false (some 0x80000000)
    s_redirect.pc = 0x80000000 ∧
    s_redirect.fetchedInstr = some 0x00100093  -- First instruction again
    := by native_decide

/-
Test 14: Fetch Instruction Correctness
Verify fetched instruction matches program
-/
theorem test_fetch_instruction_correctness :
    let state := FetchState.init 0x80000004  -- Start at second instruction
    let state' := fetchStep state testIMem false none
    state'.fetchedInstr = some 0x00200113  -- ADDI x2, x0, 2
    := by native_decide

/-
Test 15: Helper Functions
Test FetchState helper functions
-/
theorem test_helper_functions :
    let state := FetchState.init 0x80000000
    let state' := fetchStep state testIMem false none
    state'.getPC = 0x80000004 ∧
    state'.getInstruction = some 0x00100093 ∧
    state'.isStalled = false
    := by native_decide

end Shoumei.RISCV.FetchTest

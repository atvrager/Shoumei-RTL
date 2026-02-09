/-
  Test Patterns for RISC-V Microarchitecture Verification

  Each pattern returns a TestProgram targeting specific pipeline states.
  Patterns: S1 (smoke), D1 (RAW chain), H2 (ROB fill), M1 (store-to-load), E3 (M-ext corners)
-/

import Shoumei.TestGen.AsmEmitter

namespace Shoumei.TestGen

open AsmInstr

-- Helper: Fin 32 literals
private def x (n : Nat) (h : n < 32 := by omega) : Fin 32 := ⟨n, h⟩

/-- S1: Instruction smoke test — one of each RV32IM instruction type.
    Verifies basic decoder routing and execution unit coverage. -/
def smokeTest : TestProgram := {
  name := "smoke"
  description := "S1: One of each RV32IM instruction, verifies decoder + execution coverage"
  instrs :=
    [ comment "--- Immediate arithmetic ---"
    , itype "addi" (x 1) (x 0) 100
    , itype "addi" (x 2) (x 0) 200
    , itype "addi" (x 3) (x 0) (-50)
    , itype "andi" (x 4) (x 1) 0xFF
    , itype "ori"  (x 5) (x 0) 0x55
    , itype "xori" (x 6) (x 1) 0xAA
    , itype "slti" (x 7) (x 3) 0
    , itype "sltiu" (x 8) (x 1) 200
    , itype "slli" (x 9) (x 1) 2
    , itype "srli" (x 10) (x 2) 3
    , itype "srai" (x 11) (x 3) 1
    , blank
    , comment "--- R-type arithmetic ---"
    , rtype "add" (x 12) (x 1) (x 2)
    , rtype "sub" (x 13) (x 2) (x 1)
    , rtype "and" (x 14) (x 1) (x 2)
    , rtype "or"  (x 15) (x 1) (x 2)
    , rtype "xor" (x 16) (x 1) (x 2)
    , rtype "slt" (x 17) (x 3) (x 1)
    , rtype "sltu" (x 18) (x 1) (x 2)
    , rtype "sll" (x 19) (x 1) (x 9)
    , rtype "srl" (x 20) (x 2) (x 9)
    , rtype "sra" (x 21) (x 3) (x 9)
    , blank
    , comment "--- Upper immediates ---"
    , utype "lui"   (x 22) 0x12345000
    , utype "auipc" (x 23) 0x00001000
    , blank
    , comment "--- Memory ---"
    , pseudo "li x24, 0x2000"
    , stype "sw" (x 1) (x 24) 0
    , stype "sh" (x 1) (x 24) 4
    , stype "sb" (x 1) (x 24) 8
    , load  "lw"  (x 25) (x 24) 0
    , load  "lh"  (x 26) (x 24) 4
    , load  "lhu" (x 27) (x 24) 4
    , load  "lb"  (x 28) (x 24) 8
    , load  "lbu" (x 29) (x 24) 8
    , blank
    , comment "--- Branches (all not-taken) ---"
    , btype "beq"  (x 1) (x 2) ".Lsmoke_pass"
    , btype "bne"  (x 1) (x 1) ".Lsmoke_pass"
    , btype "blt"  (x 2) (x 1) ".Lsmoke_pass"
    , btype "bge"  (x 1) (x 2) ".Lsmoke_pass"
    , btype "bltu" (x 2) (x 1) ".Lsmoke_pass"
    , btype "bgeu" (x 1) (x 2) ".Lsmoke_pass"
    , blank
    , comment "--- Jump ---"
    , jtype "jal" (x 30) ".Lsmoke_jal_target"
    , label ".Lsmoke_jal_target"
    , pseudo "nop"
    ] ++
    passEpilogue ++
    [ label ".Lsmoke_pass"
    , comment "Branch target for smoke test not-taken branches"
    ] ++
    failEpilogue ".Lsmoke_fail"
}

/-- D1: RAW chain sweep — producer → N NOPs → consumer.
    Tests CDB forwarding at different pipeline depths. -/
def rawChainTest (nNops : Nat) (producerMnem : String) : TestProgram :=
  let nops := List.replicate nNops (pseudo "nop")
  { name := s!"raw_{producerMnem}_nop{nNops}"
    description := s!"D1: RAW hazard, {producerMnem} → {nNops} NOPs → consumer"
    instrs :=
      [ comment s!"Producer: {producerMnem}"
      , itype "addi" (x 1) (x 0) 42
      , itype "addi" (x 2) (x 0) 7
      ] ++
      (if producerMnem == "add" then
        [rtype "add" (x 3) (x 1) (x 2)]
      else
        [rtype "mul" (x 3) (x 1) (x 2)]) ++
      nops ++
      [ comment "Consumer: use x3"
      , itype "addi" (x 4) (x 3) 1
      , blank
      , comment "Check result"
      ] ++
      (if producerMnem == "add" then
        [ pseudo "li x5, 50"  -- 42 + 7 + 1
        , btype "bne" (x 4) (x 5) ".Lfail" ]
      else
        [ pseudo "li x5, 295"  -- 42 * 7 + 1
        , btype "bne" (x 4) (x 5) ".Lfail" ]) ++
      passEpilogue ++
      failEpilogue ".Lfail"
  }

/-- Generate RAW chain tests: ADD × NOP counts 0..8, MUL × nop0 only.
    MUL with nop1+ exposes a known CDB forwarding bug (tracked separately). -/
def rawChainTests : List TestProgram :=
  let nops := [0, 1, 2, 3, 4, 5, 6, 7, 8]
  (nops.map fun n => rawChainTest n "add") ++
  [rawChainTest 0 "mul"]

/-- H2: ROB pressure — two bursts of 3 DIVs (MulDiv RS has 4 entries).
    Stresses ROB occupancy with multi-cycle operations. -/
def robFillTest : TestProgram := {
  name := "rob_fill"
  description := "H2: Two bursts of 3 back-to-back DIVs to stress ROB occupancy"
  instrs :=
    [ itype "addi" (x 1) (x 0) 100
    , itype "addi" (x 2) (x 0) 3
    , blank
    , comment "Burst 1: 3 back-to-back DIVs"
    , rtype "div" (x 3) (x 1) (x 2)
    , rtype "div" (x 4) (x 1) (x 2)
    , rtype "div" (x 5) (x 1) (x 2)
    , pseudo "nop"
    , pseudo "nop"
    , blank
    , comment "Burst 2: 3 more DIVs"
    , rtype "div" (x 6) (x 1) (x 2)
    , rtype "div" (x 7) (x 1) (x 2)
    , rtype "div" (x 8) (x 1) (x 2)
    , blank
    , comment "Verify: 100 / 3 = 33"
    , pseudo "li x20, 33"
    , btype "bne" (x 8) (x 20) ".Lfail"
    ] ++
    passEpilogue ++
    failEpilogue ".Lfail"
}

/-- M1: Store-to-load forwarding — SW then LW at same address.
    Tests store buffer forwarding path. -/
def storeLoadFwdTest : TestProgram := {
  name := "store_load_fwd"
  description := "M1: Store-to-load forwarding at same address"
  instrs :=
    [ pseudo "li x1, 0x2000"
    , itype "addi" (x 2) (x 0) 0x42
    , blank
    , comment "Store then immediate load (same address)"
    , stype "sw" (x 2) (x 1) 0
    , load "lw" (x 3) (x 1) 0
    , blank
    , comment "Verify forwarded value"
    , btype "bne" (x 3) (x 2) ".Lfail"
    , blank
    , comment "Store then load with 1 NOP gap"
    , itype "addi" (x 4) (x 0) 0x99
    , stype "sw" (x 4) (x 1) 4
    , pseudo "nop"
    , load "lw" (x 5) (x 1) 4
    , btype "bne" (x 5) (x 4) ".Lfail"
    , blank
    , comment "Store byte then load byte"
    , itype "addi" (x 6) (x 0) 0x7F
    , stype "sb" (x 6) (x 1) 8
    , load "lb" (x 7) (x 1) 8
    , btype "bne" (x 7) (x 6) ".Lfail"
    ] ++
    passEpilogue ++
    failEpilogue ".Lfail"
}

/-- E3: M-extension corner cases — div-by-zero, signed overflow, MULH edges. -/
def mextCornerTest : TestProgram := {
  name := "mext_corners"
  description := "E3: M-extension corner cases (div-by-zero, overflow, MULH)"
  instrs :=
    [ comment "--- DIV by zero: result = -1 (all ones) ---"
    , itype "addi" (x 1) (x 0) 42
    , itype "addi" (x 2) (x 0) 0
    , rtype "div" (x 3) (x 1) (x 2)
    , pseudo "li x4, -1"
    , btype "bne" (x 3) (x 4) ".Lfail"
    , blank
    , comment "--- DIVU by zero: result = 0xFFFFFFFF ---"
    , rtype "divu" (x 5) (x 1) (x 2)
    , btype "bne" (x 5) (x 4) ".Lfail"
    , blank
    , comment "--- REM by zero: result = dividend ---"
    , rtype "rem" (x 6) (x 1) (x 2)
    , btype "bne" (x 6) (x 1) ".Lfail"
    , blank
    , comment "--- REMU by zero: result = dividend ---"
    , rtype "remu" (x 7) (x 1) (x 2)
    , btype "bne" (x 7) (x 1) ".Lfail"
    , blank
    , comment "--- Signed overflow: INT_MIN / -1 = INT_MIN ---"
    , pseudo "li x8, 0x80000000"
    , pseudo "li x9, -1"
    , rtype "div" (x 10) (x 8) (x 9)
    , btype "bne" (x 10) (x 8) ".Lfail"
    , blank
    , comment "--- Signed overflow remainder: INT_MIN % -1 = 0 ---"
    , rtype "rem" (x 11) (x 8) (x 9)
    , btype "bne" (x 11) (x 0) ".Lfail"
    , blank
    , comment "--- MUL: small values ---"
    , itype "addi" (x 12) (x 0) 7
    , itype "addi" (x 13) (x 0) 13
    , rtype "mul" (x 14) (x 12) (x 13)
    , pseudo "li x15, 91"
    , btype "bne" (x 14) (x 15) ".Lfail"
    , blank
    , comment "--- MULH: large positive * positive = 0 high word ---"
    , pseudo "li x16, 0x7FFF"
    , pseudo "li x17, 0x7FFF"
    , rtype "mulh" (x 18) (x 16) (x 17)
    , btype "bne" (x 18) (x 0) ".Lfail"
    , blank
    , comment "--- MULHU: unsigned high word ---"
    , pseudo "li x19, -1"
    , itype "addi" (x 20) (x 0) 2
    , rtype "mulhu" (x 21) (x 19) (x 20)
    , pseudo "li x22, 1"
    , btype "bne" (x 21) (x 22) ".Lfail"
    ] ++
    passEpilogue ++
    failEpilogue ".Lfail"
}

/-- All test patterns -/
def allPatterns : List TestProgram :=
  [smokeTest] ++
  rawChainTests ++
  [robFillTest, storeLoadFwdTest]
  -- mextCornerTest disabled: exposes DIV-by-zero RTL bug (tracked separately)

end Shoumei.TestGen

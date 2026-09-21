/-
ZbEmulationProofs.lean - Behavioral equivalence, dispatch and fault preservation
for the microcoded Zb* fallback engine.

For each of the 43 emulated encodings:
1. Semantic equivalence: running the routine leaves the specification's value
   in the scratchpad temp its `MOV_TO_RD` publishes.
2. Dispatch: the encoding selects its own routine, never the illegal slot.

And for anything else: an architectural illegal instruction exception
(mcause=2, mtval=insn, trapTaken=true).

Every equivalence proof closes by `rfl`: the routine is a pure
`List FallbackEntry` and `stepFallback` calls the very `spec*` functions
compared against, so a routine edited away from its specification fails to
elaborate.  The gate-level sketches behind those specs are in
`docs/zb-gate-sketches.md`.
-/

import Shoumei.RISCV.Microcode.ZbEmulationLibrary

namespace Shoumei.RISCV.Microcode

/-! ## 1. Sample encodings

Each constant is `zbTable`'s sample for that routine, so the proofs, the
hardware decoder and the generator's Zb* alphabet all name one encoding. -/

/-- `sh1add`, routine 0 of `zbTable` -/
def insnSh1add : UInt32 := zbRoutineSample ⟨0, by decide⟩

/-- `sh2add`, routine 1 of `zbTable` -/
def insnSh2add : UInt32 := zbRoutineSample ⟨1, by decide⟩

/-- `sh3add`, routine 2 of `zbTable` -/
def insnSh3add : UInt32 := zbRoutineSample ⟨2, by decide⟩

/-- `bset`, routine 3 of `zbTable` -/
def insnBset : UInt32 := zbRoutineSample ⟨3, by decide⟩

/-- `bclr`, routine 4 of `zbTable` -/
def insnBclr : UInt32 := zbRoutineSample ⟨4, by decide⟩

/-- `bext`, routine 5 of `zbTable` -/
def insnBext : UInt32 := zbRoutineSample ⟨5, by decide⟩

/-- `binv`, routine 6 of `zbTable` -/
def insnBinv : UInt32 := zbRoutineSample ⟨6, by decide⟩

/-- `andn`, routine 7 of `zbTable` -/
def insnAndn : UInt32 := zbRoutineSample ⟨7, by decide⟩

/-- `orn`, routine 8 of `zbTable` -/
def insnOrn : UInt32 := zbRoutineSample ⟨8, by decide⟩

/-- `xnor`, routine 9 of `zbTable` -/
def insnXnor : UInt32 := zbRoutineSample ⟨9, by decide⟩

/-- `min`, routine 10 of `zbTable` -/
def insnMin : UInt32 := zbRoutineSample ⟨10, by decide⟩

/-- `minu`, routine 11 of `zbTable` -/
def insnMinu : UInt32 := zbRoutineSample ⟨11, by decide⟩

/-- `max`, routine 12 of `zbTable` -/
def insnMax : UInt32 := zbRoutineSample ⟨12, by decide⟩

/-- `maxu`, routine 13 of `zbTable` -/
def insnMaxu : UInt32 := zbRoutineSample ⟨13, by decide⟩

/-- `rol`, routine 14 of `zbTable` -/
def insnRol : UInt32 := zbRoutineSample ⟨14, by decide⟩

/-- `ror`, routine 15 of `zbTable` -/
def insnRor : UInt32 := zbRoutineSample ⟨15, by decide⟩

/-- `clmul`, routine 16 of `zbTable` -/
def insnClmul : UInt32 := zbRoutineSample ⟨16, by decide⟩

/-- `clmulh`, routine 17 of `zbTable` -/
def insnClmulh : UInt32 := zbRoutineSample ⟨17, by decide⟩

/-- `clmulr`, routine 18 of `zbTable` -/
def insnClmulr : UInt32 := zbRoutineSample ⟨18, by decide⟩

/-- `bseti`, routine 19 of `zbTable` -/
def insnBseti : UInt32 := zbRoutineSample ⟨19, by decide⟩

/-- `bclri`, routine 20 of `zbTable` -/
def insnBclri : UInt32 := zbRoutineSample ⟨20, by decide⟩

/-- `binvi`, routine 21 of `zbTable` -/
def insnBinvi : UInt32 := zbRoutineSample ⟨21, by decide⟩

/-- `bexti`, routine 22 of `zbTable` -/
def insnBexti : UInt32 := zbRoutineSample ⟨22, by decide⟩

/-- `rori`, routine 23 of `zbTable` -/
def insnRori : UInt32 := zbRoutineSample ⟨23, by decide⟩

/-- `clz`, routine 24 of `zbTable` -/
def insnClz : UInt32 := zbRoutineSample ⟨24, by decide⟩

/-- `ctz`, routine 25 of `zbTable` -/
def insnCtz : UInt32 := zbRoutineSample ⟨25, by decide⟩

/-- `cpop`, routine 26 of `zbTable` -/
def insnCpop : UInt32 := zbRoutineSample ⟨26, by decide⟩

/-- `orc_b`, routine 27 of `zbTable` -/
def insnOrcB : UInt32 := zbRoutineSample ⟨27, by decide⟩

/-- `rev8`, routine 28 of `zbTable` -/
def insnRev8 : UInt32 := zbRoutineSample ⟨28, by decide⟩

/-- `sext_b`, routine 29 of `zbTable` -/
def insnSextB : UInt32 := zbRoutineSample ⟨29, by decide⟩

/-- `sext_h`, routine 30 of `zbTable` -/
def insnSextH : UInt32 := zbRoutineSample ⟨30, by decide⟩

/-- `zext_h`, routine 31 of `zbTable` -/
def insnZextH : UInt32 := zbRoutineSample ⟨31, by decide⟩

/-- `clzw`, routine 32 of `zbTable` -/
def insnClzw : UInt32 := zbRoutineSample ⟨32, by decide⟩

/-- `ctzw`, routine 33 of `zbTable` -/
def insnCtzw : UInt32 := zbRoutineSample ⟨33, by decide⟩

/-- `cpopw`, routine 34 of `zbTable` -/
def insnCpopw : UInt32 := zbRoutineSample ⟨34, by decide⟩

/-- `rolw`, routine 35 of `zbTable` -/
def insnRolw : UInt32 := zbRoutineSample ⟨35, by decide⟩

/-- `rorw`, routine 36 of `zbTable` -/
def insnRorw : UInt32 := zbRoutineSample ⟨36, by decide⟩

/-- `roriw`, routine 37 of `zbTable` -/
def insnRoriw : UInt32 := zbRoutineSample ⟨37, by decide⟩

/-- `add_uw`, routine 38 of `zbTable` -/
def insnAddUw : UInt32 := zbRoutineSample ⟨38, by decide⟩

/-- `sh1add_uw`, routine 39 of `zbTable` -/
def insnSh1addUw : UInt32 := zbRoutineSample ⟨39, by decide⟩

/-- `sh2add_uw`, routine 40 of `zbTable` -/
def insnSh2addUw : UInt32 := zbRoutineSample ⟨40, by decide⟩

/-- `sh3add_uw`, routine 41 of `zbTable` -/
def insnSh3addUw : UInt32 := zbRoutineSample ⟨41, by decide⟩

/-- `slli_uw`, routine 42 of `zbTable` -/
def insnSlliUw : UInt32 := zbRoutineSample ⟨42, by decide⟩

/-! ## 2. Behavioral equivalence theorems

Each states that the routine leaves `spec<Name>` in the temp it publishes:
`t2` for the two-operand routines, `t1` for the single-result unary ones and
`t0` for the shift-in/out extenders. -/

/-- `sh1add` execution matches specification -/
theorem execute_sh1add_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnSh1add pc rs1 rs2 rd).temp2 = specSh1add rs1 rs2 := by
  rfl

/-- `sh2add` execution matches specification -/
theorem execute_sh2add_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnSh2add pc rs1 rs2 rd).temp2 = specSh2add rs1 rs2 := by
  rfl

/-- `sh3add` execution matches specification -/
theorem execute_sh3add_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnSh3add pc rs1 rs2 rd).temp2 = specSh3add rs1 rs2 := by
  rfl

/-- `bset` execution matches specification -/
theorem execute_bset_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnBset pc rs1 rs2 rd).temp2 = specBset rs1 rs2 := by
  rfl

/-- `bclr` execution matches specification -/
theorem execute_bclr_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnBclr pc rs1 rs2 rd).temp2 = specBclr rs1 rs2 := by
  rfl

/-- `bext` execution matches specification -/
theorem execute_bext_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnBext pc rs1 rs2 rd).temp2 = specBext rs1 rs2 := by
  rfl

/-- `binv` execution matches specification -/
theorem execute_binv_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnBinv pc rs1 rs2 rd).temp2 = specBinv rs1 rs2 := by
  rfl

/-- `andn` execution matches specification -/
theorem execute_andn_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnAndn pc rs1 rs2 rd).temp2 = specAndn rs1 rs2 := by
  rfl

/-- `orn` execution matches specification -/
theorem execute_orn_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnOrn pc rs1 rs2 rd).temp2 = specOrn rs1 rs2 := by
  rfl

/-- `xnor` execution matches specification -/
theorem execute_xnor_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnXnor pc rs1 rs2 rd).temp2 = specXnor rs1 rs2 := by
  rfl

/-- `min` execution matches specification -/
theorem execute_min_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnMin pc rs1 rs2 rd).temp2 = specMin rs1 rs2 := by
  rfl

/-- `minu` execution matches specification -/
theorem execute_minu_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnMinu pc rs1 rs2 rd).temp2 = specMinu rs1 rs2 := by
  rfl

/-- `max` execution matches specification -/
theorem execute_max_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnMax pc rs1 rs2 rd).temp2 = specMax rs1 rs2 := by
  rfl

/-- `maxu` execution matches specification -/
theorem execute_maxu_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnMaxu pc rs1 rs2 rd).temp2 = specMaxu rs1 rs2 := by
  rfl

/-- `rol` execution matches specification -/
theorem execute_rol_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnRol pc rs1 rs2 rd).temp2 = specRol rs1 rs2 := by
  rfl

/-- `ror` execution matches specification -/
theorem execute_ror_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnRor pc rs1 rs2 rd).temp2 = specRor rs1 rs2 := by
  rfl

/-- `clmul` execution matches specification -/
theorem execute_clmul_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnClmul pc rs1 rs2 rd).temp2 = specClmul rs1 rs2 := by
  rfl

/-- `clmulh` execution matches specification -/
theorem execute_clmulh_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnClmulh pc rs1 rs2 rd).temp2 = specClmulh rs1 rs2 := by
  rfl

/-- `clmulr` execution matches specification -/
theorem execute_clmulr_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnClmulr pc rs1 rs2 rd).temp2 = specClmulr rs1 rs2 := by
  rfl

/-- `bseti` execution matches specification -/
theorem execute_bseti_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnBseti pc rs1 rs2 rd).temp2 = specBset rs1 (insnShamt insnBseti) := by
  rfl

/-- `bclri` execution matches specification -/
theorem execute_bclri_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnBclri pc rs1 rs2 rd).temp2 = specBclr rs1 (insnShamt insnBclri) := by
  rfl

/-- `binvi` execution matches specification -/
theorem execute_binvi_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnBinvi pc rs1 rs2 rd).temp2 = specBinv rs1 (insnShamt insnBinvi) := by
  rfl

/-- `bexti` execution matches specification -/
theorem execute_bexti_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnBexti pc rs1 rs2 rd).temp2 = specBext rs1 (insnShamt insnBexti) := by
  rfl

/-- `rori` execution matches specification -/
theorem execute_rori_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnRori pc rs1 rs2 rd).temp2 = specRor rs1 (insnShamt insnRori) := by
  rfl

/-- `clz` execution matches specification -/
theorem execute_clz_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnClz pc rs1 rs2 rd).temp1 = specClz rs1 := by
  rfl

/-- `ctz` execution matches specification -/
theorem execute_ctz_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnCtz pc rs1 rs2 rd).temp1 = specCtz rs1 := by
  rfl

/-- `cpop` execution matches specification -/
theorem execute_cpop_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnCpop pc rs1 rs2 rd).temp1 = specCpop rs1 := by
  rfl

/-- `orc_b` execution matches specification -/
theorem execute_orc_b_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnOrcB pc rs1 rs2 rd).temp1 = specOrcB rs1 := by
  rfl

/-- `rev8` execution matches specification -/
theorem execute_rev8_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnRev8 pc rs1 rs2 rd).temp1 = specRev8 rs1 := by
  rfl

/-- `sext_b` execution matches specification -/
theorem execute_sext_b_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnSextB pc rs1 rs2 rd).temp0 = specSextB rs1 := by
  rfl

/-- `sext_h` execution matches specification -/
theorem execute_sext_h_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnSextH pc rs1 rs2 rd).temp0 = specSextH rs1 := by
  rfl

/-- `zext_h` execution matches specification -/
theorem execute_zext_h_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnZextH pc rs1 rs2 rd).temp0 = specZextH rs1 := by
  rfl

/-- `clzw` execution matches specification -/
theorem execute_clzw_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnClzw pc rs1 rs2 rd).temp1 = specClzw rs1 := by
  rfl

/-- `ctzw` execution matches specification -/
theorem execute_ctzw_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnCtzw pc rs1 rs2 rd).temp1 = specCtzw rs1 := by
  rfl

/-- `cpopw` execution matches specification -/
theorem execute_cpopw_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnCpopw pc rs1 rs2 rd).temp1 = specCpopw rs1 := by
  rfl

/-- `rolw` execution matches specification -/
theorem execute_rolw_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnRolw pc rs1 rs2 rd).temp2 = specRolw rs1 rs2 := by
  rfl

/-- `rorw` execution matches specification -/
theorem execute_rorw_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnRorw pc rs1 rs2 rd).temp2 = specRorw rs1 rs2 := by
  rfl

/-- `roriw` execution matches specification -/
theorem execute_roriw_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnRoriw pc rs1 rs2 rd).temp2 = specRorw rs1 (insnShamt insnRoriw) := by
  rfl

/-- `add_uw` execution matches specification -/
theorem execute_add_uw_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnAddUw pc rs1 rs2 rd).temp2 = specAddUw rs1 rs2 := by
  rfl

/-- `sh1add_uw` execution matches specification -/
theorem execute_sh1add_uw_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnSh1addUw pc rs1 rs2 rd).temp2 = specSh1addUw rs1 rs2 := by
  rfl

/-- `sh2add_uw` execution matches specification -/
theorem execute_sh2add_uw_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnSh2addUw pc rs1 rs2 rd).temp2 = specSh2addUw rs1 rs2 := by
  rfl

/-- `sh3add_uw` execution matches specification -/
theorem execute_sh3add_uw_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnSh3addUw pc rs1 rs2 rd).temp2 = specSh3addUw rs1 rs2 := by
  rfl

/-- `slli_uw` execution matches specification -/
theorem execute_slli_uw_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnSlliUw pc rs1 rs2 rd).temp2 = specSlliUw rs1 (insnShamt insnSlliUw) := by
  rfl

/-! ## 3. Dispatch theorem -/

/-- Every one of the 43 sample encodings selects a real routine, never the
    illegal slot.  A decoder regression fails here before it can turn an
    instruction into a trap. -/
theorem routineIndex_total :
    ((List.finRange routineCount).all fun r => (routineIndex (zbRoutineSample r)).isSome) = true :=
  by decide

/-! ## 4. Fault preservation theorems -/

/-- Undefined / Illegal instruction: 0x00000000 -/
def insnIllegalZero : UInt32 := 0x00000000

/-- Unallocated custom opcode: 0x0000007b -/
def insnIllegalCustom : UInt32 := 0x0000007b

/-- Zero instruction triggers illegal instruction trap -/
theorem fault_on_zero (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    let res := executeFallback insnIllegalZero pc rs1 rs2 rd
    res.trapTaken = true ∧ res.trapCause = 2 ∧ res.trapVal = 0 := by
  refine ⟨rfl, rfl, rfl⟩

/-- Unallocated custom opcode triggers illegal instruction trap -/
theorem fault_on_custom (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    let res := executeFallback insnIllegalCustom pc rs1 rs2 rd
    res.trapTaken = true ∧ res.trapCause = 2 ∧ res.trapVal = 0x7b := by
  refine ⟨rfl, rfl, rfl⟩

/-- General theorem: any instruction outside the emulated table causes an
    illegal trap -/
theorem unemulated_causes_trap (insn : UInt32) (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    routineIndex insn = none →
    let res := executeFallback insn pc rs1 rs2 rd
    res.trapTaken = true ∧ res.trapCause = 2 ∧ res.trapVal = UInt64.ofNat insn.toNat ∧
      res.done = true := by
  intro hNone
  simp only [executeFallback, routineOps, hNone, runProgram, illegalInsnRoutine,
    stepFallback, readTemp, writeTemp]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Shoumei.RISCV.Microcode

/-
  TestGen/RandAlphabet.lean - The instruction alphabet a random program draws from.

  Two sources, and no others: the instructions the hardware decoder decodes for
  the active configuration, and the Zb* encodings the microcoded fallback
  sequencer emulates.  Both come from tables the RTL itself is built from, so
  the generator cannot emit an encoding the core has no path for.
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.OpcodeParser
import Shoumei.RISCV.Config
import Shoumei.RISCV.Microcode.ZbEmulationLibrary

namespace Shoumei.TestGen

open Shoumei.RISCV

/-- One entry of the generator's instruction alphabet. -/
inductive InstrClass where
  /-- An instruction the hardware decoder decodes. -/
  | decoded (d : InstructionDef)
  /-- A Zb* encoding the microcoded fallback sequencer emulates. -/
  | zbRoutine (r : Fin Microcode.routineCount)

instance : Inhabited InstrClass := ⟨.zbRoutine ⟨0, by decide⟩⟩

/-- Two decoded classes are equal when they name the same instruction; two Zb*
    classes when they name the same routine. -/
instance : BEq InstrClass := ⟨fun a b =>
  match a, b with
  | .decoded x, .decoded y => x.opType == y.opType && x.name == y.name
  | .zbRoutine x, .zbRoutine y => x == y
  | _, _ => false⟩

/-- Instructions that must never appear in a straight-line payload: each one
    changes the PC or the privilege level, so a program that executes it leaves
    the generated body and the fixed oracle with it. -/
def excludedOpcodes : List OpType := [.ECALL, .EBREAK, .MRET, .WFI]

/-- Every instruction the core decodes, minus the control-transfer ones, plus
    the 43 emulated Zb* encodings. -/
def decodedAlphabet (defs : List InstructionDef) : List InstrClass :=
  (defs.filter (fun d => !excludedOpcodes.contains d.opType)).map .decoded ++
  (List.finRange Microcode.routineCount).map .zbRoutine

end Shoumei.TestGen

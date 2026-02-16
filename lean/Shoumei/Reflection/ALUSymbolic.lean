/-
Reflection/ALUSymbolic.lean - Symbolic evaluation of ALU32

Uses the verified symbolic evaluator to compute BoolExpr trees for each ALU output
bit (with concrete opcode, symbolic a/b). The correctness chain connects
`evalALU32` to `BoolExpr.eval` via `symCompileGates_correct`.
-/

import Std.Tactic.BVDecide
import Shoumei.Reflection.SymbolicCompile
import Shoumei.Reflection.BitVecPacking
import Shoumei.Circuits.Combinational.ALU
import Shoumei.Circuits.Combinational.KoggeStoneAdder
import Shoumei.Circuits.Combinational.Subtractor
import Shoumei.Circuits.Combinational.Comparator
import Shoumei.Circuits.Combinational.LogicUnit
import Shoumei.Circuits.Combinational.Shifter

namespace Shoumei.Reflection.ALUSymbolic

open Shoumei Shoumei.Reflection
open Shoumei.Circuits.Combinational

/-! ## Circuit definitions -/

def aluSubCircuitMap : List (String × Circuit) :=
  [("KoggeStoneAdder32", mkKoggeStoneAdder32),
   ("Subtractor32", mkSubtractor32),
   ("Comparator32", mkComparator32),
   ("LogicUnit32", mkLogicUnit32),
   ("Shifter32", mkShifter32)]

def mkALU32Flat : Circuit :=
  flattenAllFuel aluSubCircuitMap mkALU32 3

def mkALUInitMap (a b : BitVec 32) (op : BitVec 4) : WireMap :=
  bitVecToBindings "a" 32 a ++
  bitVecToBindings "b" 32 b ++
  bitVecToBindings "op" 4 op ++
  [(Wire.mk "zero", false), (Wire.mk "one", true)]

def evalALU32 (a b : BitVec 32) (op : BitVec 4) : BitVec 32 :=
  readResultBitVecMap (compileCircuit mkALU32Flat (mkALUInitMap a b op)) "result" 32

/-! ## Symbolic infrastructure -/

def aluAssign (a b : BitVec 32) : Nat → Bool :=
  fun i => if i < 32 then a.getLsbD i else b.getLsbD (i - 32)

def mkALUSymInit (op : BitVec 4) : SymWireMap :=
  (List.range 32).map (fun i => (Wire.mk s!"a_{i}", BoolExpr.var i)) ++
  (List.range 32).map (fun i => (Wire.mk s!"b_{i}", BoolExpr.var (32 + i))) ++
  (List.range 4).map (fun i => (Wire.mk s!"op_{i}", BoolExpr.lit (op.getLsbD i))) ++
  [(Wire.mk "zero", .lit false), (Wire.mk "one", .lit true)]

/-! ## Init map agreement

We prove that the symbolic init map agrees with the concrete init map
by showing they have the same structure and related values. -/

/-- Core lemma: evaluating a symbolic lookup equals looking up in the evaluated map. -/
private theorem sym_lookup_eval_list (xs : List (Wire × BoolExpr))
    (assign : Nat → Bool) (w : Wire) :
    (SymWireMap.lookup xs w).eval assign =
    WireMap.lookup (xs.map (fun p => (p.1, p.2.eval assign))) w := by
  induction xs with
  | nil =>
    simp [SymWireMap.lookup, WireMap.lookup, List.find?, BoolExpr.eval]
  | cons hd tl ih =>
    obtain ⟨w', e⟩ := hd
    unfold SymWireMap.lookup WireMap.lookup
    simp only [List.map, List.find?]
    cases hbeq : (w' == w) with
    | true => simp
    | false =>
      exact ih

/-- The symbolic init map agrees with the concrete init map under aluAssign. -/
theorem mkALUSymInit_correct (a b : BitVec 32) (op : BitVec 4) :
    ∀ w, (SymWireMap.lookup (mkALUSymInit op) w).eval (aluAssign a b) =
         WireMap.lookup (mkALUInitMap a b op) w := by
  intro w
  rw [sym_lookup_eval_list]
  -- Suffices to show the mapped sym list = the concrete list
  suffices h : (mkALUSymInit op).map (fun p => (p.1, p.2.eval (aluAssign a b))) =
               mkALUInitMap a b op by rw [h]
  simp only [mkALUSymInit, mkALUInitMap, bitVecToBindings,
             List.map_append, List.map_map, List.map_cons, List.map_nil,
             BoolExpr.eval]
  -- After simp, the goal should compare two List.map expressions.
  -- If simp didn't close it, use congr + map_eq_map_iff
  all_goals (first
    | rfl
    | (congr 1
       · rw [List.map_eq_map_iff]; intro i hi; simp [List.mem_range.mp hi]
       · congr 1
         · rw [List.map_eq_map_iff]; intro i hi
           have : i < 32 := List.mem_range.mp hi
           simp only [show ¬(32 + i < 32) from by omega, ite_false,
                      show 32 + i - 32 = i from by omega]
         · rfl))

/-! ## Symbolic compilation -/

def aluSymCompiled (op : BitVec 4) : SymWireMap :=
  symCompileGates mkALU32Flat.gates (mkALUSymInit op)

def aluSymResult (op : BitVec 4) (i : Nat) : BoolExpr :=
  SymWireMap.lookup (aluSymCompiled op) (Wire.mk s!"result_{i}")

/-! ## Reading symbolic results -/

def readSymResultAsNat (assign : Nat → Bool) (getExpr : Nat → BoolExpr) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let bit := if (getExpr n).eval assign then 1 else 0
    bit * (2 ^ n) + readSymResultAsNat assign getExpr n

theorem readSymResultAsNat_correct (assign : Nat → Bool) (m : WireMap)
    (name : String) (getExpr : Nat → BoolExpr)
    (h : ∀ i, (getExpr i).eval assign = m.lookup (Wire.mk s!"{name}_{i}"))
    (n : Nat) :
    readSymResultAsNat assign getExpr n = readWiresAsNatMap m name n := by
  induction n with
  | zero => simp [readSymResultAsNat, readWiresAsNatMap]
  | succ k ih =>
    simp only [readSymResultAsNat, readWiresAsNatMap]
    rw [h k, ih]

/-! ## Main correctness chain -/

/-- symCompileGates on circuit gates agrees with compileCircuit. -/
theorem symCompileCircuit_correct (c : Circuit) (sm : SymWireMap) (m : WireMap)
    (assign : Nat → Bool)
    (h : ∀ w, (sm.lookup w).eval assign = m.lookup w) :
    ∀ w, ((symCompileGates c.gates sm).lookup w).eval assign =
         (compileCircuit c m).lookup w :=
  symCompileGates_correct c.gates sm m assign h

/-- evalALU32 equals readResultBitVecMap of compileCircuit (definitional). -/
private theorem evalALU32_as_circuit (a b : BitVec 32) (op : BitVec 4) :
    evalALU32 a b op =
    readResultBitVecMap (compileCircuit mkALU32Flat (mkALUInitMap a b op)) "result" 32 := rfl

/-- readResultBitVecMap unfolds to BitVec.ofNat of readWiresAsNatMap. -/
private theorem readResultBitVecMap_unfold (m : WireMap) (name : String) (w : Nat) :
    readResultBitVecMap m name w = BitVec.ofNat w (readWiresAsNatMap m name w) := rfl

theorem evalALU32_eq_sym (a b : BitVec 32) (op : BitVec 4) :
    evalALU32 a b op =
    BitVec.ofNat 32 (readSymResultAsNat (aluAssign a b) (fun i => aluSymResult op i) 32) := by
  rw [evalALU32_as_circuit, readResultBitVecMap_unfold]
  -- Goal: BitVec.ofNat 32 (readWiresAsNatMap (compileCircuit mkALU32Flat ...) "result" 32) =
  --       BitVec.ofNat 32 (readSymResultAsNat ...)
  -- Suffices to show the Nat args agree
  apply congrArg (BitVec.ofNat 32)
  -- Show readWiresAsNatMap agrees with readSymResultAsNat
  symm
  apply readSymResultAsNat_correct
  intro i
  exact symCompileCircuit_correct mkALU32Flat (mkALUSymInit op)
    (mkALUInitMap a b op) (aluAssign a b) (mkALUSymInit_correct a b op)
    (Wire.mk s!"result_{i}")

/-! ## ALU operation types -/

inductive ALUOp where
  | ADD | SUB | SLT | SLTU | AND | OR | XOR | SLL | SRL | SRA
  deriving Repr, BEq, DecidableEq

def ALUOp.toOpcode : ALUOp → BitVec 4
  | .ADD  => 0x0  | .SUB  => 0x1  | .SLT  => 0x2  | .SLTU => 0x3
  | .AND  => 0x4  | .OR   => 0x5  | .XOR  => 0x6
  | .SLL  => 0x8  | .SRL  => 0x9  | .SRA  => 0xB

def aluSemantics (op : ALUOp) (a b : BitVec 32) : BitVec 32 :=
  match op with
  | .ADD  => a + b
  | .SUB  => a - b
  | .SLT  => if decide (a.toInt < b.toInt) then 1 else 0
  | .SLTU => if decide (a < b) then 1 else 0
  | .AND  => a &&& b
  | .OR   => a ||| b
  | .XOR  => a ^^^ b
  | .SLL  => a <<< (b &&& 0x1F#32).toNat
  | .SRL  => a >>> (b &&& 0x1F#32).toNat
  | .SRA  => a.sshiftRight (b &&& 0x1F#32).toNat

/-! ## Generic readSymResultAsNat lemmas -/

private theorem readSymResultAsNat_bound (assign : Nat → Bool) (f : Nat → BoolExpr) (n : Nat) :
    readSymResultAsNat assign f n < 2 ^ n := by
  induction n with
  | zero => simp [readSymResultAsNat]
  | succ k ih => simp only [readSymResultAsNat]; split <;> simp <;> omega

private theorem readSymResultAsNat_testBit (assign : Nat → Bool) (f : Nat → BoolExpr)
    (n i : Nat) (hi : i < n) :
    (readSymResultAsNat assign f n).testBit i = (f i).eval assign := by
  induction n with
  | zero => omega
  | succ k ih =>
    simp only [readSymResultAsNat]
    have hbound := readSymResultAsNat_bound assign f k
    by_cases hik : i = k
    · subst hik
      split <;> rename_i heval <;> simp
      · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hbound]; simp [heval]
      · rw [Nat.testBit_lt_two_pow hbound]; simp [heval]
    · have hik' : i < k := by omega
      split <;> simp
      · rw [Nat.testBit_two_pow_add_gt (by omega)]; exact ih hik'
      · exact ih hik'

/-! ## Per-opcode bridge theorems and axioms

The verified symbolic infrastructure reduces each opcode to a BoolExpr
equivalence check. AND/OR/XOR are proven via constFold; the rest remain axioms
pending similar treatment for arithmetic/shift operations. -/

-- Bitwise per-bit helper: constFold reduces to the expected simple form
private theorem and_constFold_all :
    ∀ i : Fin 32,
      (aluSymResult 0x4 i.val).constFold = .and (.var i.val) (.var (32 + i.val)) := by
  native_decide

private theorem or_constFold_all :
    ∀ i : Fin 32,
      (aluSymResult 0x5 i.val).constFold = .or (.var i.val) (.var (32 + i.val)) := by
  native_decide

private theorem xor_constFold_all :
    ∀ i : Fin 32,
      (aluSymResult 0x6 i.val).constFold = .xor (.var i.val) (.var (32 + i.val)) := by
  native_decide

-- Generic per-bit proof for bitwise ops via constFold
private theorem bitwise_bit_correct (a b : BitVec 32)
    (op : BitVec 4) (i : Nat) (hi : i < 32)
    (expected : BoolExpr)
    (hcf : (aluSymResult op i).constFold = expected)
    (heval : expected.eval (aluAssign a b) = (a.getLsbD i && b.getLsbD i)) :
    (aluSymResult op i).eval (aluAssign a b) = (a.getLsbD i && b.getLsbD i) := by
  rw [← BoolExpr.constFold_correct, hcf, heval]

private theorem bitwise_bridge (a b : BitVec 32) (op : BitVec 4) (rhs : BitVec 32)
    (hbits : ∀ i, i < 32 → (aluSymResult op i).eval (aluAssign a b) = rhs.getLsbD i) :
    evalALU32 a b op = rhs := by
  rw [evalALU32_eq_sym]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ofNat, readSymResultAsNat_testBit _ _ 32 i hi]
  simp only [hi, decide_true, Bool.true_and]
  exact hbits i hi

-- AND: proven
theorem alu32_bridge_and (a b : BitVec 32) : evalALU32 a b 0x4 = a &&& b := by
  apply bitwise_bridge a b 0x4 (a &&& b)
  intro i hi
  rw [BitVec.getLsbD_and]
  exact bitwise_bit_correct a b 0x4 i hi _ (and_constFold_all ⟨i, hi⟩)
    (by simp [BoolExpr.eval, aluAssign, hi, show ¬(32 + i < 32) from by omega,
              show 32 + i - 32 = i from by omega])

-- OR: proven
theorem alu32_bridge_or (a b : BitVec 32) : evalALU32 a b 0x5 = a ||| b := by
  apply bitwise_bridge a b 0x5 (a ||| b)
  intro i hi
  rw [BitVec.getLsbD_or]
  exact bitwise_bit_correct a b 0x5 i hi _ (or_constFold_all ⟨i, hi⟩)
    (by simp [BoolExpr.eval, aluAssign, hi, show ¬(32 + i < 32) from by omega,
              show 32 + i - 32 = i from by omega])

-- XOR: proven
theorem alu32_bridge_xor (a b : BitVec 32) : evalALU32 a b 0x6 = a ^^^ b := by
  apply bitwise_bridge a b 0x6 (a ^^^ b)
  intro i hi
  rw [BitVec.getLsbD_xor]
  exact bitwise_bit_correct a b 0x6 i hi _ (xor_constFold_all ⟨i, hi⟩)
    (by simp [BoolExpr.eval, Bool.xor, aluAssign, hi, show ¬(32 + i < 32) from by omega,
              show 32 + i - 32 = i from by omega])

-- Remaining axioms (arithmetic and shift operations)
axiom alu32_bridge_add : ∀ (a b : BitVec 32), evalALU32 a b 0x0 = a + b
axiom alu32_bridge_sub : ∀ (a b : BitVec 32), evalALU32 a b 0x1 = a - b
axiom alu32_bridge_slt : ∀ (a b : BitVec 32),
    evalALU32 a b 0x2 = if decide (a.toInt < b.toInt) then 1 else 0
axiom alu32_bridge_sltu : ∀ (a b : BitVec 32),
    evalALU32 a b 0x3 = if decide (a < b) then 1 else 0
axiom alu32_bridge_sll : ∀ (a b : BitVec 32),
    evalALU32 a b 0x8 = a <<< (b &&& 0x1F#32).toNat
axiom alu32_bridge_srl : ∀ (a b : BitVec 32),
    evalALU32 a b 0x9 = a >>> (b &&& 0x1F#32).toNat
axiom alu32_bridge_sra : ∀ (a b : BitVec 32),
    evalALU32 a b 0xB = a.sshiftRight (b &&& 0x1F#32).toNat

/-- The main bridge theorem, proven from per-opcode axioms. -/
theorem alu32_bridge (op : ALUOp) (a b : BitVec 32) :
    evalALU32 a b op.toOpcode = aluSemantics op a b := by
  cases op <;> simp only [ALUOp.toOpcode, aluSemantics]
  · exact alu32_bridge_add a b
  · exact alu32_bridge_sub a b
  · exact alu32_bridge_slt a b
  · exact alu32_bridge_sltu a b
  · exact alu32_bridge_and a b
  · exact alu32_bridge_or a b
  · exact alu32_bridge_xor a b
  · exact alu32_bridge_sll a b
  · exact alu32_bridge_srl a b
  · exact alu32_bridge_sra a b

end Shoumei.Reflection.ALUSymbolic

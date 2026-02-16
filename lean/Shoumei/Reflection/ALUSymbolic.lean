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
    (op : BitVec 4) (i : Nat)
    (expected : BoolExpr) (result : Bool)
    (hcf : (aluSymResult op i).constFold = expected)
    (heval : expected.eval (aluAssign a b) = result) :
    (aluSymResult op i).eval (aluAssign a b) = result := by
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
  exact bitwise_bit_correct a b 0x4 i _ _ (and_constFold_all ⟨i, hi⟩)
    (by simp [BoolExpr.eval, aluAssign, hi, show ¬(32 + i < 32) from by omega,
              show 32 + i - 32 = i from by omega])

-- OR: proven
theorem alu32_bridge_or (a b : BitVec 32) : evalALU32 a b 0x5 = a ||| b := by
  apply bitwise_bridge a b 0x5 (a ||| b)
  intro i hi
  rw [BitVec.getLsbD_or]
  exact bitwise_bit_correct a b 0x5 i _ _ (or_constFold_all ⟨i, hi⟩)
    (by simp [BoolExpr.eval, aluAssign, hi, show ¬(32 + i < 32) from by omega,
              show 32 + i - 32 = i from by omega])

-- XOR: proven
theorem alu32_bridge_xor (a b : BitVec 32) : evalALU32 a b 0x6 = a ^^^ b := by
  apply bitwise_bridge a b 0x6 (a ^^^ b)
  intro i hi
  rw [BitVec.getLsbD_xor]
  exact bitwise_bit_correct a b 0x6 i _ _ (xor_constFold_all ⟨i, hi⟩)
    (by simp [BoolExpr.eval, Bool.xor, aluAssign, hi, show ¬(32 + i < 32) from by omega,
              show 32 + i - 32 = i from by omega])

/-! ## ADD bridge: three-layer proof -/

-- Layer 3: Ripple-carry Bool functions match BitVec addition
private def carryBit (a b : BitVec 32) : Nat → Bool
  | 0 => a.getLsbD 0 && b.getLsbD 0
  | n + 1 => (a.getLsbD (n+1) && b.getLsbD (n+1)) ||
             ((a.getLsbD (n+1) ^^ b.getLsbD (n+1)) && carryBit a b n)

private def sumBit (a b : BitVec 32) : Nat → Bool
  | 0 => a.getLsbD 0 ^^ b.getLsbD 0
  | n + 1 => (a.getLsbD (n+1) ^^ b.getLsbD (n+1)) ^^ carryBit a b n

-- Layer 3: Connect carryBit/sumBit to BitVec.carry/getLsbD_add from stdlib

private theorem atLeastTwo_eq_xor_form (x y c : Bool) :
    Bool.atLeastTwo x y c = (x && y) || ((x ^^ y) && c) := by
  cases x <;> cases y <;> cases c <;> rfl

private theorem carryBit_eq_carry (a b : BitVec 32) (n : Nat) :
    carryBit a b n = BitVec.carry (n + 1) a b false := by
  induction n with
  | zero =>
    simp only [carryBit, BitVec.carry_succ, BitVec.carry_zero,
               Bool.atLeastTwo_false_right]
  | succ k ih =>
    simp only [carryBit, ih, BitVec.carry_succ]
    cases a.getLsbD (k + 1) <;> cases b.getLsbD (k + 1) <;> simp [Bool.atLeastTwo]

private theorem sumBit_eq_getLsbD_add (a b : BitVec 32) (i : Nat) (hi : i < 32) :
    sumBit a b i = (a + b).getLsbD i := by
  rw [BitVec.getLsbD_add hi]
  cases i with
  | zero =>
    simp [sumBit, BitVec.carry_zero]
  | succ k =>
    simp only [sumBit, carryBit_eq_carry]
    -- Goal: a.getLsbD (k+1) ^^ b.getLsbD (k+1) ^^ carry (k+1) a b false
    --     = a.getLsbD (k+1) ^^ (b.getLsbD (k+1) ^^ carry (k+1) a b false)
    rw [Bool.xor_assoc]

-- Layer 2: Ripple-carry BoolExpr evaluates to sumBit
private def adderCarry : Nat → BoolExpr
  | 0 => .and (.var 0) (.var 32)
  | n + 1 => .or (.and (.var (n+1)) (.var (33+n)))
                 (.and (.xor (.var (n+1)) (.var (33+n))) (adderCarry n))

private def adderSum : Nat → BoolExpr
  | 0 => .xor (.var 0) (.var 32)
  | n + 1 => .xor (.xor (.var (n+1)) (.var (33+n))) (adderCarry n)

private theorem adderCarry_eval (a b : BitVec 32) (n : Nat) (hn : n < 32) :
    (adderCarry n).eval (aluAssign a b) = carryBit a b n := by
  induction n with
  | zero => simp [adderCarry, carryBit, BoolExpr.eval, aluAssign]
  | succ k ih =>
    simp only [adderCarry, carryBit, BoolExpr.eval, aluAssign]
    have hk : k < 32 := by omega
    rw [ih hk]
    simp only [show k + 1 < 32 from by omega, ite_true,
               show ¬(33 + k < 32) from by omega, ite_false,
               show 33 + k - 32 = k + 1 from by omega]

private theorem adderSum_eval (a b : BitVec 32) (i : Nat) (hi : i < 32) :
    (adderSum i).eval (aluAssign a b) = sumBit a b i := by
  cases i with
  | zero => simp [adderSum, sumBit, BoolExpr.eval, aluAssign]
  | succ k =>
    simp only [adderSum, sumBit, BoolExpr.eval, aluAssign]
    have hk : k < 32 := by omega
    rw [adderCarry_eval a b k hk]
    simp only [show k + 1 < 32 from by omega, ite_true,
               show ¬(33 + k < 32) from by omega, ite_false,
               show 33 + k - 32 = k + 1 from by omega]

-- Layer 1: KSA BoolExpr ≡ ripple-carry BoolExpr (via verified semantic checker)
-- Interleaved var order: [a_0, b_0, a_1, b_1, ...] so carry chains collapse during constFold
private def addVarsForBit (i : Nat) : List Nat :=
  (List.range (i + 1)).flatMap (fun k => [k, 32 + k])

private theorem ksa_eq_ripple :
    ∀ i : Fin 32, BoolExpr.beqSem (aluSymResult 0x0 i.val) (adderSum i.val) (addVarsForBit i.val) = true := by
  native_decide

private theorem ksa_bit_correct (a b : BitVec 32) (i : Nat) (hi : i < 32) :
    (aluSymResult 0x0 i).eval (aluAssign a b) = (a + b).getLsbD i := by
  have h1 := BoolExpr.beqSem_correct _ _ _ (ksa_eq_ripple ⟨i, hi⟩) (aluAssign a b)
  rw [h1, adderSum_eval a b i hi, sumBit_eq_getLsbD_add a b i hi]

-- Assembly: replace axiom with theorem
theorem alu32_bridge_add (a b : BitVec 32) : evalALU32 a b 0x0 = a + b := by
  apply bitwise_bridge a b 0x0 (a + b)
  intro i hi
  exact ksa_bit_correct a b i hi

/-! ## SUB bridge: three-layer proof

SUB uses the identity `a - b = a + ~~~b + 1` (two's complement).
The KSA computes the addition with complemented b and carry-in = 1. -/

-- Layer 3: Ripple-carry Bool functions for subtraction (complement b, carry-in = 1)
private def subCarryBit (a b : BitVec 32) : Nat → Bool
  | 0 => a.getLsbD 0 || !b.getLsbD 0  -- atLeastTwo(a0, !b0, cin=1)
  | n + 1 => (a.getLsbD (n+1) && !b.getLsbD (n+1)) ||
             ((a.getLsbD (n+1) ^^ !b.getLsbD (n+1)) && subCarryBit a b n)

private def subSumBit (a b : BitVec 32) : Nat → Bool
  | 0 => a.getLsbD 0 ^^ b.getLsbD 0  -- a0 ^^ !b0 ^^ cin(=1) = a0 ^^ b0
  | n + 1 => (a.getLsbD (n+1) ^^ !b.getLsbD (n+1)) ^^ subCarryBit a b n

-- Layer 3: Connect to (a - b).getLsbD via per-bit bv_decide
private theorem subSumBit_eq_getLsbD_sub (a b : BitVec 32) (i : Nat) (hi : i < 32) :
    subSumBit a b i = (a - b).getLsbD i := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ |
                 _ | _ | _ | _ | _ | _ | _ | _ |
                 _ | _ | _ | _ | _ | _ | _ | _ |
                 _ | _ | _ | _ | _ | _ | _ | _ | i
  all_goals first | (dsimp only [subSumBit, subCarryBit]; bv_decide) | omega

-- Layer 2: Ripple-carry BoolExpr evaluates to subSumBit
private def subAdderCarry : Nat → BoolExpr
  | 0 => .or (.var 0) (.not (.var 32))
  | n + 1 => .or (.and (.var (n+1)) (.not (.var (33+n))))
                 (.and (.xor (.var (n+1)) (.not (.var (33+n)))) (subAdderCarry n))

private def subAdderSum : Nat → BoolExpr
  | 0 => .xor (.var 0) (.var 32)
  | n + 1 => .xor (.xor (.var (n+1)) (.not (.var (33+n)))) (subAdderCarry n)

private theorem subAdderCarry_eval (a b : BitVec 32) (n : Nat) (hn : n < 32) :
    (subAdderCarry n).eval (aluAssign a b) = subCarryBit a b n := by
  induction n with
  | zero => simp [subAdderCarry, subCarryBit, BoolExpr.eval, aluAssign]
  | succ k ih =>
    simp only [subAdderCarry, subCarryBit, BoolExpr.eval, aluAssign]
    have hk : k < 32 := by omega
    rw [ih hk]
    simp only [show k + 1 < 32 from by omega, ite_true,
               show ¬(33 + k < 32) from by omega, ite_false,
               show 33 + k - 32 = k + 1 from by omega]

private theorem subAdderSum_eval (a b : BitVec 32) (i : Nat) (hi : i < 32) :
    (subAdderSum i).eval (aluAssign a b) = subSumBit a b i := by
  cases i with
  | zero => simp [subAdderSum, subSumBit, BoolExpr.eval, aluAssign]
  | succ k =>
    simp only [subAdderSum, subSumBit, BoolExpr.eval, aluAssign]
    have hk : k < 32 := by omega
    rw [subAdderCarry_eval a b k hk]
    simp only [show k + 1 < 32 from by omega, ite_true,
               show ¬(33 + k < 32) from by omega, ite_false,
               show 33 + k - 32 = k + 1 from by omega]

-- Layer 1: KSA BoolExpr ≡ ripple-carry BoolExpr (via verified semantic checker)
private theorem ksa_sub_eq_ripple :
    ∀ i : Fin 32, BoolExpr.beqSem (aluSymResult 0x1 i.val) (subAdderSum i.val) (addVarsForBit i.val) = true := by
  native_decide

private theorem ksa_sub_bit_correct (a b : BitVec 32) (i : Nat) (hi : i < 32) :
    (aluSymResult 0x1 i).eval (aluAssign a b) = (a - b).getLsbD i := by
  have h1 := BoolExpr.beqSem_correct _ _ _ (ksa_sub_eq_ripple ⟨i, hi⟩) (aluAssign a b)
  rw [h1, subAdderSum_eval a b i hi, subSumBit_eq_getLsbD_sub a b i hi]

-- Assembly
theorem alu32_bridge_sub (a b : BitVec 32) : evalALU32 a b 0x1 = a - b := by
  apply bitwise_bridge a b 0x1 (a - b)
  intro i hi
  exact ksa_sub_bit_correct a b i hi

/-! ## SLT bridge: signed less-than comparison

Result is 1 if a <s b, else 0. Only bit 0 is nontrivial. -/

-- Helper: getLsbD of small BitVec constants for i ≥ 1
private theorem getLsbD_one_high (i : Nat) (hi : i ≥ 1) (_hi32 : i < 32) :
    (1 : BitVec 32).getLsbD i = false := by
  simp only [BitVec.getLsbD, BitVec.toNat, Nat.testBit, Nat.shiftRight_eq_div_pow]
  have h2 : 1 < 2 ^ i := Nat.one_lt_two_pow_iff.mpr (by omega)
  simp [Nat.div_eq_of_lt h2]

private theorem getLsbD_zero_any (i : Nat) (_hi : i < 32) :
    (0 : BitVec 32).getLsbD i = false := by
  simp [BitVec.getLsbD, BitVec.toNat]

-- Bits 1-31 are all zero
private theorem slt_high_bits_zero :
    ∀ i : Fin 31, (aluSymResult 0x2 (i.val + 1)).constFold = .lit false := by
  native_decide

-- Bit 0: signed less-than via subtraction MSB
private def sltRefExpr : BoolExpr :=
  .or (.and (.var 31) (.not (.var 63)))
      (.and (.not (.xor (.var 31) (.var 63))) (subAdderSum 31))

private theorem slt_bit0_eq_ref :
    BoolExpr.beqSem (aluSymResult 0x2 0) sltRefExpr (addVarsForBit 31) = true := by
  native_decide

private theorem sltRefExpr_eval (a b : BitVec 32) :
    sltRefExpr.eval (aluAssign a b) =
    ((a.getLsbD 31 && !b.getLsbD 31) ||
     (!(a.getLsbD 31 ^^ b.getLsbD 31) && (a - b).getLsbD 31)) := by
  simp only [sltRefExpr, BoolExpr.eval, aluAssign,
             show (31 : Nat) < 32 from by omega, ite_true,
             show ¬((63 : Nat) < 32) from by omega, ite_false,
             show (63 : Nat) - 32 = 31 from by omega]
  rw [subAdderSum_eval a b 31 (by omega), subSumBit_eq_getLsbD_sub a b 31 (by omega)]

-- SLT formula: the bit-level formula equals the signed comparison
-- We reformulate using BitVec.slt to help bv_decide
private theorem slt_formula_correct (a b : BitVec 32) :
    ((a.getLsbD 31 && !b.getLsbD 31) ||
     (!(a.getLsbD 31 ^^ b.getLsbD 31) && (a - b).getLsbD 31)) =
    decide (a.toInt < b.toInt) := by
  rw [← BitVec.slt_eq_decide]
  bv_decide

theorem alu32_bridge_slt (a b : BitVec 32) :
    evalALU32 a b 0x2 = if decide (a.toInt < b.toInt) then 1 else 0 := by
  apply bitwise_bridge a b 0x2 (if decide (a.toInt < b.toInt) then 1 else 0)
  intro i hi
  by_cases hi0 : i = 0
  · subst hi0
    have h1 := BoolExpr.beqSem_correct _ _ _ slt_bit0_eq_ref (aluAssign a b)
    rw [h1, sltRefExpr_eval, slt_formula_correct]
    have h1bit : (1 : BitVec 32).getLsbD 0 = true := by native_decide
    have h0bit : (0 : BitVec 32).getLsbD 0 = false := by native_decide
    split <;> simp [*]
  · have hi31 : i - 1 < 31 := by omega
    have hcf := slt_high_bits_zero ⟨i - 1, hi31⟩
    have : i - 1 + 1 = i := by omega
    rw [this] at hcf
    rw [← BoolExpr.constFold_correct, hcf, BoolExpr.eval]
    symm
    split <;> exact (by
      first
      | exact getLsbD_one_high i (by omega) hi
      | exact getLsbD_zero_any i hi)

/-! ## SLTU bridge: unsigned less-than comparison -/

-- Bits 1-31 are all zero
private theorem sltu_high_bits_zero :
    ∀ i : Fin 31, (aluSymResult 0x3 (i.val + 1)).constFold = .lit false := by
  native_decide

-- Bit 0: unsigned less-than
private def sltuRefExpr : BoolExpr :=
  .or (.and (.not (.var 31)) (.var 63))
      (.and (.not (.xor (.var 31) (.var 63))) (subAdderSum 31))

private theorem sltu_bit0_eq_ref :
    BoolExpr.beqSem (aluSymResult 0x3 0) sltuRefExpr (addVarsForBit 31) = true := by
  native_decide

private theorem sltuRefExpr_eval (a b : BitVec 32) :
    sltuRefExpr.eval (aluAssign a b) =
    ((!a.getLsbD 31 && b.getLsbD 31) ||
     (!(a.getLsbD 31 ^^ b.getLsbD 31) && (a - b).getLsbD 31)) := by
  simp only [sltuRefExpr, BoolExpr.eval, aluAssign,
             show (31 : Nat) < 32 from by omega, ite_true,
             show ¬((63 : Nat) < 32) from by omega, ite_false,
             show (63 : Nat) - 32 = 31 from by omega]
  rw [subAdderSum_eval a b 31 (by omega), subSumBit_eq_getLsbD_sub a b 31 (by omega)]

private theorem sltu_formula_correct (a b : BitVec 32) :
    ((!a.getLsbD 31 && b.getLsbD 31) ||
     (!(a.getLsbD 31 ^^ b.getLsbD 31) && (a - b).getLsbD 31)) =
    decide (a < b) := by
  bv_decide

theorem alu32_bridge_sltu (a b : BitVec 32) :
    evalALU32 a b 0x3 = if decide (a < b) then 1 else 0 := by
  apply bitwise_bridge a b 0x3 (if decide (a < b) then 1 else 0)
  intro i hi
  by_cases hi0 : i = 0
  · subst hi0
    have h1 := BoolExpr.beqSem_correct _ _ _ sltu_bit0_eq_ref (aluAssign a b)
    rw [h1, sltuRefExpr_eval, sltu_formula_correct]
    have h1bit : (1 : BitVec 32).getLsbD 0 = true := by native_decide
    have h0bit : (0 : BitVec 32).getLsbD 0 = false := by native_decide
    split <;> simp [*]
  · have hi31 : i - 1 < 31 := by omega
    have hcf := sltu_high_bits_zero ⟨i - 1, hi31⟩
    have : i - 1 + 1 = i := by omega
    rw [this] at hcf
    rw [← BoolExpr.constFold_correct, hcf, BoolExpr.eval]
    symm
    split <;> exact (by
      first
      | exact getLsbD_one_high i (by omega) hi
      | exact getLsbD_zero_any i hi)
/-! ## Shift operations: shared infrastructure

All three shifts (SLL, SRL, SRA) use a barrel shifter controlled by b[4:0].
We build a MUX-tree BoolExpr reference, verify it matches the circuit via beqSem,
then prove the MUX tree evaluates to the correct BitVec shift operation. -/

-- Build a 2^n-way MUX tree indexed by vars (32+0),...,(32+n-1)
private def buildShiftMux : Nat → (Nat → BoolExpr) → Nat → BoolExpr
  | 0, f, base => f base
  | n + 1, f, base =>
    BoolExpr.ite (.var (32 + n))
      (buildShiftMux n f (base + 2^n))
      (buildShiftMux n f base)

-- What buildShiftMux decodes to
private def decodeShift (assign : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => (if assign (32 + n) then 2^n else 0) + decodeShift assign n

private theorem buildShiftMux_eval (n : Nat) (f : Nat → BoolExpr) (base : Nat)
    (assign : Nat → Bool) :
    (buildShiftMux n f base).eval assign =
    (f (base + decodeShift assign n)).eval assign := by
  induction n generalizing base with
  | zero => simp [buildShiftMux, decodeShift]
  | succ k ih =>
    unfold buildShiftMux decodeShift
    simp only [BoolExpr.eval]
    split
    · rw [ih]; congr 1; rw [Nat.add_assoc]
    · rw [ih]; congr 1; rw [Nat.zero_add]

-- Key number-theoretic helper: n % 2^(k+1) = 2^k * (n/2^k % 2) + n % 2^k
private theorem nat_mod_two_mul (n m : Nat) (_hm : 0 < m) :
    n % (2 * m) = m * (n / m % 2) + n % m := by
  have h3 : n / m / 2 = n / (2 * m) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  have hm1 := Nat.div_add_mod n m
  have hm2 := Nat.div_add_mod n (2 * m)
  have hm3 := Nat.div_add_mod (n / m) 2
  rw [h3] at hm3
  rcases Nat.mod_two_eq_zero_or_one (n / m) with h | h
  · rw [h] at hm3 ⊢
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero] at hm3 ⊢
    rw [← hm3, show m * (2 * (n / (2 * m))) = 2 * m * (n / (2 * m)) from by
      rw [Nat.mul_left_comm, Nat.mul_assoc]] at hm1
    omega
  · rw [h] at hm3 ⊢
    simp only [Nat.mul_one] at ⊢
    rw [← hm3, show m * (2 * (n / (2 * m)) + 1) = 2 * m * (n / (2 * m)) + m from by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, Nat.mul_assoc]] at hm1
    omega

-- Connect testBit to the coefficient in binary expansion
private theorem testBit_ite_mul_eq (n k : Nat) :
    (if n.testBit k then 2^k else 0) = 2^k * (n / 2^k % 2) := by
  have hm : n / 2^k % 2 = 0 ∨ n / 2^k % 2 = 1 := Nat.mod_two_eq_zero_or_one _
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases hm with h | h <;> simp [h]

-- Connect decodeShift to b.toNat % 2^n
private theorem decodeShift_eq_mod (a b : BitVec 32) (n : Nat) (hn : n ≤ 32) :
    decodeShift (aluAssign a b) n = b.toNat % 2^n := by
  induction n with
  | zero => simp [decodeShift, Nat.mod_one]
  | succ k ih =>
    unfold decodeShift
    simp only [aluAssign, show ¬(32 + k < 32) from by omega, ite_false,
               show 32 + k - 32 = k from by omega]
    rw [ih (by omega)]
    rw [show b.getLsbD k = b.toNat.testBit k from rfl]
    rw [testBit_ite_mul_eq]
    have h2k : (2 : Nat)^(k+1) = 2 * 2^k := by
      rw [Nat.pow_succ]; exact Nat.mul_comm _ _
    rw [h2k]
    exact (nat_mod_two_mul b.toNat (2^k) (Nat.pos_of_ne_zero (by omega))).symm

-- Connect (b &&& 0x1F).toNat to b.toNat % 32
private theorem and_mask_eq_mod (b : BitVec 32) :
    (b &&& 0x1F#32).toNat = b.toNat % 32 := by
  rw [BitVec.toNat_and]
  show b.toNat &&& (2^5 - 1) = b.toNat % 2^5
  exact Nat.and_two_pow_sub_one_eq_mod b.toNat 5

private theorem decodeShift_eq_mask (a b : BitVec 32) :
    decodeShift (aluAssign a b) 5 = (b &&& 0x1F#32).toNat := by
  rw [and_mask_eq_mod, decodeShift_eq_mod a b 5 (by omega)]

-- Variable list for shift beqSem: control bits first, then data bits
private def shiftVars : List Nat := [32, 33, 34, 35, 36] ++ List.range 32

/-! ### SLL (shift left logical, opcode 0x8) -/

private def sllRefBit (i : Nat) : BoolExpr :=
  buildShiftMux 5 (fun s => if i ≥ s then .var (i - s) else .lit false) 0

private theorem sll_beqSem :
    ∀ i : Fin 32, BoolExpr.beqSem (aluSymResult 0x8 i.val) (sllRefBit i.val) shiftVars = true := by
  native_decide

private theorem sllRefBit_eval (a b : BitVec 32) (i : Nat) (hi : i < 32) :
    (sllRefBit i).eval (aluAssign a b) =
    (a <<< (b &&& 0x1F#32).toNat).getLsbD i := by
  simp only [sllRefBit]
  rw [buildShiftMux_eval, Nat.zero_add, decodeShift_eq_mask]
  have hs : (b &&& 0x1F#32).toNat < 32 := by rw [and_mask_eq_mod]; omega
  rw [BitVec.getLsbD_shiftLeft]
  simp only [show (decide (i < 32) : Bool) = true from by simp [hi], Bool.true_and]
  split
  · -- i ≥ s: result is a.getLsbD (i - s)
    rename_i hge
    simp only [BoolExpr.eval, aluAssign, show i - (b &&& 0x1F#32).toNat < 32 from by omega, ite_true,
               show ¬(i < (b &&& 0x1F#32).toNat) from by omega, decide_false, Bool.not_false,
               Bool.true_and]
  · -- i < s: result is false
    rename_i hlt
    simp only [BoolExpr.eval,
               show i < (b &&& 0x1F#32).toNat from by omega, decide_true, Bool.not_true,
               Bool.false_and]

theorem alu32_bridge_sll (a b : BitVec 32) :
    evalALU32 a b 0x8 = a <<< (b &&& 0x1F#32).toNat := by
  apply bitwise_bridge a b 0x8 _
  intro i hi
  have h := BoolExpr.beqSem_correct _ _ _ (sll_beqSem ⟨i, hi⟩) (aluAssign a b)
  rw [h]
  exact sllRefBit_eval a b i hi

/-! ### SRL (shift right logical, opcode 0x9) -/

private def srlRefBit (i : Nat) : BoolExpr :=
  buildShiftMux 5 (fun s => if i + s < 32 then .var (i + s) else .lit false) 0

private theorem srl_beqSem :
    ∀ i : Fin 32, BoolExpr.beqSem (aluSymResult 0x9 i.val) (srlRefBit i.val) shiftVars = true := by
  native_decide

private theorem srlRefBit_eval (a b : BitVec 32) (i : Nat) (_hi : i < 32) :
    (srlRefBit i).eval (aluAssign a b) =
    (a >>> (b &&& 0x1F#32).toNat).getLsbD i := by
  simp only [srlRefBit]
  rw [buildShiftMux_eval, Nat.zero_add, decodeShift_eq_mask]
  have hs : (b &&& 0x1F#32).toNat < 32 := by rw [and_mask_eq_mod]; omega
  rw [BitVec.getLsbD_ushiftRight]
  split
  · -- i + s < 32: result is a.getLsbD (i + s)
    rename_i hlt
    simp only [BoolExpr.eval, aluAssign, hlt, ite_true]
    congr 1; omega
  · -- i + s ≥ 32: result is false
    rename_i hge
    simp only [BoolExpr.eval, BitVec.getLsbD]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le a.isLt
      (Nat.pow_le_pow_right (by omega) (by omega)))).symm

theorem alu32_bridge_srl (a b : BitVec 32) :
    evalALU32 a b 0x9 = a >>> (b &&& 0x1F#32).toNat := by
  apply bitwise_bridge a b 0x9 _
  intro i hi
  have h := BoolExpr.beqSem_correct _ _ _ (srl_beqSem ⟨i, hi⟩) (aluAssign a b)
  rw [h]
  exact srlRefBit_eval a b i hi

/-! ### SRA (shift right arithmetic, opcode 0xB) -/

private def sraRefBit (i : Nat) : BoolExpr :=
  buildShiftMux 5 (fun s => if i + s < 32 then .var (i + s) else .var 31) 0

private theorem sra_beqSem :
    ∀ i : Fin 32, BoolExpr.beqSem (aluSymResult 0xB i.val) (sraRefBit i.val) shiftVars = true := by
  native_decide

private theorem sraRefBit_eval (a b : BitVec 32) (i : Nat) (hi : i < 32) :
    (sraRefBit i).eval (aluAssign a b) =
    (a.sshiftRight (b &&& 0x1F#32).toNat).getLsbD i := by
  simp only [sraRefBit]
  rw [buildShiftMux_eval, Nat.zero_add, decodeShift_eq_mask]
  have hs : (b &&& 0x1F#32).toNat < 32 := by rw [and_mask_eq_mod]; omega
  rw [BitVec.getLsbD_sshiftRight]
  simp only [show ¬(32 ≤ i) from by omega, decide_false, Bool.not_false, Bool.true_and]
  split
  · -- i + s < 32: result is a.getLsbD (i + s)
    rename_i hlt
    simp only [BoolExpr.eval, aluAssign, hlt, ite_true]
    rw [if_pos (show (b &&& 0x1F#32).toNat + i < 32 from by omega)]
    congr 1; omega
  · -- i + s ≥ 32: result is a.getLsbD 31 (sign extension = msb)
    rename_i hge
    simp only [BoolExpr.eval, aluAssign, show (31 : Nat) < 32 from by omega, ite_true]
    rw [if_neg (show ¬((b &&& 0x1F#32).toNat + i < 32) from by omega)]
    rw [BitVec.msb_eq_getLsbD_last]

theorem alu32_bridge_sra (a b : BitVec 32) :
    evalALU32 a b 0xB = a.sshiftRight (b &&& 0x1F#32).toNat := by
  apply bitwise_bridge a b 0xB _
  intro i hi
  have h := BoolExpr.beqSem_correct _ _ _ (sra_beqSem ⟨i, hi⟩) (aluAssign a b)
  rw [h]
  exact sraRefBit_eval a b i hi

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

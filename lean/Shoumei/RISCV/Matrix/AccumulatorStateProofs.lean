/-
RISCV/Matrix/AccumulatorStateProofs.lean - Proofs for Accumulator State

Key correctness properties for the accumulator behavioral model.
-/

import Shoumei.RISCV.Matrix.AccumulatorState

namespace Shoumei.RISCV.Matrix

/-! ## Init Properties -/

theorem init_all_zeros (r c : Nat) (i : Fin r) (j : Fin c) :
    (AccumulatorState.init r c).data i j = 0 := by
  simp [AccumulatorState.init]

theorem init_tr (r c : Nat) :
    (AccumulatorState.init r c).tr = r := by
  simp [AccumulatorState.init]

theorem init_vl (r c : Nat) :
    (AccumulatorState.init r c).vl = c := by
  simp [AccumulatorState.init]

/-! ## Configuration Properties -/

theorem setTR_bounded (s : AccumulatorState r c) (n : Nat) :
    (s.setTR n).tr ≤ r := by
  simp [AccumulatorState.setTR]
  omega

theorem setVL_bounded (s : AccumulatorState r c) (n : Nat) :
    (s.setVL n).vl ≤ c := by
  simp [AccumulatorState.setVL]
  omega

theorem setTR_preserves_data (s : AccumulatorState r c) (n : Nat) (i : Fin r) (j : Fin c) :
    (s.setTR n).data i j = s.data i j := by
  simp [AccumulatorState.setTR]

theorem setVL_preserves_data (s : AccumulatorState r c) (n : Nat) (i : Fin r) (j : Fin c) :
    (s.setVL n).data i j = s.data i j := by
  simp [AccumulatorState.setVL]

/-! ## Read/Write Properties -/

theorem writeRow_readRow (s : AccumulatorState r c) (row : Fin r) (vals : Fin c → UInt32) (j : Fin c) :
    (s.writeRow row vals).data row j = vals j := by
  simp [AccumulatorState.writeRow]

theorem writeRow_other_row (s : AccumulatorState r c) (row : Fin r) (vals : Fin c → UInt32)
    (i : Fin r) (j : Fin c) (h : i ≠ row) :
    (s.writeRow row vals).data i j = s.data i j := by
  simp [AccumulatorState.writeRow, h]

theorem writeCol_readCol (s : AccumulatorState r c) (col : Fin c) (vals : Fin r → UInt32) (i : Fin r) :
    (s.writeCol col vals).data i col = vals i := by
  simp [AccumulatorState.writeCol]

theorem writeCol_other_col (s : AccumulatorState r c) (col : Fin c) (vals : Fin r → UInt32)
    (i : Fin r) (j : Fin c) (h : j ≠ col) :
    (s.writeCol col vals).data i j = s.data i j := by
  simp [AccumulatorState.writeCol, h]

/-! ## Destructive Read Properties -/

theorem readRowDestructive_returns_data (s : AccumulatorState r c) (row : Fin r) (j : Fin c) :
    (s.readRowDestructive row).2 j = s.data row j := by
  simp [AccumulatorState.readRowDestructive]

theorem readRowDestructive_zeros_row (s : AccumulatorState r c) (row : Fin r) (j : Fin c) :
    (s.readRowDestructive row).1.data row j = 0 := by
  simp [AccumulatorState.readRowDestructive]

theorem readRowDestructive_preserves_other (s : AccumulatorState r c) (row : Fin r)
    (i : Fin r) (j : Fin c) (h : i ≠ row) :
    (s.readRowDestructive row).1.data i j = s.data i j := by
  simp [AccumulatorState.readRowDestructive, h]

theorem readColDestructive_returns_data (s : AccumulatorState r c) (col : Fin c) (i : Fin r) :
    (s.readColDestructive col).2 i = s.data i col := by
  simp [AccumulatorState.readColDestructive]

theorem readColDestructive_zeros_col (s : AccumulatorState r c) (col : Fin c) (i : Fin r) :
    (s.readColDestructive col).1.data i col = 0 := by
  simp [AccumulatorState.readColDestructive]

/-! ## Raw Read/Write Properties -/

theorem rawReadRow_eq_data (s : AccumulatorState r c) (row : Fin r) (j : Fin c) :
    s.rawReadRow row j = s.data row j := by
  simp [AccumulatorState.rawReadRow]

theorem rawWriteRow_same_as_writeRow (s : AccumulatorState r c) (row : Fin r) (vals : Fin c → UInt32) :
    (s.rawWriteRow row vals).data = (s.writeRow row vals).data := by
  ext i j
  simp [AccumulatorState.rawWriteRow, AccumulatorState.writeRow]

/-! ## Outer Product Properties -/

theorem outerProduct_overwrites (s : AccumulatorState r c)
    (vs1 : Fin r → UInt32) (vs2 : Fin c → UInt32) (sew : SEW)
    (i : Fin r) (j : Fin c) :
    (s.outerProduct vs1 vs2 sew).data i j =
      ((AccumulatorState.init r c).outerProduct vs1 vs2 sew).data i j := by
  simp [AccumulatorState.outerProduct, AccumulatorState.init]

end Shoumei.RISCV.Matrix

/-
RISCV/Matrix/AccumulatorState.lean - Accumulator State for VME

The accumulator array holds intermediate matrix multiply-accumulate results.
Used by the IME (Integrated Matrix Extension) outer-product variant.

Design:
- 2D array of 32-bit accumulators: maxRows × maxCols
- Configurable active dimensions via TR (tile rows) and VL (vector length / tile cols)
- Supports int8→int32 (4x widening) and int16→int32 (2x widening) outer products
- Destructive read for rows/columns (shifts data out)
- Raw read/write for context switch save/restore
-/

import Shoumei.DSL

namespace Shoumei.RISCV.Matrix

/-! ## SEW (Selected Element Width) -/

/-- Element width for VME operations -/
inductive SEW where
  | Int8  : SEW   -- 8-bit signed integer elements
  | Int16 : SEW   -- 16-bit signed integer elements
  deriving Repr, BEq, DecidableEq

/-- Element width in bits -/
def SEW.bits : SEW → Nat
  | .Int8  => 8
  | .Int16 => 16

/-! ## Accumulator State -/

/-- Accumulator state for the matrix execution unit.

    Parameterized by maximum tile dimensions. For VLEN=128:
    - int8:  maxRows=16, maxCols=16 (VLEN/8 × VLEN/8)
    - int16: maxRows=8,  maxCols=8  (VLEN/16 × VLEN/16)

    We use a single array sized for the largest configuration (int8). -/
structure AccumulatorState (maxRows maxCols : Nat) where
  /-- 2D accumulator data -/
  data : Fin maxRows → Fin maxCols → UInt32
  /-- Configured tile rows (≤ maxRows), set by MSETRLI -/
  tr : Nat
  /-- Configured tile columns (≤ maxCols), set by MSETCLI -/
  vl : Nat

/-- Initial state: all zeros, max dimensions -/
def AccumulatorState.init (maxRows maxCols : Nat) : AccumulatorState maxRows maxCols :=
  { data := fun _ _ => 0
    tr := maxRows
    vl := maxCols }

/-- Set tile row dimension -/
def AccumulatorState.setTR (s : AccumulatorState r c) (newTR : Nat) : AccumulatorState r c :=
  { s with tr := min newTR r }

/-- Set tile column dimension -/
def AccumulatorState.setVL (s : AccumulatorState r c) (newVL : Nat) : AccumulatorState r c :=
  { s with vl := min newVL c }

/-! ## Core Operations -/

/-- Sign-extend an n-bit value (stored in UInt32) to Int32 (as Int) -/
private def signExtendToInt (val : UInt32) (width : Nat) : Int :=
  let mask := (1 <<< width) - 1
  let truncated := val.toNat &&& mask
  let signBit := 1 <<< (width - 1)
  if truncated &&& signBit != 0 then
    (truncated : Int) - (1 <<< width : Int)
  else
    truncated

/-- Truncate Int to UInt32 (mod 2^32) -/
private def truncateToU32 (v : Int) : UInt32 :=
  ((v % (2^32 : Int) + (2^32 : Int)).toNat % (2^32)).toUInt32

/-- Outer product: acc[i][j] = sign_ext(vs1[i]) * sign_ext(vs2[j])

    Overwrites the accumulator (non-accumulating version).
    vs1 and vs2 are flattened vectors of elements packed into UInt32 values. -/
def AccumulatorState.outerProduct
    (s : AccumulatorState r c)
    (vs1 : Fin r → UInt32) (vs2 : Fin c → UInt32)
    (sew : SEW) : AccumulatorState r c :=
  let w := sew.bits
  { s with data := fun i j =>
      let ai := signExtendToInt (vs1 i) w
      let bj := signExtendToInt (vs2 j) w
      truncateToU32 (ai * bj) }

/-- Outer product accumulate: acc[i][j] += sign_ext(vs1[i]) * sign_ext(vs2[j])

    Adds the outer product to the existing accumulator contents. -/
def AccumulatorState.outerProductAccum
    (s : AccumulatorState r c)
    (vs1 : Fin r → UInt32) (vs2 : Fin c → UInt32)
    (sew : SEW) : AccumulatorState r c :=
  let w := sew.bits
  { s with data := fun i j =>
      let ai := signExtendToInt (vs1 i) w
      let bj := signExtendToInt (vs2 j) w
      let product := truncateToU32 (ai * bj)
      s.data i j + product }

/-- Vector-scalar MAC: acc[i][j] += sign_ext(vs1[i]) * sign_ext(scalar)

    Broadcasts scalar across all columns. -/
def AccumulatorState.vectorScalarMAC
    (s : AccumulatorState r c)
    (vs1 : Fin r → UInt32) (scalar : UInt32)
    (sew : SEW) : AccumulatorState r c :=
  let w := sew.bits
  let bs := signExtendToInt scalar w
  { s with data := fun i j =>
      let ai := signExtendToInt (vs1 i) w
      let product := truncateToU32 (ai * bs)
      s.data i j + product }

/-- Read accumulator row (destructive): returns row data, zeros the row.

    Used by VRACCR instruction. Returns a vector of maxCols UInt32 values. -/
def AccumulatorState.readRowDestructive
    (s : AccumulatorState r c) (row : Fin r)
    : AccumulatorState r c × (Fin c → UInt32) :=
  let rowData := s.data row
  let newState := { s with data := fun i j =>
    if i == row then 0 else s.data i j }
  (newState, rowData)

/-- Read accumulator column (destructive): returns column data, zeros the column.

    Used by VRACCC instruction. Returns a vector of maxRows UInt32 values. -/
def AccumulatorState.readColDestructive
    (s : AccumulatorState r c) (col : Fin c)
    : AccumulatorState r c × (Fin r → UInt32) :=
  let colData := fun i => s.data i col
  let newState := { s with data := fun i j =>
    if j == col then 0 else s.data i j }
  (newState, colData)

/-- Write a row into the accumulator.

    Used by VWACCR instruction. -/
def AccumulatorState.writeRow
    (s : AccumulatorState r c) (row : Fin r) (vals : Fin c → UInt32)
    : AccumulatorState r c :=
  { s with data := fun i j =>
    if i == row then vals j else s.data i j }

/-- Write a column into the accumulator.

    Used by VWACCC instruction. -/
def AccumulatorState.writeCol
    (s : AccumulatorState r c) (col : Fin c) (vals : Fin r → UInt32)
    : AccumulatorState r c :=
  { s with data := fun i j =>
    if j == col then vals i else s.data i j }

/-- Raw read row (non-destructive, for context switch save).

    Used by VRRACCR instruction. -/
def AccumulatorState.rawReadRow
    (s : AccumulatorState r c) (row : Fin r) : Fin c → UInt32 :=
  s.data row

/-- Raw write row (for context switch restore).

    Used by VRWACCR instruction. -/
def AccumulatorState.rawWriteRow
    (s : AccumulatorState r c) (row : Fin r) (vals : Fin c → UInt32)
    : AccumulatorState r c :=
  { s with data := fun i j =>
    if i == row then vals j else s.data i j }

end Shoumei.RISCV.Matrix

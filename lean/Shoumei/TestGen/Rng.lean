/-
  TestGen/Rng.lean - Seedable random computation for the test generator.

  Everything the generator draws threads one explicit `StdGen`, so a printed
  seed reproduces a run exactly.  `split` hands out independent streams, which
  is how adjacent programs in a batch are decorrelated.
-/

import Init.Data.Random

namespace Shoumei.TestGen

/-- Deterministic random computation over an explicit generator. -/
abbrev RandM := StateM StdGen

namespace RandM

/-- Uniform in `[lo, hi]`, inclusive. -/
def pick (lo hi : Nat) : RandM Nat := do
  let g ← get
  let (v, g') := randNat g lo hi
  set g'
  return v

/-- Uniform over `0 .. n-1`.  `n = 0` yields 0. -/
def pickNat (n : Nat) : RandM Nat :=
  if n == 0 then return 0 else pick 0 (n - 1)

/-- One element of a non-empty list. -/
def pickFrom {α : Type} [Inhabited α] (xs : List α) : RandM α := do
  let i ← pickNat xs.length
  return xs.getD i default

/-- One bit. -/
def pickBit : RandM Nat := pick 0 1

/-- A fresh, independent generator; the current stream moves on. -/
def split : RandM StdGen := do
  let g ← get
  let (a, b) := RandomGen.split g
  set a
  return b

/-- Uniform permutation. -/
def shuffle {α : Type} [Inhabited α] (xs : List α) : RandM (List α) := do
  let mut pool := xs
  let mut acc : List α := []
  for _ in List.range xs.length do
    if pool.isEmpty then
      break
    let i ← pickNat pool.length
    acc := acc ++ [pool.getD i default]
    pool := pool.eraseIdx i
  return acc

end RandM

/-- Run a computation from a seed. -/
def runRand (g : StdGen) (m : RandM α) : α := (m.run g).1

/-- Run a computation from a numeric seed. -/
def runSeed (seed : Nat) (m : RandM α) : α := runRand (mkStdGen seed) m

end Shoumei.TestGen

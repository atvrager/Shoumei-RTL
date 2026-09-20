/-
RISCV/Memory/Cache/PLRU.lean - Tree-PLRU replacement policy

A cache with more than two ways needs a replacement policy; the levels used to
carry a single LRU bit, which is 2-way only.  Tree-PLRU is the cheap standard
choice, and it degenerates exactly to that single bit at 2 ways, so one block
serves every geometry.

Layout: `ways - 1` bits in level order; node `i` owns children `2i+1` (left)
and `2i+2` (right).  A bit points at the subtree to leave first.

    ways = 4 (3 bits)                  ways = 2 (1 bit)
         b0                                b0
        /  \                              /  \
      b1    b2                         w0    w1
      / \   / \
    w0  w1 w2  w3

  victim: start at the root, follow the bits down to a leaf.
  update: on touching way `w`, every bit on the path from its leaf to the root
          is set to point away from `w`, so `w` becomes most-recently used.

`ways` must be a power of two (the levels use 1, 2, 4, 8).  The structural
circuit exposes the victim as a one-hot way select, so a level feeds it
straight into its way muxes with no encoder in between.
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.Decoder

namespace Shoumei.RISCV.Memory.Cache

open Shoumei
open Shoumei.Circuits.Combinational

/-! ## Behavioral Model -/

/-- Tree-PLRU state: `ways - 1` level-order bits (root first). -/
structure PLRUState (ways : Nat) where
  bits : List Bool
  deriving Repr

/-- Tree depth (levels below the root). -/
def PLRUState.depth (ways : Nat) : Nat := if ways ≤ 1 then 0 else Nat.log2 ways

/-- Initial state: every bit 0, so the victim is the leftmost way. -/
def PLRUState.init (ways : Nat) : PLRUState ways :=
  { bits := List.replicate (ways - 1) false }

/-- Victim way: follow the bits from the root to a leaf, then map the leaf back
    to a way index (leaves are the last `ways` nodes in level order). -/
def PLRUState.victim (s : PLRUState ways) : Nat :=
  let leaf := (List.range (PLRUState.depth ways)).foldl
    (fun node _ => if s.bits.getD node false then 2 * node + 2 else 2 * node + 1) 0
  leaf - (ways - 1)

/-- Mark way `w` most-recently used: set each bit on the path from its leaf to
    the root to point away from the path taken. -/
def PLRUState.update (s : PLRUState ways) (w : Nat) : PLRUState ways :=
  let rec go (node : Nat) (bits : List Bool) (fuel : Nat) : List Bool :=
    match fuel with
    | 0 => bits
    | fuel + 1 =>
      if node == 0 then bits
      else
        let parent := (node - 1) / 2
        let cameFromRight := node % 2 == 0
        go parent (bits.set parent (!cameFromRight)) fuel
  { bits := go (ways - 1 + w) s.bits (PLRUState.depth ways) }

/-! ## Structural Circuit -/

/-- OR-reduce `ws` into `out`, generating intermediate wires named `pfx_oN`. -/
private def orReduce (zero : Wire) (pfx : String) (ws : List Wire) (out : Wire) : List Gate :=
  match ws with
  | [] => [Gate.mkBUF zero out]
  | [w] => [Gate.mkBUF w out]
  | w :: rest =>
    let rec go (acc : List Gate) (prev : Wire) (rem : List Wire) (n : Nat) : List Gate :=
      match rem with
      | [] => acc ++ [Gate.mkBUF prev out]
      | w' :: tl =>
        let o := Wire.mk s!"{pfx}_o{n}"
        go (acc ++ [Gate.mkOR prev w' o]) o tl (n + 1)
    go [] w rest 1

/-- Leaves under the *right* child of node `i` in a full binary tree of `ways`
    leaves: level `lv`, `ways / 2^(lv+1)` leaves per child subtree. -/
private def rightLeaves (ways i : Nat) : List Nat :=
  let lv := Nat.log2 (i + 1)
  let span := ways / 2 ^ (lv + 1)
  let first := (i - (2 ^ lv - 1)) * 2 * span
  (List.range span).map (fun k => first + span + k)

/-- Tree-PLRU circuit.

    Ports:
    - inputs : clock, reset, zero, one, upd_en, upd_way_oh[ways-1:0]
    - outputs: victim_oh[ways-1:0]

    Both way selects are one-hot, which is what the caches already have (way
    hit vectors, victim selects), so no encoder sits in between.  The victim is
    available combinationally; `upd_en` with `upd_way_oh` marks a way
    most-recently used at the clock edge. -/
def mkPLRU (ways : Nat) : Circuit :=
  let depth := PLRUState.depth ways
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"
  let upd_en := Wire.mk "upd_en"
  let upd_way_oh := (List.range ways).map fun i => Wire.mk s!"upd_way_oh_{i}"
  let victim_oh := (List.range ways).map fun i => Wire.mk s!"victim_oh_{i}"

  -- Tree bits: one DFF per internal node.
  let bit_d := (List.range (ways - 1)).map fun i => Wire.mk s!"bit_d_{i}"
  let bit_q := (List.range (ways - 1)).map fun i => Wire.mk s!"bit_q_{i}"
  let bit_gates := (List.range (ways - 1)).map fun i =>
    Gate.mkDFF bit_d[i]! clock reset bit_q[i]!

  -- The updated way *is* the one-hot leaf select (gated by the update enable).
  let leaf_oh := (List.range ways).map fun i => Wire.mk s!"leaf_oh_{i}"
  let leaf_gates := (List.range ways).map fun w =>
    Gate.mkAND upd_way_oh[w]! upd_en leaf_oh[w]!

  -- is_right[i] = the updated way is in node i's right subtree.
  let in_right := (List.range (ways - 1)).map fun i => Wire.mk s!"in_right_{i}"
  let ascend_gates : List Gate :=
    ((List.range (ways - 1)).map (fun i =>
      orReduce zero s!"in_right_t_{i}"
        ((rightLeaves ways i).map (fun w => leaf_oh[w]!)) in_right[i]!))
    |>.flatten

  -- bit_d = upd_en ? in_right : hold
  let bit_next_gates := (List.range (ways - 1)).map fun i =>
    Gate.mkMUX bit_q[i]! in_right[i]! upd_en bit_d[i]!

  -- Victim: one-hot descent.  `sel` is one-hot over all 2*ways-1 nodes.
  let sel := (List.range (2 * ways - 1)).map fun i => Wire.mk s!"sel_{i}"
  let not_bit := (List.range (ways - 1)).map fun i => Wire.mk s!"nbit_{i}"
  let levelGates := (List.range depth).map (fun d =>
    let first := 2 ^ d - 1
    let count := 2 ^ d
    (List.range count).map (fun k =>
      let node := first + k
      [Gate.mkAND sel[node]! not_bit[node]! sel[2 * node + 1]!,
       Gate.mkAND sel[node]! bit_q[node]! sel[2 * node + 2]!]))
  let descend_gates : List Gate :=
    [Gate.mkBUF one sel[0]!] ++
    (List.range (ways - 1)).map (fun i => Gate.mkNOT bit_q[i]! not_bit[i]!) ++
    List.flatten (List.flatten levelGates)
  -- victim_oh[w] = sel of the leaf node for way w
  let victim_gates := (List.range ways).map fun w =>
    Gate.mkBUF sel[ways - 1 + w]! victim_oh[w]!

  { name := s!"PLRU{ways}"
    inputs := [clock, reset, zero, one, upd_en] ++ upd_way_oh
    outputs := victim_oh
    gates := bit_gates ++ leaf_gates ++ ascend_gates ++ bit_next_gates ++
             descend_gates ++ victim_gates
    instances := []
    signalGroups := [
      { name := "upd_way_oh", width := ways, wires := upd_way_oh },
      { name := "victim_oh", width := ways, wires := victim_oh }
    ]
  }

end Shoumei.RISCV.Memory.Cache

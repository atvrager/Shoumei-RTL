# Proof Strategy: QueueN Multi-Entry FIFO Invariants

This document details the first-principles verification architecture for multi-entry circular queues (`QueueN`) in Shoumei RTL.

---

## 1. The Multi-Entry Problem

In `Queue1`, capacity is 1, and the valid bit doubles as the occupancy counter.
In `QueueN` ($N \ge 2$), capacity expands to arbitrary depth $N$, introducing:
1. **Circular Addressing**: Read (`head`) and Write (`tail`) pointers advance modulo $N$.
2. **Multi-Bit Occupancy**: A counter tracks $0 \le \text{count} \le N$.
3. **Decoupled Concurrency**: A queue with $0 < \text{count} < N$ can simultaneously accept an enqueue and emit a dequeue in the same clock cycle.

---

## 2. Invariant Hierarchy

Correctness is established in three complementary layers:

```
┌────────────────────────────────────────────────────────┐
│  Layer 1: Symbolic Trace Induction (QueueState / CB)   │
│  - Capacity bound: count ≤ N under any operation trace │
│  - Dequeue empty safety: pop(empty) = none             │
│  - Enqueue full safety: push(full) = no-op             │
└──────────────────────────┬─────────────────────────────┘
                           │ Discharged via symbolic induction
┌──────────────────────────▼─────────────────────────────┐
│  Layer 2: Universal Control Equations (Gate Logic)     │
│  - Empty Safety: empty = 1 ⟹ deq_valid = 0, deq_fire=0 │
│  - Full Safety:  full = 1  ⟹ enq_ready = 0, enq_fire=0 │
│  - Concurrency:  !empty ∧ !full ⟹ enq_fire ∧ deq_fire  │
└──────────────────────────┬─────────────────────────────┘
                           │ Discharged via boolean simplification
┌──────────────────────────▼─────────────────────────────┐
│  Layer 3: Operational Gate Bridge (mkQueueNStructural) │
│  - Bit-tree empty detector: count == 0                 │
│  - Bit-tree full detector: count == N                  │
│  - Machine-checked on synthesized netlists             │
└────────────────────────────────────────────────────────┘
```

---

## 3. Layer 1: Inductive Capacity Invariant

In [`QueueProofs.lean`](../../lean/Shoumei/Circuits/Sequential/QueueProofs.lean), we prove that an initialized queue never exceeds its capacity under an arbitrary trace of operations:

```lean
inductive QueueOp (α : Type) where
  | enq (val : α)
  | deq

def applyTrace (ops : List (QueueOp α)) (q : QueueState α) : QueueState α :=
  ops.foldl (fun acc op => applyOp op acc) q

theorem never_exceeds_capacity (ops : List (QueueOp α)) (cap : Nat) :
    (applyTrace ops (QueueState.empty cap)).count ≤ cap
```

### Inductive Argument
1. **Base Case**: $\text{count}(\text{empty}) = 0 \le \text{capacity}$.
2. **Step (`enqueue`)**:
   - If $\text{count} \ge \text{capacity}$, $\text{isFull} = \text{true} \implies \text{enqueue}$ is a no-op $\implies \text{count}' = \text{count} \le \text{capacity}$.
   - If $\text{count} < \text{capacity}$, $\text{count}' = \text{count} + 1 \le \text{capacity}$.
3. **Step (`dequeue`)**:
   - If empty, $\text{dequeue}$ returns unchanged state.
   - If non-empty, $\text{count}' = \text{count} - 1 < \text{count} \le \text{capacity}$.

Because this argument is purely symbolic, Lean verifies it in $<1\text{ ms}$ for arbitrary $N$, data types $\alpha$, and trace lengths.

---

## 4. Layer 2: Universal Gate Control Equations

The interface handshaking gates in [`QueueN.lean`](../../lean/Shoumei/Circuits/Sequential/QueueN.lean) are:
$$\text{enq\_ready} = \neg\text{full}$$
$$\text{deq\_valid} = \neg\text{empty}$$
$$\text{enq\_fire} = \text{enq\_valid} \land \text{enq\_ready}$$
$$\text{deq\_fire} = \text{deq\_ready} \land \text{deq\_valid}$$

In [`QueueNTemporalProofs.lean`](../../lean/Shoumei/Circuits/Sequential/QueueNTemporalProofs.lean):

### Universal Empty Safety
$$\text{empty} = 1 \implies \text{deq\_valid} = 0 \implies \text{deq\_fire} = 0$$
When the queue is empty, a dequeue transfer cannot occur, protecting the memory array and pointers from underflow.

### Universal Full Safety
$$\text{full} = 1 \implies \text{enq\_ready} = 0 \implies \text{enq\_fire} = 0$$
When the queue is full, an enqueue transfer cannot occur, protecting stored items from overwrite.

### Universal Concurrent Transfer
$$\neg\text{empty} \land \neg\text{full} \implies \text{enq\_ready} = 1 \land \text{deq\_valid} = 1$$
When partially occupied, the queue simultaneously absorbs a new item at `tail` and delivers an item from `head`.

---

## 5. Performance Engineering: Eliminating Proof Stalls

Evaluating whole netlists with `evalCircuit` under `native_decide` causes severe stalls when:
1. `evalCircuit` accumulates $G$ gate updates as nested function closures $\mathcal{O}(G^2)$ in Lean's evaluator.
2. Dynamic string interpolation (`s!"count_{i}"`) inside closures triggers thousands of heap allocations per theorem.

### Solutions Applied:
- **Symbolic Induction First**: Proofs on the abstract transition system are instant and hold for all $N$.
- **Modular Isolation**: Prove the control equations in isolation without pulling in large RAM arrays.
- **Static LUT Environments**: Fast pattern-matched environments replace dynamic string searches for netlist evaluation.

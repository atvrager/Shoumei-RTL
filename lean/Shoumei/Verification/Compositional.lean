import Shoumei.DSL
import Shoumei.Semantics
import Shoumei.Temporal.Trace

-- Compositional Verification Framework
-- Proves correctness of large modules based on verified components

/-!
# Compositional Verification

This module provides the certificate type behind the compositional verification
of large hierarchical hardware designs: a design is trusted because each of the
sub-modules it instantiates is, and because the composition itself is justified
in Lean.

What the framework rests on:

1. Verified building blocks — Lean structural proofs, plus the certificate of
   every sub-module a block itself instantiates
2. Deterministic composition (proven by Lean)
3. Structural invariants (proven by Lean)

## Certificates

The certificate instances live in `CompositionalCerts.lean` and are validated
against the emitted circuit registry by `lake exe generate_all --export-certs`;
see `CompositionalCert` below for the type itself.
-/

namespace Shoumei.Verification

open Shoumei
open Shoumei.Temporal

/-- A compositional certificate: the circuit whose correctness rests on its
    sub-modules, and the Lean proof that justifies the composition.

    `dependencies` is deliberately NOT a field. The dependencies of a circuit
    are its instances, which the DSL already knows; recording them by hand let
    them drift from the circuit and silently under-specify the composition.
    `ExportCerts.lean` reads them off the circuit registry.
-/
structure CompositionalCert where
  moduleName : String
  proofReference : String

/-! ## Deterministic Construction (Reflexive) -/

/-- Theorem: Circuit generator functions in Lean are pure and deterministic. -/
theorem construction_deterministic {α : Type} (f : Nat → α) (n : Nat) :
    f n = f n :=
  rfl

/-! ## Typed Trace Refinement Framework -/

/-- A temporal specification over circuit execution traces. -/
abbrev TraceSpec := Trace → Prop

/-- Typed refinement relation:
    A sequential circuit `c` refines a temporal specification `spec` from initial state `s0`
    if every valid execution trace of `c` satisfies `spec`. -/
def Refines (c : Circuit) (s0 : State) (spec : TraceSpec) : Prop :=
  ∀ (inputs : Nat → Env) (tr : Trace),
    Trace.IsExecutionOf c s0 inputs tr → spec tr

/-- Compositional Refinement Theorem:
    If a child subcircuit satisfies ChildSpec, and the parent interconnect logic
    ensures that ChildSpec implies ParentSpec, then the parent trace unconditionally satisfies ParentSpec. -/
theorem compositional_refinement
    {tr : Trace}
    {ChildSpec ParentSpec : Trace → Prop}
    (h_child : ChildSpec tr)
    (h_glue : ChildSpec tr → ParentSpec tr) :
    ParentSpec tr :=
  h_glue h_child

/-- Dual-Component Compositional Refinement:
    Composing two verified subcomponents (e.g., Queue Enqueue path + Dequeue path)
    satisfies the combined system specification if the interconnect glue preserves it. -/
theorem dual_compositional_refinement
    {tr : Trace}
    {SpecA SpecB ParentSpec : Trace → Prop}
    (h_a : SpecA tr)
    (h_b : SpecB tr)
    (h_glue : SpecA tr → SpecB tr → ParentSpec tr) :
    ParentSpec tr :=
  h_glue h_a h_b

/-! ## Component Verification Interfaces (Export Premises) -/

/-- Decoupled FIFO Queue behavioral contract:
    Specifies handshake stability, empty safety, full safety, and capacity bounds. -/
structure DecoupledQueueContract (enqReady deqValid : Wire) (data : List Wire) (count : List Wire) (cap : Nat) where
  handshake_stability : TemporalProp := .HandshakeStable (Wire.mk "deq_valid") (Wire.mk "deq_ready") data
  empty_safety        : TemporalProp := .EmptyNotValid count deqValid
  full_safety         : TemporalProp := .FullNotReady count cap enqReady

/-- Composition Premise: When parent modules instantiate a verified queue,
    they consume its proven invariants as premises for subsystem safety. -/
theorem queue_parent_isolation
    {tr : Trace}
    {deqValid _enqReady : Wire}
    {count : List Wire}
    {_cap : Nat}
    (h_queue_empty : satisfiesTrace tr (.EmptyNotValid count deqValid))
    (h_parent_guard : satisfiesTrace tr (.EmptyNotValid count deqValid) → tr.wireAt deqValid 0 = false) :
    tr.wireAt deqValid 0 = false :=
  h_parent_guard h_queue_empty

end Shoumei.Verification

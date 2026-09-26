import ShoumeiSec.Bridge.Spec
import ShoumeiSec.Bridge.Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.BridgeQueue1

set_option linter.unusedVariables false

def absState (s : ShoumeiSec.Bridge.Impl.State) : ShoumeiSec.Bridge.Spec.State where
  v_auto_ff_cc_337_slice_34 := s.v_auto_ff_cc_337_slice_15
  v_procdff_30 := s.v_procdff_14

def absInputs (i : ShoumeiSec.Bridge.Impl.Inputs) : ShoumeiSec.Bridge.Spec.Inputs where
  enq_data := i.enq_data
  enq_valid := i.enq_valid
  deq_ready := i.deq_ready
  clock := i.clock
  reset := i.reset

/-- Sequential Equivalence: Shoumei-emitted Queue1_8 netlist step function
    refines human-written expressive Queue1_spec under state abstraction. -/
theorem queue1_sec (i : ShoumeiSec.Bridge.Impl.Inputs) (s : ShoumeiSec.Bridge.Impl.State) :
    let imp := ShoumeiSec.Bridge.Impl.step i s
    let spc := ShoumeiSec.Bridge.Spec.step (absInputs i) (absState s)
    imp.1.enq_ready = spc.1.enq_ready ∧
    imp.1.valid = spc.1.valid ∧
    imp.1.data_reg = spc.1.data_reg ∧
    absState imp.2 = spc.2 := by
  obtain ⟨enq_d, enq_v, deq_r, clk, rst⟩ := i
  obtain ⟨d, v⟩ := s
  simp only [ShoumeiSec.Bridge.Impl.step, ShoumeiSec.Bridge.Spec.step, absState, absInputs, ShoumeiSec.Bridge.Spec.State.mk.injEq]
  bv_decide

/-- Lifted SVA: Ready-Valid protocol contract (enq_ready = !valid). -/
theorem impl_enq_ready_contract (i : ShoumeiSec.Bridge.Impl.Inputs) (s : ShoumeiSec.Bridge.Impl.State) :
    (ShoumeiSec.Bridge.Impl.step i s).1.enq_ready = ~~~(ShoumeiSec.Bridge.Impl.step i s).1.valid := by
  obtain ⟨enq_d, enq_v, deq_r, clk, rst⟩ := i
  obtain ⟨d, v⟩ := s
  simp only [ShoumeiSec.Bridge.Impl.step]

/-- Lifted SVA: Handshake stability (occupied and unacknowledged holds data). -/
theorem impl_handshake_stable (s₀ : ShoumeiSec.Bridge.Impl.State) (i₀ i₁ : ShoumeiSec.Bridge.Impl.Inputs)
    (h_rst0 : i₀.reset = 0#1) (h_rst1 : i₁.reset = 0#1)
    (h_valid : (ShoumeiSec.Bridge.Impl.step i₀ s₀).1.valid = 1#1)
    (h_not_rdy : i₀.deq_ready = 0#1) :
    let s₁ := (ShoumeiSec.Bridge.Impl.step i₀ s₀).2
    let o₁ := (ShoumeiSec.Bridge.Impl.step i₁ s₁).1
    o₁.valid = 1#1 ∧ o₁.data_reg = (ShoumeiSec.Bridge.Impl.step i₀ s₀).1.data_reg := by
  obtain ⟨ed0, ev0, dr0, c0, r0⟩ := i₀
  obtain ⟨ed1, ev1, dr1, c1, r1⟩ := i₁
  obtain ⟨d0, v0⟩ := s₀
  simp only [ShoumeiSec.Bridge.Impl.step] at *
  bv_decide

/-- Lifted SVA: Push effect (enqueue into empty queue buffers the data). -/
theorem impl_push_effect (s₀ : ShoumeiSec.Bridge.Impl.State) (i₀ i₁ : ShoumeiSec.Bridge.Impl.Inputs)
    (h_rst0 : i₀.reset = 0#1) (h_rst1 : i₁.reset = 0#1)
    (h_empty : (ShoumeiSec.Bridge.Impl.step i₀ s₀).1.valid = 0#1)
    (h_push : i₀.enq_valid = 1#1) :
    let s₁ := (ShoumeiSec.Bridge.Impl.step i₀ s₀).2
    let o₁ := (ShoumeiSec.Bridge.Impl.step i₁ s₁).1
    o₁.valid = 1#1 ∧ o₁.data_reg = i₀.enq_data := by
  obtain ⟨ed0, ev0, dr0, c0, r0⟩ := i₀
  obtain ⟨ed1, ev1, dr1, c1, r1⟩ := i₁
  obtain ⟨d0, v0⟩ := s₀
  simp only [ShoumeiSec.Bridge.Impl.step] at *
  bv_decide

end ShoumeiSec.BridgeQueue1

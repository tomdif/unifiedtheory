/- The physical ordered factor E C^(-1/2), E=exp(L/2), is densely
defined and closable. Reversed-order adjoint tests are supplied by the
actual shifted trials and their proved inverse-clock energy. -/
import UnifiedTheory.Audit.KFCausalOrderedOperatorComposition
import UnifiedTheory.Audit.KFCausalShiftedInverseClockAction
import UnifiedTheory.Audit.KFCausalClockDressedDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalOrderedExponentialClosure
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalDampedProductDomain
open UnifiedTheory.Audit.KFCausalCoupledTrialDensity
open UnifiedTheory.Audit.KFCausalClockDressedProducts
open UnifiedTheory.Audit.KFCausalClockDressedActions
open UnifiedTheory.Audit.KFCausalClockDressedDomain
open UnifiedTheory.Audit.KFCausalPhysicalClockPowers
open UnifiedTheory.Audit.KFCausalLongitudinalExponential
open UnifiedTheory.Audit.KFCausalShiftedProductAction
open UnifiedTheory.Audit.KFCausalShiftedInverseClockAction
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

def orderedExponential (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  composition (longitudinalExponential ε hε hbar (1/2)) (clockPower (-(1/2)))

def reversedExponential (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  composition (clockPower (-(1/2))) (longitudinalExponential ε hε hbar (1/2))

theorem trial_mem_reversedExponential (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| ≤ Real.pi*ε) (v : ℝ × SchwartzMap TailSpace ℂ) :
    trialFamily ε a hε ha v ∈ (reversedExponential ε hε hbar).domain := by
  apply (composition_domain _ _ _).mpr
  exact ⟨shiftedState ε a v.1 (-(1/2)*hbar) hε ha (half_shift_bound ε hbar hh) v.2 (v.2.memLp 2 volume),
    trial_exponential_graph ε a v.1 hbar (1/2) hε ha (half_shift_bound ε hbar hh) v.2 v.2.integrable (v.2.memLp 2 volume),
    shifted_inverse_clock_domain ε a v.1 (-(1/2)*hbar) hε ha (half_shift_bound ε hbar hh) v.2 (v.2.memLp 2 volume)⟩

theorem reversedExponential_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε) :
    Dense ((reversedExponential ε hε hbar).domain : Set Hilbert) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hs : Submodule.span ℂ (Set.range (trialFamily ε 1 hε zero_lt_one)) ≤
      (reversedExponential ε hε hbar).domain := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,rfl⟩
    exact trial_mem_reversedExponential ε 1 hbar hε zero_lt_one hh v
  have hc := Submodule.topologicalClosure_mono hs
  rw [dense_trial_span ε 1 hε zero_lt_one] at hc
  exact top_unique hc

theorem dressed_ordered_graph (ε a p hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| ≤ Real.pi*ε) (ψ : SchwartzMap TailSpace ℂ) :
    (dressedState ε a p hε ha ψ (ψ.memLp 2 volume),
      shiftedState ε a p (-(1/2)*hbar) hε ha (half_shift_bound ε hbar hh) ψ (ψ.memLp 2 volume)) ∈
      (orderedExponential ε hε hbar).graph := by
  apply (composition_graph _ _ _ _).mpr
  exact ⟨trialState ε a p hε ha ψ (ψ.memLp 2 volume),
    dressed_inverse_graph ε a p hε ha ψ (ψ.memLp 2 volume),
    trial_exponential_graph ε a p hbar (1/2) hε ha (half_shift_bound ε hbar hh) ψ ψ.integrable (ψ.memLp 2 volume)⟩

theorem orderedExponential_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε) :
    Dense ((orderedExponential ε hε hbar).domain : Set Hilbert) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hs : Submodule.span ℂ (Set.range (dressedFamily ε 1 hε zero_lt_one)) ≤
      (orderedExponential ε hε hbar).domain := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,rfl⟩
    exact LinearPMap.mem_domain_of_mem_graph (dressed_ordered_graph ε 1 v.1 hbar hε zero_lt_one hh v.2)
  have hc := Submodule.topologicalClosure_mono hs
  rw [dense_dressed_span ε 1 hε zero_lt_one] at hc
  exact top_unique hc

theorem orderedExponential_closable (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε) :
    (orderedExponential ε hε hbar).IsClosable :=
  composition_closable _ _ (longitudinal_exponential_selfAdjoint ε hε hbar (1/2))
    (clockPower_selfAdjoint (-(1/2))) (reversedExponential_dense ε hbar hε hh)

def closedOrderedExponential (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  (orderedExponential ε hε hbar).closure

theorem orderedExponential_le_closure (ε hbar : ℝ) (hε : 0 < ε) :
    orderedExponential ε hε hbar ≤ closedOrderedExponential ε hε hbar :=
  (orderedExponential ε hε hbar).le_closure

theorem closedOrderedExponential_graph (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε) :
    (closedOrderedExponential ε hε hbar).graph=(orderedExponential ε hε hbar).graph.topologicalClosure :=
  (orderedExponential_closable ε hbar hε hh).graph_closure_eq_closure_graph.symm

theorem closedOrderedExponential_closed (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε) :
    (closedOrderedExponential ε hε hbar).IsClosed :=
  (orderedExponential_closable ε hbar hε hh).closure_isClosed

theorem closedOrderedExponential_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε) :
    Dense ((closedOrderedExponential ε hε hbar).domain : Set Hilbert) :=
  (orderedExponential_dense ε hbar hε hh).mono (orderedExponential_le_closure ε hbar hε).1

#print axioms trial_mem_reversedExponential
#print axioms reversedExponential_dense
#print axioms dressed_ordered_graph
#print axioms orderedExponential_dense
#print axioms orderedExponential_closable
#print axioms orderedExponential_le_closure
#print axioms closedOrderedExponential_graph
#print axioms closedOrderedExponential_closed
#print axioms closedOrderedExponential_dense

end
end UnifiedTheory.Audit.KFCausalOrderedExponentialClosure

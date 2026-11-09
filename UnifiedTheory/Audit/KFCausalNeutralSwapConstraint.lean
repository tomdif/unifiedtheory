/- Every packet in the proved neutral response class has an extra plane-
interchange symmetry. It survives Hilbert closure and the stronger
completed-form pair closure; it is not implied by total charge zero. -/
import UnifiedTheory.Audit.KFCausalChargedPlaneSwap
import UnifiedTheory.Audit.KFCausalNeutralResponseGraphClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNeutralSwapConstraint
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalChargedPlaneSwap
open UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles (neutralSource exponentialProfile)
open UnifiedTheory.Audit.KFCausalNeutralMixedClockState (state)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)

theorem packet_fixed (a : ℝ) (ha : 0 < a) (p : ℝ) (b C : ℂ) (P : Polynomial ℂ) :
    KFCausalPolynomialGaussianDomain.input ε a h hε ha hh C p (neutralSource b) 4 P ∈ fixedSpace := by
  have hzero : KFCausalPolynomialGaussianDomain.input ε a h hε ha hh C 0 (neutralSource b) 4 P ∈ fixedSpace := by
    have hc : Continuous (fun x : ℝ => exponentialProfile b C P (x:ℂ)) := by
      unfold exponentialProfile
      fun_prop
    have hr := KFCausalNeutralFiniteCharge.packet_relation ε a h hε ha hh b C P
    have ho := KFCausalUnboundedNeutralCharge.relation_map _ hc.measurable
      (operator : Hilbert →L[ℂ] Hilbert) neutral_multiplier _ _ hr
    change KFCausalUnboundedNeutralCharge.relation _
      (operator (KFCausalClockFloorInvariantTrial.trialState ε a h hε ha hh))
      (operator (KFCausalPolynomialGaussianDomain.input ε a h hε ha hh C 0 (neutralSource b) 4 P)) at ho
    have ht := trial_fixed ε a h hε ha hh
    change operator _ = _ at ht
    rw [ht] at ho
    exact Lp.ext (ho.trans hr.symm)
  rw [KFCausalNeutralMixedClockCharge.packet_frequency]
  change operator (KFCausalNeutralMixedClockCharge.phaseOperator p _) = _
  unfold KFCausalNeutralMixedClockCharge.phaseOperator
  rw [← clock_multiplier]
  exact congrArg (KFCausalClockChargeMultiplier.clockMultiplier _ _ _) hzero

theorem state_fixed (N : ℕ) (a p : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) :
    state ε h hε hh N a p ha b C P ∈ fixedSpace :=
  fixedSpace.sum_mem fun i _ => packet_fixed ε h hε hh (a i) (ha i) (p i) (b i) (C i) (P i)

def neutralStates : Set Hilbert := {f | ∃ (N : ℕ) (a p : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ), f = state ε h hε hh N a p ha b C P}

theorem neutralStates_subset_fixed : neutralStates ε h hε hh ⊆ fixedSpace := by
  rintro f ⟨N,a,p,ha,b,C,P,rfl⟩
  exact state_fixed ε h hε hh N a p ha b C P

theorem closure_subset_fixed : closure (neutralStates ε h hε hh) ⊆ fixedSpace :=
  closure_minimal (neutralStates_subset_fixed ε h hε hh) fixedSpace_closed

theorem completedPairs_input_fixed (hb : |h| ≤ 2*Real.pi*ε/3) (t : ℝ)
    (z : KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hb 1 1 1 t ×
      KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hb 1 1 1 t)
    (hz : z ∈ KFCausalNeutralResponseGraphClosure.completedPairs ε h hε hh hb t) :
    KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hb 1 1 1 t z.1 ∈ fixedSpace := by
  let J := KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hb 1 1 1 t
  have hc : IsClosed {w :
      KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hb 1 1 1 t ×
        KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hb 1 1 1 t |
      J w.1 ∈ fixedSpace} :=
    fixedSpace_closed.preimage (J.continuous.comp continuous_fst)
  apply closure_minimal (s := KFCausalNeutralResponseGraphClosure.packetPairs ε h hε hh hb t)
    (t := {w | J w.1 ∈ fixedSpace}) _ hc hz
  rintro w ⟨N,a,p,ha,b,C,P,rfl⟩
  exact state_fixed ε h hε hh N a p ha b C P

#print axioms packet_fixed
#print axioms state_fixed
#print axioms neutralStates_subset_fixed
#print axioms closure_subset_fixed
#print axioms completedPairs_input_fixed
end
end UnifiedTheory.Audit.KFCausalNeutralSwapConstraint

/- Actual integrated weighted potential response for common-complex-source,
constant-neutral-polynomial finite packets. All nonnegative mass, quartic
and vacuum couplings are allowed, including zero. No response premise or
clock-integrability premise is added. -/
import UnifiedTheory.Audit.KFCausalCommonComplexGaussianWeightedTransport

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonComplexGaussianPotentialResponse
noncomputable section
open MeasureTheory
open KFCausalCommonComplexQuarticJointAngular (source)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)
open KFCausalClockResponseTransport (clock coefficient coefficient_lower)
open KFCausalWeightedReciprocalNeutralWholeClock
  (positiveSlice transportResponse reducedResponse)
open KFCausalWeightedReciprocalNeutralPotentialTransport (potentialEnergy potentialResponse)
open KFCausalCommonRealGaussianPotentialResponse (fraction_div_clock_bound)

theorem reduced_bound : ∃ M : ℝ,0≤M ∧ ∀ (mass2 quartic vacuum : ℝ),
    0≤mass2→0≤quartic→0≤vacuum→
    ∀ (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ) (C : Fin n → ℂ),
    0<ε→h≠0→(∀i,1≤w i)→|h|≤2*Real.pi*ε/3→∀s:ℝ,
    -(M/ε)*positiveSlice mass2 quartic vacuum n ε h a w p C (fun _=>source A D) (fun _=>1) s≤
      reducedResponse mass2 quartic vacuum n ε h a w p C (fun _=>source A D) (fun _=>1) s := by
  obtain ⟨K,hK,hbound⟩ := KFCausalCommonComplexGaussianWeightedTransport.transport_bound
  refine ⟨2+K/4,by positivity,?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C hε hh hw hb s
  let E := positiveSlice mass2 quartic vacuum n ε h a w p C (fun _=>source A D) (fun _=>1) s
  have hE : 0≤E := KFCausalCommonComplexGaussianWeightedTransport.positiveSlice_nonnegative
    mass2 quartic vacuum n ε h A D a w p C hε hh hw hb hmass hquartic hvacuum s
  have hc : 0<clock ε s := by unfold clock; positivity
  have hy : |-h/2|≤Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  have hcoef := mul_le_mul_of_nonneg_right (coefficient_lower ε (-h/2) s hε hy) hE
  have ht := hbound mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C hε hh hw hb s
  have hdiv : transportResponse mass2 quartic vacuum n ε h a w p C
      (fun _=>source A D) (fun _=>1) s/clock ε s≤(K/(4*ε))*E := by
    calc
      _≤(K*fraction ε s*E)/clock ε s := div_le_div_of_nonneg_right ht hc.le
      _=K*(fraction ε s/clock ε s)*E := by ring
      _≤K*(1/(4*ε))*E := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (fraction_div_clock_bound ε s hε) hK) hE
      _=_ := by ring
  rw [KFCausalWeightedReciprocalNeutralWholeClock.reduced_identity]
  change -((2+K/4)/ε)*E≤coefficient ε (-h/2) s*E-
    transportResponse mass2 quartic vacuum n ε h a w p C (fun _=>source A D) (fun _=>1) s/clock ε s
  have he : -((2+K/4)/ε)*E=-(2/ε)*E-(K/(4*ε))*E := by ring
  rw [he]
  linarith

theorem potential_response_lower : ∃ M : ℝ,0≤M ∧ ∀ (mass2 quartic vacuum : ℝ),
    0≤mass2→0≤quartic→0≤vacuum→
    ∀ (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ) (C : Fin n → ℂ)
    (hε : 0<ε) (ha : ∀i,0<a i) (hh : h≠0) (hw : ∀i,1≤w i) (hb : |h|≤2*Real.pi*ε/3),
    -(M/ε)*potentialEnergy mass2 quartic vacuum n ε h a w p C (fun _=>source A D) (fun _=>1)
      hε ha hh hw hb≤
    potentialResponse mass2 quartic vacuum n ε h a w p C (fun _=>source A D) (fun _=>1)
      hε ha hh hw hb := by
  obtain ⟨M,hM,hbound⟩ := reduced_bound
  refine ⟨M,hM,?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C hε ha hh hw hb
  rw [KFCausalWeightedReciprocalNeutralPotentialTransport.potentialEnergy_integral,
    KFCausalWeightedReciprocalNeutralPotentialTransport.potentialResponse_reduced_integral,
    ←integral_const_mul]
  exact integral_mono
    ((KFCausalWeightedReciprocalNeutralPotentialTransport.positiveSlice_integrable
      mass2 quartic vacuum n ε h a w p C (fun _=>source A D) (fun _=>1) hε ha hh hw hb).const_mul _)
    (KFCausalWeightedReciprocalNeutralWholeClock.response_integrability
      mass2 quartic vacuum n ε h a w p C (fun _=>source A D) (fun _=>1) hε hh hw hb ha).2.1
    (hbound mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C hε hh hw hb)

#print axioms reduced_bound
#print axioms potential_response_lower
end
end UnifiedTheory.Audit.KFCausalCommonComplexGaussianPotentialResponse

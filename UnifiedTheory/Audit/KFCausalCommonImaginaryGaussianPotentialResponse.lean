/- Actual integrated weighted potential response for common-purely-imaginary-source,
constant-neutral-polynomial finite packets. All nonnegative mass, quartic
and vacuum couplings are allowed, including zero. No response premise or
clock-integrability premise is added. -/
import UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianWeightedTransport
import UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralPotentialTransport
import UnifiedTheory.Audit.KFCausalCommonRealGaussianPotentialResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
namespace UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianPotentialResponse
noncomputable section
open MeasureTheory
open KFCausalNeutralPlaneNormalizedGeometry (fraction)
open KFCausalClockResponseTransport (clock coefficient coefficient_lower)
open KFCausalWeightedReciprocalNeutralWholeClock (positiveSlice transportResponse reducedResponse)
open KFCausalWeightedReciprocalNeutralPotentialTransport (potentialEnergy potentialResponse)
open KFCausalCommonRealGaussianPotentialResponse (fraction_div_clock_bound)

variable (mass2 quartic vacuum : ℝ)
theorem reduced_bound (n : ℕ) (ε h D : ℝ) (a w p : Fin n → ℝ)
    (C : Fin n → ℂ) (hε : 0 < ε) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic)
    (hvacuum : 0 ≤ vacuum) (s : ℝ) :
    -(136/ε)*positiveSlice mass2 quartic vacuum n ε h a w p C (fun _ => ((D:ℂ)*Complex.I)) (fun _ => 1) s ≤
      reducedResponse mass2 quartic vacuum n ε h a w p C (fun _ => ((D:ℂ)*Complex.I)) (fun _ => 1) s := by
  let E := positiveSlice mass2 quartic vacuum n ε h a w p C (fun _ => ((D:ℂ)*Complex.I)) (fun _ => 1) s
  have hE : 0 ≤ E := KFCausalCommonImaginaryGaussianWeightedTransport.positiveSlice_nonnegative
    mass2 quartic vacuum n ε h a w p C hε hh hw hb D hmass hquartic hvacuum s
  have hc : 0 < clock ε s := by unfold clock; positivity
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  have hcoef := mul_le_mul_of_nonneg_right (coefficient_lower ε (-h/2) s hε hy) hE
  have ht := KFCausalCommonImaginaryGaussianWeightedTransport.transport_bound
    mass2 quartic vacuum n ε h a w p C hε hh hw hb D hmass hquartic hvacuum s
  have hdiv : transportResponse mass2 quartic vacuum n ε h a w p C (fun _ => ((D:ℂ)*Complex.I)) (fun _ => 1) s/clock ε s ≤
      (134/ε)*E := by
    calc
      _ ≤ (536*fraction ε s*E)/clock ε s := div_le_div_of_nonneg_right ht hc.le
      _ = 536*(fraction ε s/clock ε s)*E := by ring
      _ ≤ 536*(1/(4*ε))*E := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (fraction_div_clock_bound ε s hε) (by norm_num)) hE
      _ = _ := by ring
  rw [KFCausalWeightedReciprocalNeutralWholeClock.reduced_identity]
  change -(136/ε)*E ≤ coefficient ε (-h/2) s*E-
    transportResponse mass2 quartic vacuum n ε h a w p C (fun _ => ((D:ℂ)*Complex.I)) (fun _ => 1) s/clock ε s
  have he : -(136/ε)*E=-(2/ε)*E-(134/ε)*E := by ring
  rw [he]
  linarith

theorem potential_response_lower (n : ℕ) (ε h D : ℝ) (a w p : Fin n → ℝ)
    (C : Fin n → ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
    (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    -(136/ε)*potentialEnergy mass2 quartic vacuum n ε h a w p C
      (fun _ => ((D:ℂ)*Complex.I)) (fun _ => 1) hε ha hh hw hb ≤
      potentialResponse mass2 quartic vacuum n ε h a w p C
        (fun _ => ((D:ℂ)*Complex.I)) (fun _ => 1) hε ha hh hw hb := by
  rw [KFCausalWeightedReciprocalNeutralPotentialTransport.potentialEnergy_integral,
    KFCausalWeightedReciprocalNeutralPotentialTransport.potentialResponse_reduced_integral,
    ← integral_const_mul]
  exact integral_mono
    ((KFCausalWeightedReciprocalNeutralPotentialTransport.positiveSlice_integrable
      mass2 quartic vacuum n ε h a w p C (fun _ => ((D:ℂ)*Complex.I)) (fun _ => 1) hε ha hh hw hb).const_mul _)
    (KFCausalWeightedReciprocalNeutralWholeClock.response_integrability
      mass2 quartic vacuum n ε h a w p C (fun _ => ((D:ℂ)*Complex.I)) (fun _ => 1) hε hh hw hb ha).2.1
    (reduced_bound mass2 quartic vacuum n ε h D a w p C hε hh hw hb hmass hquartic hvacuum)

#print axioms reduced_bound
#print axioms potential_response_lower
end
end UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianPotentialResponse

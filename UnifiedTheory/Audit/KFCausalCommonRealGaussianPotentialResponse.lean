/- The original full-clock ordered-potential response on finite reciprocal
families with one common real neutral source and P=1. The pointwise transport
estimate retains its clock fraction, giving the explicit relative constant
136/epsilon after the already established clock integration by parts. -/
import UnifiedTheory.Audit.KFCausalCommonRealGaussianTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalCommonRealGaussianPotentialResponse
noncomputable section
open MeasureTheory
open KFCausalNeutralPlaneNormalizedGeometry (fraction)
open KFCausalClockResponseTransport (clock coefficient coefficient_lower)
open KFCausalReciprocalNeutralPositiveEnergy (positiveSlice potentialEnergy)
open KFCausalReciprocalNeutralWholeClock (transportResponse reducedResponse)
open KFCausalReciprocalNeutralPotentialTransport (potentialResponse)

theorem fraction_div_clock_bound (ε s : ℝ) (hε : 0 < ε) :
    fraction ε s/clock ε s ≤ 1/(4*ε) := by
  have hc : 0 < ε+Real.exp s := by positivity
  unfold fraction clock
  rw [show Real.exp s+ε=ε+Real.exp s by ring,div_div]
  apply (div_le_div_iff₀ (mul_pos hc hc) (by positivity : 0 < 4*ε)).mpr
  nlinarith [sq_nonneg (ε-Real.exp s)]

theorem reduced_bound (n : ℕ) (ε h B : ℝ) (a w p : Fin n → ℝ)
    (C : Fin n → ℂ) (hε : 0 < ε) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
    (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    -(136/ε)*positiveSlice n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) s ≤
      reducedResponse n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) s := by
  let E := positiveSlice n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) s
  have hE : 0 ≤ E := KFCausalReciprocalNeutralPositiveEnergy.positiveSlice_nonnegative
    n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) s
  have hc : 0 < clock ε s := by unfold clock; positivity
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  have hcoef := mul_le_mul_of_nonneg_right (coefficient_lower ε (-h/2) s hε hy) hE
  have ht := KFCausalCommonRealGaussianTransport.transport_bound n ε h B a w p C hε hh hw hb s
  have hdiv : transportResponse n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) s/clock ε s ≤
      (134/ε)*E := by
    calc
      _ ≤ (536*fraction ε s*E)/clock ε s := div_le_div_of_nonneg_right ht hc.le
      _ = 536*(fraction ε s/clock ε s)*E := by ring
      _ ≤ 536*(1/(4*ε))*E := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (fraction_div_clock_bound ε s hε) (by norm_num)) hE
      _ = _ := by ring
  change -(136/ε)*E ≤ coefficient ε (-h/2) s*E-
    transportResponse n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) s/clock ε s
  have he : -(136/ε)*E=-(2/ε)*E-(134/ε)*E := by ring
  rw [he]
  linarith

theorem potential_bound (n : ℕ) (ε h B : ℝ) (a w p : Fin n → ℝ)
    (C : Fin n → ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
    (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3) :
    -(136/ε)*potentialEnergy n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1)
      hε ha hh hw hb ≤
      potentialResponse n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) hε ha hh hw hb := by
  rw [KFCausalReciprocalNeutralPositiveEnergy.potentialEnergy_positive_integral,
    KFCausalReciprocalNeutralPotentialTransport.potentialResponse_reduced_integral,
    ← integral_const_mul]
  exact integral_mono
    ((KFCausalReciprocalNeutralPositiveEnergy.positiveSlice_integrable
      n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) hε ha hh hw hb).const_mul _)
    (KFCausalReciprocalNeutralWholeClock.response_integrability
      n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) hε hh hw hb ha).2.1
    (reduced_bound n ε h B a w p C hε hh hw hb)

#print axioms fraction_div_clock_bound
#print axioms reduced_bound
#print axioms potential_bound
end
end UnifiedTheory.Audit.KFCausalCommonRealGaussianPotentialResponse

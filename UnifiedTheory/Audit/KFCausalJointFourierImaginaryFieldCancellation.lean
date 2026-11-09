/- The imaginary adjacent-field contribution cancels in the full
charged-frequency integral. Absolute integrability is proved, so this
cancellation can be used after either order of integration. -/
import UnifiedTheory.Audit.KFCausalJointFourierFullTiltBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalJointFourierImaginaryFieldCancellation
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalJointFourierFrequencyDomain (amplitude)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalNeutralFourierPairing (weightedCross)
open KFCausalNeutralJointCurvatureForm (coefficients)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalClockFloorRelativeShift (scale)

local instance : SFinite chargedMeasure := by unfold chargedMeasure; infer_instance

variable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (r : ℂ)

def cross (m j l : ℕ) (q : Charged × ℝ) : ℂ :=
  (q.1.1.2:ℂ)^m*(conj (amplitude n α β w b c P r j q)*amplitude n α β w b c P r l q)

theorem cross_integrable (hβ : 0 < β) (hA : ∀ i, 0 < (w i*α)*area r)
    (hC : ∀ i, 0 < (w i*α)*area r-8*β*r.im^2) (m j l : ℕ) :
    Integrable (cross n α β w b c P r m j l) (chargedMeasure.prod volume) := by
  have hv := KFCausalJointFourierFrequencyDomain.amplitude_weighted_memLp
    n α β w b c P r hβ hA hC m j
  have hl := KFCausalJointFourierFrequencyDomain.amplitude_weighted_memLp
    n α β w b c P r hβ hA hC 0 l
  simp only [pow_zero,one_mul] at hl
  apply (hv.star.integrable_mul hl).congr
  filter_upwards [] with q
  change star ((q.1.1.2:ℂ)^m*amplitude n α β w b c P r j q)*
    amplitude n α β w b c P r l q = _
  simp only [cross,Complex.star_def,map_mul,map_pow,Complex.conj_ofReal,mul_assoc]

theorem frequency_cross_im_zero (hβ : 0 < β) (m j l : ℕ) (q : Charged) :
    (∫ k : ℝ, cross n α β w b c P r m j l (q,k)).im = 0 := by
  have he (k : ℝ) : cross n α β w b c P r m j l (q,k) =
      (q.1.2:ℂ)^m*weightedCross n β b
        (coefficients n w c (chart α r (q.1.1^2+q.1.2^2) q.2))
        (coefficients n w c (chart α r (q.1.1^2+q.1.2^2) q.2)) P P j l
        (fieldSlope r*q.1.2) (2*r.im*q.1.2) k := by
    rw [KFCausalNeutralFourierPairing.weightedCross_identity n β b _ _ P P hβ]
    rfl
  simp_rw [he]
  rw [integral_const_mul,← Complex.ofReal_pow]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
    KFCausalNeutralFourierPairing.same_profile_pairing_real n β b _ P hβ,mul_zero]

theorem full_cross_im_zero (hβ : 0 < β) (hA : ∀ i, 0 < (w i*α)*area r)
    (hC : ∀ i, 0 < (w i*α)*area r-8*β*r.im^2) (m j l : ℕ) :
    (∫ q : Charged × ℝ, cross n α β w b c P r m j l q ∂chargedMeasure.prod volume).im = 0 := by
  have hi := cross_integrable n α β w b c P r hβ hA hC m j l
  have him : (∫ q : Charged, (∫ k : ℝ, cross n α β w b c P r m j l (q,k)).im ∂chargedMeasure) =
      (∫ q : Charged, (∫ k : ℝ, cross n α β w b c P r m j l (q,k)) ∂chargedMeasure).im :=
    integral_im hi.integral_prod_left
  rw [integral_prod _ hi,← him]
  simp only [frequency_cross_im_zero n α β w b c P r hβ,integral_zero]

theorem imaginary_field_integral_zero (hβ : 0 < β) (hA : ∀ i, 0 < (w i*α)*area r)
    (hC : ∀ i, 0 < (w i*α)*area r-8*β*r.im^2) (j l : ℕ) (γ : ℝ) :
    (∫ q : Charged × ℝ, (Complex.I*(γ:ℂ)*cross n α β w b c P r 1 j l q).re
      ∂chargedMeasure.prod volume) = 0 := by
  have hi := (cross_integrable n α β w b c P r hβ hA hC 1 j l).const_mul (Complex.I*(γ:ℂ))
  have hre : (∫ q : Charged × ℝ, (Complex.I*(γ:ℂ)*cross n α β w b c P r 1 j l q).re
      ∂chargedMeasure.prod volume) =
      (∫ q : Charged × ℝ, Complex.I*(γ:ℂ)*cross n α β w b c P r 1 j l q
        ∂chargedMeasure.prod volume).re := integral_re hi
  rw [hre,integral_const_mul]
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,mul_zero,one_mul,
    full_cross_im_zero n α β w b c P r hβ hA hC,sub_self]

theorem actual_imaginary_field_integral_zero (ε y s : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i) (j l : ℕ) (γ : ℝ) :
    (∫ q : Charged × ℝ, (Complex.I*(γ:ℂ)*
      cross n α β w b c P (scale ε y s) 1 j l q).re ∂chargedMeasure.prod volume) = 0 := by
  have hi (i : Fin n) := KFCausalJointFourierFullTiltBound.actual_widths α β ε y s
    hα hβ hwidth hε hy (w i) (hw i)
  exact imaginary_field_integral_zero n α β w b c P _ hβ (fun i => (hi i).1)
    (fun i => (hi i).2) j l γ

#print axioms cross_integrable
#print axioms frequency_cross_im_zero
#print axioms full_cross_im_zero
#print axioms imaginary_field_integral_zero
#print axioms actual_imaginary_field_integral_zero
end
end UnifiedTheory.Audit.KFCausalJointFourierImaginaryFieldCancellation

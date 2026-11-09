/- A pointwise sign of a complex L2 multiplier gives the same sign for the
imaginary part of its Hilbert-space form pairing. -/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalSignedMultiplierPairing
noncomputable section
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem signed_inner_nonnegative (m : X → ℂ) (c : ℝ) (f g : Lp ℂ 2 μ)
    (hm : ∀ x, 0 ≤ c*(m x).im) (hg : g =ᵐ[μ] fun x => m x*f x) :
    0 ≤ c*(inner ℂ f g).im := by
  have hi := L2.integrable_inner (𝕜 := ℂ) f g
  have he := integral_im hi
  change (∫ x, (inner ℂ (f x) (g x)).im ∂μ) = (∫ x, inner ℂ (f x) (g x) ∂μ).im at he
  rw [L2.inner_def,← he,← integral_const_mul]
  apply integral_nonneg_of_ae
  filter_upwards [hg] with x hx
  rw [hx]
  change 0 ≤ c*(inner ℂ (f x) (m x • f x)).im
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  change 0 ≤ c*(m x*(‖f x‖:ℂ)^2).im
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,mul_zero,zero_add]
  simpa only [mul_assoc] using mul_nonneg (hm x) (sq_nonneg ‖f x‖)

#print axioms signed_inner_nonnegative

end
end UnifiedTheory.Audit.KFCausalSignedMultiplierPairing

/- A strictly signed multiplier gives a strictly signed quadratic pairing
on every nonzero L2 vector. No positive uniform multiplier bound is assumed. -/
import UnifiedTheory.Audit.KFCausalSignedMultiplierPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalStrictMultiplierPairing
noncomputable section
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem negative_integral_of_nonzero (f : X → ℝ) (hi : Integrable f μ)
    (hn : ∀ᵐ x ∂μ, f x ≤ 0) (hz : ¬ f =ᵐ[μ] 0) : (∫ x, f x ∂μ) < 0 := by
  have hp : ∀ᵐ x ∂μ, 0 ≤ -f x := hn.mono (fun _ h => neg_nonneg.mpr h)
  have hi' := hi.neg
  have he : (∫ x, -f x ∂μ) ≠ 0 := by
    intro h
    have hf := (integral_eq_zero_iff_of_nonneg_ae hp hi').mp h
    apply hz
    filter_upwards [hf] with x hx
    exact neg_eq_zero.mp hx
  have hpos := lt_of_le_of_ne (integral_nonneg_of_ae hp) (Ne.symm he)
  rw [integral_neg] at hpos
  linarith

theorem negative_integral_of_ae_negative [NeZero μ] (f : X → ℝ) (hi : Integrable f μ)
    (hn : ∀ᵐ x ∂μ, f x < 0) : (∫ x, f x ∂μ) < 0 := by
  apply negative_integral_of_nonzero μ f hi (hn.mono (fun _ h => h.le))
  intro hz
  obtain ⟨x,hx,hz'⟩ := (hn.and hz).exists
  exact (ne_of_lt hx) hz'

theorem scalar_imaginary_pairing (z w : ℂ) : (inner ℂ z (w*z)).im = w.im*‖z‖^2 := by
  change (inner ℂ z (w • z)).im = _
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  change (w*(‖z‖:ℂ)^2).im = _
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add]

theorem imaginary_pairing_integral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℝ) (f g : Lp E 2 μ) :
    c*(inner ℂ f g).im = ∫ x, c*(inner ℂ (f x) (g x)).im ∂μ := by
  have he := integral_im (L2.integrable_inner (𝕜 := ℂ) f g)
  change (∫ x, (inner ℂ (f x) (g x)).im ∂μ) = (∫ x, inner ℂ (f x) (g x) ∂μ).im at he
  rw [integral_const_mul,he,L2.inner_def]

theorem multiplier_pairing_nonpositive (m : X → ℂ) (c : ℝ) (f g : Lp ℂ 2 μ)
    (hg : g =ᵐ[μ] fun x => m x*f x) (hn : ∀ x, c*(m x).im ≤ 0) :
    c*(inner ℂ f g).im ≤ 0 := by
  rw [imaginary_pairing_integral]
  apply integral_nonpos_of_ae
  filter_upwards [hg] with x hx
  rw [hx,scalar_imaginary_pairing,← mul_assoc]
  exact mul_nonpos_of_nonpos_of_nonneg (hn x) (sq_nonneg _)

theorem multiplier_pairing_negative (m : X → ℂ) (c : ℝ) (f g : Lp ℂ 2 μ)
    (hg : g =ᵐ[μ] fun x => m x*f x) (hn : ∀ x, c*(m x).im < 0) (hf : f ≠ 0) :
    c*(inner ℂ f g).im < 0 := by
  rw [imaginary_pairing_integral]
  apply negative_integral_of_nonzero μ _ ((L2.integrable_inner (𝕜 := ℂ) f g).im.const_mul c)
  · filter_upwards [hg] with x hx
    change c*(inner ℂ (f x) (g x)).im ≤ 0
    rw [hx,scalar_imaginary_pairing,← mul_assoc]
    exact mul_nonpos_of_nonpos_of_nonneg (hn x).le (sq_nonneg _)
  · intro hz
    apply hf
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [hg,hz] with x hx he
    change c*(inner ℂ (f x) (g x)).im = 0 at he
    rw [hx,scalar_imaginary_pairing,← mul_assoc] at he
    have hn' : c*(m x).im ≠ 0 := (hn x).ne
    have hs := (mul_eq_zero.mp he).resolve_left hn'
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)

#print axioms negative_integral_of_nonzero
#print axioms negative_integral_of_ae_negative
#print axioms scalar_imaginary_pairing
#print axioms imaginary_pairing_integral
#print axioms multiplier_pairing_nonpositive
#print axioms multiplier_pairing_negative

end
end UnifiedTheory.Audit.KFCausalStrictMultiplierPairing

/- A pointwise imaginary-part velocity estimate passes to actual L2
quadratic forms, retaining its weight. -/
import UnifiedTheory.Audit.KFCausalSignedMultiplierPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalMultiplierVelocityPairing
noncomputable section
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem velocity_pairing_bound (m : X → ℂ) (p w : X → ℝ) (c K : ℝ)
    (f g k h : Lp ℂ 2 μ)
    (hg : g =ᵐ[μ] fun x => m x*f x)
    (hk : k =ᵐ[μ] fun x => (p x:ℂ)*f x)
    (hh : h =ᵐ[μ] fun x => (w x:ℂ)*f x)
    (hb : ∀ x, |c*(m x).im-p x| ≤ K*w x) :
    |c*(inner ℂ f g).im-(inner ℂ f k).re| ≤ K*(inner ℂ f h).re := by
  have hi1 := L2.integrable_inner (𝕜 := ℂ) f g
  have hi2 := L2.integrable_inner (𝕜 := ℂ) f k
  have hi3 := L2.integrable_inner (𝕜 := ℂ) f h
  have hiv : Integrable (fun x => c*(inner ℂ (f x) (g x)).im-(inner ℂ (f x) (k x)).re) μ :=
    (hi1.im.const_mul c).sub hi2.re
  have ei1 := integral_im hi1
  have ei2 := integral_re hi2
  have ei3 := integral_re hi3
  change (∫ x, (inner ℂ (f x) (g x)).im ∂μ) = (∫ x, inner ℂ (f x) (g x) ∂μ).im at ei1
  change (∫ x, (inner ℂ (f x) (k x)).re ∂μ) = (∫ x, inner ℂ (f x) (k x) ∂μ).re at ei2
  change (∫ x, (inner ℂ (f x) (h x)).re ∂μ) = (∫ x, inner ℂ (f x) (h x) ∂μ).re at ei3
  have he : c*(inner ℂ f g).im-(inner ℂ f k).re =
      ∫ x, c*(inner ℂ (f x) (g x)).im-(inner ℂ (f x) (k x)).re ∂μ := by
    rw [L2.inner_def,L2.inner_def,← ei1,← ei2,
      ← integral_const_mul]
    exact (integral_sub (hi1.im.const_mul c) hi2.re).symm
  rw [he,← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x, ‖c*(inner ℂ (f x) (g x)).im-(inner ℂ (f x) (k x)).re‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, K*(inner ℂ (f x) (h x)).re ∂μ := by
      apply integral_mono_ae hiv.norm (hi3.re.const_mul K)
      filter_upwards [hg,hk,hh] with x hxg hxk hxh
      have hm (z : ℂ) : inner ℂ (f x) (z*f x) = z*((‖f x‖:ℝ):ℂ)^2 := by
        change inner ℂ (f x) (z • f x) = _
        rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
        rfl
      change ‖c*(inner ℂ (f x) (g x)).im-(inner ℂ (f x) (k x)).re‖ ≤
        K*(inner ℂ (f x) (h x)).re
      rw [hxg,hxk,hxh,hm,hm,hm,← Complex.ofReal_pow]
      simp only [Complex.mul_im,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,
        mul_zero,zero_add,sub_zero,Real.norm_eq_abs]
      have hh' := mul_le_mul_of_nonneg_right (hb x) (sq_nonneg ‖f x‖)
      convert hh' using 1
      · rw [← mul_assoc,← sub_mul,abs_mul,abs_of_nonneg (sq_nonneg ‖f x‖)]
      · ring
    _ = K*(inner ℂ f h).re := by
      rw [integral_const_mul,ei3,L2.inner_def]

#print axioms velocity_pairing_bound

theorem integrated_velocity_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c K : ℝ) (f g k : Lp E 2 μ)
    (hb : ∀ᵐ x ∂μ, |c*(inner ℂ (f x) (g x)).im-(inner ℂ (f x) (k x)).re| ≤ K*‖f x‖^2) :
    |c*(inner ℂ f g).im-(inner ℂ f k).re| ≤ K*‖f‖^2 := by
  have hi1 := L2.integrable_inner (𝕜 := ℂ) f g
  have hi2 := L2.integrable_inner (𝕜 := ℂ) f k
  have hi3 := L2.integrable_inner (𝕜 := ℂ) f f
  have ei1 := integral_im hi1
  have ei2 := integral_re hi2
  have ei3 := integral_re hi3
  change (∫ x, (inner ℂ (f x) (g x)).im ∂μ) = (∫ x, inner ℂ (f x) (g x) ∂μ).im at ei1
  change (∫ x, (inner ℂ (f x) (k x)).re ∂μ) = (∫ x, inner ℂ (f x) (k x) ∂μ).re at ei2
  change (∫ x, (inner ℂ (f x) (f x)).re ∂μ) = (∫ x, inner ℂ (f x) (f x) ∂μ).re at ei3
  have hiv := (hi1.im.const_mul c).sub hi2.re
  have he : c*(inner ℂ f g).im-(inner ℂ f k).re =
      ∫ x, c*(inner ℂ (f x) (g x)).im-(inner ℂ (f x) (k x)).re ∂μ := by
    rw [L2.inner_def,L2.inner_def,← ei1,← ei2,
      ← integral_const_mul]
    exact (integral_sub (hi1.im.const_mul c) hi2.re).symm
  rw [he,← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x, ‖c*(inner ℂ (f x) (g x)).im-(inner ℂ (f x) (k x)).re‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, K*(inner ℂ (f x) (f x)).re ∂μ := by
      apply integral_mono_ae hiv.norm (hi3.re.const_mul K)
      filter_upwards [hb] with x hx
      change ‖c*(inner ℂ (f x) (g x)).im-(inner ℂ (f x) (k x)).re‖ ≤ K*(inner ℂ (f x) (f x)).re
      have hs : (inner ℂ (f x) (f x)).re = ‖f x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
      rw [hs,Real.norm_eq_abs]
      exact hx
    _ = K*‖f‖^2 := by
      have hs : (inner ℂ f f).re = ‖f‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
      rw [integral_const_mul,ei3,← L2.inner_def,hs]

#print axioms integrated_velocity_bound

end
end UnifiedTheory.Audit.KFCausalMultiplierVelocityPairing

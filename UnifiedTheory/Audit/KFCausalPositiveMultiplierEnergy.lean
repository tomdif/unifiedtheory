/- Positivity and exact weighted energy for the constructed multiplier.
Domain membership includes genuine integrability of the weighted square. -/
import UnifiedTheory.Audit.KFCausalPositiveMultiplierResolvent
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPositiveMultiplierEnergy
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalPositiveMultiplierResolvent

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem l2_norm_square (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  calc
    _ = inner ℂ f f := by
      simpa only [Complex.ofReal_pow] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f).symm
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast

theorem multiplier_coe (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x)
    (f : (positiveMultiplier (μ := μ) w hm hw).domain) :
    positiveMultiplier w hm hw f =ᵐ[μ] fun x => (w x:ℂ)*(f:Lp ℂ 2 μ) x :=
  (multiplier_graph_iff (μ := μ) w hm hw (f:Lp ℂ 2 μ) _).mp
    ((positiveMultiplier w hm hw).mem_graph f)

theorem multiplier_domain_integrable_iff (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x)
    (f : Lp ℂ 2 μ) :
    f ∈ (positiveMultiplier w hm hw).domain ↔ Integrable (fun x => (w x)^2*‖f x‖^2) μ := by
  rw [multiplier_domain_iff]
  have ha : AEStronglyMeasurable (fun x => (w x:ℂ)*f x) μ :=
    (Complex.continuous_ofReal.measurable.comp hm).aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm ha]
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem multiplier_norm_square (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x)
    (f : (positiveMultiplier (μ := μ) w hm hw).domain) :
    ‖positiveMultiplier w hm hw f‖^2 = ∫ x, (w x)^2*‖(f:Lp ℂ 2 μ) x‖^2 ∂μ := by
  rw [l2_norm_square]
  apply integral_congr_ae
  filter_upwards [multiplier_coe w hm hw f] with x hx
  rw [hx]
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem real_weight_inner (r : ℝ) (z : ℂ) :
    (inner ℂ ((r:ℂ)*z) z).re = r*‖z‖^2 := by
  change (inner ℂ ((r:ℂ) • z) z).re = _
  rw [inner_smul_left,Complex.conj_ofReal,inner_self_eq_norm_sq_to_K]
  change ((r:ℂ)*(‖z‖:ℂ)^2).re = _
  norm_cast

theorem multiplier_inner (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x)
    (f : (positiveMultiplier (μ := μ) w hm hw).domain) :
    (inner ℂ (positiveMultiplier w hm hw f) (f:Lp ℂ 2 μ)).re =
      ∫ x, w x*‖(f:Lp ℂ 2 μ) x‖^2 ∂μ := by
  rw [L2.inner_def]
  change RCLike.re (∫ x, inner ℂ ((positiveMultiplier w hm hw f) x) ((f:Lp ℂ 2 μ) x) ∂μ) = _
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) (positiveMultiplier w hm hw f) (f:Lp ℂ 2 μ))]
  apply integral_congr_ae
  filter_upwards [multiplier_coe w hm hw f] with x hx
  rw [hx]
  exact real_weight_inner _ _

theorem multiplier_positive (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x)
    (f : (positiveMultiplier (μ := μ) w hm hw).domain) :
    0 ≤ (inner ℂ (positiveMultiplier w hm hw f) (f:Lp ℂ 2 μ)).re := by
  rw [multiplier_inner]
  exact integral_nonneg (fun x => mul_nonneg (hw x) (sq_nonneg _))

#print axioms l2_norm_square
#print axioms multiplier_coe
#print axioms multiplier_domain_integrable_iff
#print axioms multiplier_norm_square
#print axioms multiplier_inner
#print axioms multiplier_positive

end
end UnifiedTheory.Audit.KFCausalPositiveMultiplierEnergy

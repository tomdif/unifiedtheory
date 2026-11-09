/- A positive exponential controls the positive spectral tail. The translation
estimate separates the negative tail explicitly; no two-sided momentum
coercivity is assumed or inferred from an exponential energy. -/
import UnifiedTheory.Audit.KFCausalL2PhaseTailBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalL2ExponentialTailBound
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation (modulation phase phase_norm)
open UnifiedTheory.Audit.KFCausalL2PhaseTailBound
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem positive_tail (w : X → ℝ) (hw : Measurable w) (R : ℝ)
    (f : Lp ℂ 2 μ) (he : Integrable (fun x => Real.exp (w x)*‖f x‖^2) μ) :
    (∫ x in {x | R ≤ w x}, ‖f x‖^2 ∂μ) ≤
      Real.exp (-R)*(∫ x, Real.exp (w x)*‖f x‖^2 ∂μ) := by
  have hs : MeasurableSet {x | R ≤ w x} := measurableSet_le measurable_const hw
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  rw [← integral_indicator hs,← integral_const_mul]
  apply integral_mono_ae (hf.indicator hs) (he.const_mul _)
  filter_upwards [] with x
  by_cases hx : R ≤ w x
  · rw [Set.indicator_of_mem (show x ∈ {x | R ≤ w x} from hx)]
    have hex : 1 ≤ Real.exp (-R)*Real.exp (w x) := by
      rw [← Real.exp_add,Real.one_le_exp_iff]
      linarith
    nlinarith only [mul_le_mul_of_nonneg_right hex (sq_nonneg ‖f x‖)]
  · rw [Set.indicator_of_notMem (show x ∉ {x | R ≤ w x} from hx)]
    positivity

theorem phase_square_bound (v w R : ℝ) :
    ‖Complex.exp (Complex.I*(v*w:ℝ))-1‖^2 ≤
      v^2*(R^2+2*Real.exp w)+4*(if w < -R then 1 else 0) := by
  by_cases ht : w < -R
  · rw [if_pos ht]
    have hb : ‖Complex.exp (Complex.I*(v*w:ℝ))-1‖ ≤ 2 := by
      simpa only [Complex.norm_exp_ofReal_mul_I,Complex.norm_exp_I_mul_ofReal,norm_one,
        one_add_one_eq_two] using norm_sub_le (Complex.exp (Complex.I*(v*w:ℝ))) (1:ℂ)
    have hp : 0 ≤ v^2*(R^2+2*Real.exp w) := by positivity
    nlinarith [norm_nonneg (Complex.exp (Complex.I*(v*w:ℝ))-1)]
  · rw [if_neg ht,mul_zero,add_zero]
    have hb := pow_le_pow_left₀ (norm_nonneg (Complex.exp (Complex.I*(v*w:ℝ))-1))
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := v*w)) 2
    rw [Real.norm_eq_abs,sq_abs,mul_pow] at hb
    have hwR : w^2 ≤ R^2+2*Real.exp w := by
      by_cases hw : 0 ≤ w
      · have hex := Real.pow_div_factorial_le_exp w hw 2
        norm_num at hex
        nlinarith [sq_nonneg R]
      · have hw' : -R ≤ w := le_of_not_gt ht
        nlinarith [Real.exp_pos w,mul_nonneg (by linarith : 0 ≤ R+w) (by linarith : 0 ≤ R-w)]
    exact hb.trans (mul_le_mul_of_nonneg_left hwR (sq_nonneg v))

theorem phase_difference_negative_tail (w : X → ℝ) (hw : Measurable w)
    (v R : ℝ) (f : Lp ℂ 2 μ)
    (he : Integrable (fun x => Real.exp (w x)*‖f x‖^2) μ) :
    ‖modulation μ (fun x => v*w x) (measurable_const.mul hw) f-f‖^2 ≤
      v^2*(R^2*‖f‖^2+2*(∫ x, Real.exp (w x)*‖f x‖^2 ∂μ))+
        4*(∫ x in {x | w x < -R}, ‖f x‖^2 ∂μ) := by
  have hs : MeasurableSet {x | w x < -R} := measurableSet_lt hw measurable_const
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hb := ((hf.const_mul (R^2)).add (he.const_mul 2)).const_mul (v^2)
  have ht := (hf.indicator hs).const_mul 4
  simp only [Pi.add_apply] at hb
  rw [phase_difference_square w hw v f,l2_norm_square,← integral_indicator hs,
    ← integral_const_mul,← integral_const_mul,← integral_const_mul,
    ← integral_add (hf.const_mul (R^2)) (he.const_mul 2),
    ← integral_const_mul,← integral_add hb ht]
  apply integral_mono_ae (phase_difference_integrable w hw v f) (hb.add ht)
  filter_upwards [] with x
  have h := mul_le_mul_of_nonneg_right (phase_square_bound v (w x) R) (sq_nonneg ‖f x‖)
  by_cases hx : w x < -R
  · simp only [Pi.add_apply,Set.indicator_of_mem (show x ∈ {x | w x < -R} from hx),
      if_pos hx,phase] at h ⊢
    nlinarith only [h]
  · simp only [Pi.add_apply,Set.indicator_of_notMem (show x ∉ {x | w x < -R} from hx),
      if_neg hx,phase] at h ⊢
    nlinarith only [h]

#print axioms positive_tail
#print axioms phase_square_bound
#print axioms phase_difference_negative_tail

end
end UnifiedTheory.Audit.KFCausalL2ExponentialTailBound

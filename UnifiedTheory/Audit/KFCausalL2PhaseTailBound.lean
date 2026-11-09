/- A radial Born tail controls the norm of bounded phase tests. No
unweighted second moment is required: the phase difference is bounded by
the frequency inside a ball and by two outside. -/
import UnifiedTheory.Audit.KFCausalLpPhaseTranslation
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalL2PhaseTailBound
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation (modulation modulation_coe phase phase_norm)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

variable {X : Type*} [MeasurableSpace X]
  {μ : Measure X}

theorem phase_difference_square (w : X → ℝ) (hw : Measurable w) (t : ℝ) (f : Lp ℂ 2 μ) :
    ‖modulation μ (fun x => t*w x) (measurable_const.mul hw) f-f‖^2 =
      ∫ x, ‖phase (fun x => t*w x) x-1‖^2*‖f x‖^2 ∂μ := by
  rw [l2_norm_square]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (modulation μ (fun x => t*w x) (measurable_const.mul hw) f) f,
    modulation_coe μ (fun x => t*w x) (measurable_const.mul hw) f] with x hs hm
  simp only [Pi.sub_apply] at hs
  rw [hs,hm,show phase (fun x => t*w x) x*f x-f x = (phase (fun x => t*w x) x-1)*f x by ring,
    norm_mul,mul_pow]

theorem phase_difference_integrable (w : X → ℝ) (hw : Measurable w) (t : ℝ) (f : Lp ℂ 2 μ) :
    Integrable (fun x => ‖phase (fun x => t*w x) x-1‖^2*‖f x‖^2) μ := by
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  apply (hf.const_mul 4).mono' ?_ ?_
  · exact (((Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (measurable_const.mul hw))))).aestronglyMeasurable.sub
        aestronglyMeasurable_const).norm.pow 2 |>.mul ((Lp.aestronglyMeasurable f).norm.pow 2)
  · filter_upwards [] with x
    have hb : ‖phase (fun x => t*w x) x-1‖ ≤ 2 := by
      simpa only [phase_norm,norm_one,one_add_one_eq_two] using norm_sub_le (phase (fun x => t*w x) x) (1:ℂ)
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    nlinarith [mul_le_mul_of_nonneg_right (show ‖phase (fun x => t*w x) x-1‖^2 ≤ 4 by nlinarith [norm_nonneg (phase (fun x => t*w x) x-1)]) (sq_nonneg ‖f x‖)]

theorem phase_difference_square_tail (w S : X → ℝ) (hw : Measurable w) (hS : Measurable S)
    (hdom : ∀ x, w x^2 ≤ S x) (t R : ℝ) (hR : 0 ≤ R) (f : Lp ℂ 2 μ) :
    ‖modulation μ (fun x => t*w x) (measurable_const.mul hw) f-f‖^2 ≤
      t^2*R^2*‖f‖^2+4*(∫ x in {x | R^2 ≤ S x}, ‖f x‖^2 ∂μ) := by
  have hs : MeasurableSet {x | R^2 ≤ S x} := measurableSet_le measurable_const hS
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  rw [phase_difference_square w hw t f, l2_norm_square,← integral_indicator hs,← integral_const_mul,
    ← integral_const_mul,← integral_add (hf.const_mul _) ((hf.indicator hs).const_mul _)]
  apply integral_mono_ae (phase_difference_integrable w hw t f)
    ((hf.const_mul _).add ((hf.indicator hs).const_mul _))
  filter_upwards [] with x
  simp only [Pi.add_apply]
  by_cases hx : R^2 ≤ S x
  · rw [Set.indicator_of_mem (show x ∈ {x | R^2 ≤ S x} from hx)]
    have hb : ‖phase (fun x => t*w x) x-1‖ ≤ 2 := by
      simpa only [phase_norm,norm_one,one_add_one_eq_two] using norm_sub_le (phase (fun x => t*w x) x) (1:ℂ)
    have he : ‖phase (fun x => t*w x) x-1‖^2 ≤ 4 := by nlinarith [norm_nonneg (phase (fun x => t*w x) x-1)]
    nlinarith [mul_le_mul_of_nonneg_right he (sq_nonneg ‖f x‖),
      mul_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg R)) (sq_nonneg ‖f x‖)]
  · rw [Set.indicator_of_notMem (show x ∉ {x | R^2 ≤ S x} from hx),mul_zero,add_zero]
    have hwR : |w x| ≤ R := by
      have hn : S x < R^2 := lt_of_not_ge hx
      nlinarith [hdom x,sq_abs (w x),abs_nonneg (w x)]
    have hb : ‖phase (fun x => t*w x) x-1‖ ≤ |t| * R :=
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t*w x)).trans
        ((abs_mul t (w x)).trans_le (mul_le_mul_of_nonneg_left hwR (abs_nonneg t)))
    have he : ‖phase (fun x => t*w x) x-1‖^2 ≤ t^2*R^2 := by
      have hsq := pow_le_pow_left₀ (norm_nonneg (phase (fun x => t*w x) x-1)) hb 2
      simpa only [mul_pow,sq_abs] using hsq
    exact mul_le_mul_of_nonneg_right he (sq_nonneg ‖f x‖)

#print axioms phase_difference_square
#print axioms phase_difference_integrable
#print axioms phase_difference_square_tail

end
end UnifiedTheory.Audit.KFCausalL2PhaseTailBound

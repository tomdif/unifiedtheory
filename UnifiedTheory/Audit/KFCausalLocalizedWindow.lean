/- Explicit unit windows supported in arbitrarily small Euclidean balls.
Their position-phase displacement is bounded by the radius times the
operator norm of the tested linear functional. -/
import UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
import UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalLocalizedWindow
noncomputable section
open MeasureTheory MeasureTheory.Measure
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation (modulation modulation_coe)

variable (n : ℕ)

def ballState (r : ℝ) : BlockHilbert n :=
  indicatorConstLp 2 (Metric.isOpen_ball.measurableSet : MeasurableSet (Metric.ball (0 : Block n) r))
    measure_ball_lt_top.ne (1 : ℂ)

theorem ballState_norm_pos (r : ℝ) (hr : 0 < r) : 0 < ‖ballState n r‖ := by
  have hm : 0 < (volume : Measure (Block n)).real (Metric.ball 0 r) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 hr).ne' measure_ball_lt_top.ne
  rw [ballState,norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [norm_one,one_mul]
  exact Real.rpow_pos_of_pos hm _

def window (r : ℝ) : BlockHilbert n := (‖ballState n r‖⁻¹ : ℝ) • ballState n r

theorem window_norm (r : ℝ) (hr : 0 < r) : ‖window n r‖ = 1 := by
  rw [window,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (ballState_norm_pos n r hr).ne'

theorem window_support (r : ℝ) : ∀ᵐ x ∂(volume : Measure (Block n)),
    r ≤ ‖x‖ → window n r x = 0 := by
  filter_upwards [Lp.coeFn_smul (‖ballState n r‖⁻¹ : ℝ) (ballState n r),
    (indicatorConstLp_coeFn_notMem (p := 2) (μ := (volume : Measure (Block n)))
      (hs := Metric.isOpen_ball.measurableSet) (hμs := measure_ball_lt_top.ne) (c := (1 : ℂ)))] with x hs hx
  intro hxr
  have hn : x ∉ Metric.ball (0 : Block n) r := by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hxr
  change ((‖ballState n r‖⁻¹ : ℝ) • ballState n r) x = 0
  rw [hs]
  change (‖ballState n r‖⁻¹ : ℝ) • ballState n r x = 0
  rw [show ballState n r x = 0 from hx hn,smul_zero]

theorem localized_modulation_bound (r : ℝ) (u : Block n →L[ℝ] ℝ)
    (f : BlockHilbert n) (hs : ∀ᵐ x ∂volume, r ≤ ‖x‖ → f x = 0) :
    ‖modulation volume u u.continuous.measurable f-f‖ ≤ (‖u‖*r)*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (modulation volume u u.continuous.measurable f) f,
    modulation_coe volume u u.continuous.measurable f,hs] with x hd hm hx
  rw [hd]
  simp only [Pi.sub_apply,hm]
  by_cases hxr : r ≤ ‖x‖
  · rw [hx hxr,mul_zero,sub_zero,norm_zero,mul_zero]
  · have hux : |u x| ≤ ‖u‖*r := (u.le_opNorm x).trans
      (mul_le_mul_of_nonneg_left (le_of_not_ge hxr) (norm_nonneg _))
    rw [show KFCausalLpPhaseTranslation.phase u x*f x-f x =
      (scalar (u x)-1)*f x by change scalar (u x)*f x-f x = _; ring, norm_mul]
    exact mul_le_mul_of_nonneg_right ((scalar_sub_one (u x)).trans hux) (norm_nonneg _)

theorem window_modulation_bound (r : ℝ) (hr : 0 < r) (u : Block n →L[ℝ] ℝ) :
    ‖modulation volume u u.continuous.measurable (window n r)-window n r‖ ≤ ‖u‖*r := by
  simpa only [window_norm n r hr,mul_one] using
    localized_modulation_bound n r u (window n r) (window_support n r)

#print axioms ballState_norm_pos
#print axioms window_norm
#print axioms window_support
#print axioms localized_modulation_bound
#print axioms window_modulation_bound

end
end UnifiedTheory.Audit.KFCausalLocalizedWindow

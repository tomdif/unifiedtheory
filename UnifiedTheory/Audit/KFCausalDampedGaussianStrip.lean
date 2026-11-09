/- Complex extension of the repaired scalar trial function. The real-axis
tail repair is compatible with Gaussian bounds on a nonzero complex strip.
Fourier exponential-domain consequences are derived separately. -/
import UnifiedTheory.Audit.KFCausalCoupledDampedGaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalDampedGaussianStrip
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalCoupledDampedGaussian

def entire (ε a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(a/2:ℝ)*z^2-(ε:ℂ)*Complex.exp (-(z/(ε:ℂ))))

def line (ε a y : ℝ) (q : ℝ) : ℂ := entire ε a ((q:ℂ)+(y:ℂ)*Complex.I)

theorem entire_differentiable (ε a : ℝ) : Differentiable ℂ (entire ε a) := by
  unfold entire
  fun_prop

theorem line_continuous (ε a y : ℝ) : Continuous (line ε a y) := by
  unfold line
  exact (entire_differentiable ε a).continuous.comp (by fun_prop)

theorem entire_real (ε a q : ℝ) : entire ε a q = (dampedGaussian ε a q:ℂ) := by
  unfold entire dampedGaussian
  push_cast
  simp only [neg_div]

theorem line_norm (ε a y q : ℝ) :
    ‖line ε a y q‖ =
      Real.exp (-(a/2)*(q^2-y^2)-ε*Real.exp (-q/ε)*Real.cos (y/ε)) := by
  rw [line,entire,Complex.norm_exp]
  congr 1
  simp [Complex.exp_re,Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.mul_re,
    Complex.mul_im,pow_two,Real.cos_neg]
  ring

theorem line_gaussian_bound (ε a y q : ℝ) (hε : 0 ≤ ε) (hy : 0 ≤ Real.cos (y/ε)) :
    ‖line ε a y q‖ ≤ Real.exp ((a/2)*y^2)*Real.exp (-(a/2)*q^2) := by
  rw [line_norm,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (mul_nonneg hε (Real.exp_pos (-q/ε)).le) hy]

theorem cosine_nonnegative (ε d y : ℝ) (hε : 0 < ε)
    (hd : d ≤ Real.pi*ε/2) (hy : |y| ≤ d) : 0 ≤ Real.cos (y/ε) := by
  apply Real.cos_nonneg_of_mem_Icc
  have ha := (abs_le.mp hy)
  constructor
  · apply (le_div_iff₀ hε).mpr
    nlinarith
  · apply (div_le_iff₀ hε).mpr
    nlinarith

theorem strip_gaussian_bound (ε a d : ℝ) (hε : 0 < ε) (ha : 0 ≤ a)
    (hd : d ≤ Real.pi*ε/2) (y q : ℝ) (hy : |y| ≤ d) :
    ‖line ε a y q‖ ≤ Real.exp ((a/2)*d^2)*Real.exp (-(a/2)*q^2) := by
  have hb := line_gaussian_bound ε a y q hε.le (cosine_nonnegative ε d y hε hd hy)
  have hd0 : 0 ≤ d := (abs_nonneg y).trans hy
  have hs : y^2 ≤ d^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg y) hd0).mpr hy
  apply hb.trans
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs (by positivity))) (Real.exp_pos _).le

theorem line_integrable (ε a y : ℝ) (hε : 0 ≤ ε) (ha : 0 < a)
    (hy : 0 ≤ Real.cos (y/ε)) : Integrable (line ε a y) := by
  have hi := (integrable_exp_neg_mul_sq (by positivity : 0 < a/2)).const_mul (Real.exp ((a/2)*y^2))
  apply hi.mono' (line_continuous ε a y).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun q => line_gaussian_bound ε a y q hε hy)

theorem line_square_integrable (ε a y : ℝ) (hε : 0 ≤ ε) (ha : 0 < a)
    (hy : 0 ≤ Real.cos (y/ε)) : Integrable (fun q => ‖line ε a y q‖^2) := by
  have hi := (integrable_exp_neg_mul_sq ha).const_mul (Real.exp (a*y^2))
  apply hi.mono' ((line_continuous ε a y).norm.pow 2).aestronglyMeasurable
  filter_upwards [] with q
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hh := line_gaussian_bound ε a y q hε hy
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hh
  convert hs using 1
  rw [mul_pow,← Real.exp_nat_mul,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  congr 1 <;> congr 1 <;> ring

#print axioms entire_differentiable
#print axioms entire_real
#print axioms line_norm
#print axioms strip_gaussian_bound
#print axioms line_integrable
#print axioms line_square_integrable

end
end UnifiedTheory.Audit.KFCausalDampedGaussianStrip

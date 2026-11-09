/- Cauchy's estimate controls differences inside a bounded analytic
strip. The constant is explicit and independent of the real coordinate. -/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalBoundedStripDifference
noncomputable section
open Set Metric

theorem half_ball_im (d : ℝ) (q w : ℂ) (hq : |q.im| ≤ d/2)
    (hw : w ∈ closedBall q (d/2)) : |w.im| ≤ d := by
  have hn : ‖w-q‖ ≤ d/2 := mem_closedBall_iff_norm.mp hw
  have hi : |w.im-q.im| ≤ ‖w-q‖ := Complex.abs_im_le_norm (w-q)
  have ha : |w.im| ≤ |w.im-q.im|+|q.im| := by
    simpa only [sub_add_cancel] using abs_add_le (w.im-q.im) q.im
  linarith

variable (d M : ℝ) (hd : 0 < d) (f : ℂ → ℂ)
  (hF : ∀ q, |q.im| ≤ d → AnalyticAt ℂ f q)
  (hB : ∀ q, |q.im| ≤ d → ‖f q‖ ≤ M)

include hd hF hB in
theorem derivative_bound (q : ℂ) (hq : |q.im| ≤ d/2) :
    ‖deriv f q‖ ≤ 2*M/d := by
  have hf : DifferentiableOn ℂ f (closedBall q (d/2)) :=
    fun w hw => (hF w (half_ball_im d q w hq hw)).differentiableAt.differentiableWithinAt
  have hc : DiffContOnCl ℂ f (ball q (d/2)) :=
    DiffContOnCl.mk_ball (hf.mono ball_subset_closedBall) hf.continuousOn
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith : 0 < d/2)
    hc (fun w hw => hB w (half_ball_im d q w hq (sphere_subset_closedBall hw)))
  convert hb using 1
  ring

include hd hF hB in
theorem difference_bound (q r : ℂ) (hq : |q.im| ≤ d/2) (hr : |r.im| ≤ d/2) :
    ‖f r-f q‖ ≤ (2*M/d)*‖r-q‖ := by
  have hs : Convex ℝ {z : ℂ | |z.im| ≤ d/2} := by
    have hc := (convex_Icc (-(d/2)) (d/2)).linear_preimage Complex.imLm
    convert hc using 1
    ext z
    change (|z.im| ≤ d/2) ↔ (-(d/2) ≤ z.im ∧ z.im ≤ d/2)
    exact abs_le
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hF z (le_trans hz (by linarith))).differentiableAt)
    (fun z hz => derivative_bound d M hd f hF hB z hz) hs hq hr

include hd hF hB in
theorem vertical_difference (a h : ℝ) (hh : |h| ≤ d) :
    ‖f ((a:ℂ)+(-h/2:ℝ)*Complex.I)-f ((a:ℂ)+(h/2:ℝ)*Complex.I)‖ ≤
      (2*M/d)*|h| := by
  have hm : |(((a:ℂ)+(-h/2:ℝ)*Complex.I):ℂ).im| ≤ d/2 := by
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add,abs_div,abs_neg]
    norm_num
    linarith
  have hp : |(((a:ℂ)+(h/2:ℝ)*Complex.I):ℂ).im| ≤ d/2 := by
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add,abs_div]
    norm_num
    linarith
  have he : ((a:ℂ)+(-h/2:ℝ)*Complex.I)-((a:ℂ)+(h/2:ℝ)*Complex.I) = -(h:ℂ)*Complex.I := by
    push_cast
    ring
  have hb := difference_bound d M hd f hF hB _ _ hp hm
  rw [he,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one] at hb
  exact hb

#print axioms half_ball_im
#print axioms derivative_bound
#print axioms difference_bound
#print axioms vertical_difference

end
end UnifiedTheory.Audit.KFCausalBoundedStripDifference

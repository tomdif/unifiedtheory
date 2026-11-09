/- Uniform first-order remainder for the actual charged Gaussian cutoff.
The slope is bounded by 2 sqrt(delta) and is 2 delta-Lipschitz. -/
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalGaussianCutoffTaylor
noncomputable section

def amplitude (δ r : ℝ) : ℝ := Real.exp (-δ*r^2)
def slope (δ r : ℝ) : ℝ := -2*δ*Real.mulExpNegMulSq δ r

theorem amplitude_bounds (δ : ℝ) (hδ : 0 ≤ δ) (r : ℝ) :
    0 ≤ amplitude δ r ∧ amplitude δ r ≤ 1 :=
  ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))⟩

theorem amplitude_derivative (δ r : ℝ) : HasDerivAt (amplitude δ) (slope δ r) r := by
  have hd := (((hasDerivAt_id r).pow 2).const_mul (-δ)).exp
  convert hd using 1
  unfold slope Real.mulExpNegMulSq
  have he : -(δ*r*r) = -δ*r^2 := by ring
  rw [he]
  simp only [Pi.pow_apply,id_eq]
  ring

theorem slope_bound (δ : ℝ) (hδ : 0 < δ) (r : ℝ) : |slope δ r| ≤ 2*Real.sqrt δ := by
  have hs := Real.abs_mulExpNegMulSq_le hδ (x := r)
  rw [slope,abs_mul,abs_mul,abs_neg,abs_of_pos hδ]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*δ)).trans_eq
  have hr := Real.sq_sqrt hδ.le
  have hn := (Real.sqrt_pos.mpr hδ).ne'
  nth_rw 1 [← hr]
  field_simp

theorem slope_lipschitz (δ : ℝ) (hδ : 0 < δ) (r s : ℝ) :
    |slope δ r-slope δ s| ≤ 2*δ*|r-s| := by
  rw [slope,slope,← mul_sub,abs_mul,abs_mul,abs_neg,abs_of_pos hδ]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Real.dist_eq] using Real.dist_mulExpNegMulSq_le_dist hδ (x := r) (y := s))
    (by positivity)

theorem amplitude_remainder (δ : ℝ) (hδ : 0 < δ) (r t : ℝ) :
    |amplitude δ (r+t)-amplitude δ r-t*slope δ r| ≤ 2*δ*t^2 := by
  let R := fun u => amplitude δ u-amplitude δ r-(u-r)*slope δ r
  have hd (u : ℝ) : HasDerivAt R (slope δ u-slope δ r) u := by
    simpa only [one_mul] using ((amplitude_derivative δ u).sub_const (amplitude δ r)).sub
      (((hasDerivAt_id u).sub_const r).mul_const (slope δ r))
  have hb (u : ℝ) (hu : u ∈ segment ℝ r (r+t)) : ‖slope δ u-slope δ r‖ ≤ 2*δ*|t| := by
    apply (slope_lipschitz δ hδ u r).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2*δ)
    simpa only [Real.norm_eq_abs,add_sub_cancel_left] using norm_sub_le_of_mem_segment hu
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u (_hu : u ∈ segment ℝ r (r+t)) => (hd u).hasDerivWithinAt) hb
    (convex_segment r (r+t)) (left_mem_segment ℝ r (r+t)) (right_mem_segment ℝ r (r+t))
  simp only [R,sub_self,zero_mul,sub_zero,add_sub_cancel_left,Real.norm_eq_abs] at hm
  exact hm.trans_eq (by rw [mul_assoc,← sq,sq_abs])

#print axioms amplitude_bounds
#print axioms amplitude_derivative
#print axioms slope_bound
#print axioms slope_lipschitz
#print axioms amplitude_remainder

end
end UnifiedTheory.Audit.KFCausalGaussianCutoffTaylor

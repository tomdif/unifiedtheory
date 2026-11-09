/- Exact quartic field-slope control and its pointwise Young bound.
The latter absorbs the field term into the actual v^2 energy moment,
without division by the energy of a coherent superposition. -/
import UnifiedTheory.Audit.KFCausalAngularQuarticGaussianSmoothing

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalQuarticFieldSlopeBound
noncomputable section
open KFCausalAngularQuarticGaussianSmoothing (weight weightSlope)

theorem slope_square (sigma x : ℝ) (hs : 0≤sigma) :
    sigma*(weightSlope sigma x)^2≤4*(weight sigma x)^2 := by
  have he : 4*(weight sigma x)^2-sigma*(weightSlope sigma x)^2=
      4*(x^8+8*sigma*x^6+18*sigma^2*x^4+9*sigma^4) := by
    unfold weight weightSlope
    ring
  have hp : 0≤4*(x^8+8*sigma*x^6+18*sigma^2*x^4+9*sigma^4) := by positivity
  linarith

theorem slope_bound (sigma x : ℝ) (hs : 0<sigma) :
    |weightSlope sigma x|≤(2/Real.sqrt sigma)*weight sigma x := by
  have hW : 0≤weight sigma x := by unfold weight; positivity
  have hsq : (Real.sqrt sigma*|weightSlope sigma x|)^2≤(2*weight sigma x)^2 := by
    rw [mul_pow,Real.sq_sqrt hs.le,sq_abs]
    nlinarith only [slope_square sigma x hs.le]
  have hle := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    (by positivity : 0≤2*weight sigma x)).mp hsq
  have ht : |weightSlope sigma x|≤(2*weight sigma x)/Real.sqrt sigma :=
    (le_div_iff₀ (Real.sqrt_pos.mpr hs)).mpr (by simpa only [mul_comm] using hle)
  convert ht using 1
  ring

private theorem scalar_young (a b c v : ℝ) (ha : 0≤a) (hc : 0≤c)
    (hb : b^2≤4*a*c) : -(a*v^2+c)≤b*v := by
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg v)
  have he : (b*v)^2≤4*(a*v^2)*c := by nlinarith only [hm]
  have hp : 0≤a*v^2+c := by positivity
  have hab : |b*v|≤a*v^2+c := by
    have hh := sq_nonneg (a*v^2-c)
    nlinarith [sq_abs (b*v),abs_nonneg (b*v)]
  exact (neg_le_neg hab).trans (neg_abs_le (b*v))

theorem field_young (sigma a R v x : ℝ) (hs : 0<sigma) (ha : 0<a) :
    -a*v^2*weight sigma x-(R^2/(a*sigma))*weight sigma x≤R*v*weightSlope sigma x := by
  have hW : 0≤weight sigma x := by unfold weight; positivity
  have hb : (R*weightSlope sigma x)^2≤4*(a*weight sigma x)*
      ((R^2/(a*sigma))*weight sigma x) := by
    have hh := mul_le_mul_of_nonneg_left (slope_square sigma x hs.le)
      (show 0≤R^2/sigma by positivity)
    have hl : (R^2/sigma)*(sigma*(weightSlope sigma x)^2)=
        (R*weightSlope sigma x)^2 := by field_simp
    have hr : (R^2/sigma)*(4*(weight sigma x)^2)=
        4*(a*weight sigma x)*((R^2/(a*sigma))*weight sigma x) := by
      field_simp [ha.ne']
    rw [hl,hr] at hh
    exact hh
  have ht := scalar_young (a*weight sigma x) (R*weightSlope sigma x)
    ((R^2/(a*sigma))*weight sigma x) v (by positivity) (by positivity) hb
  nlinarith only [ht]

#print axioms slope_square
#print axioms slope_bound
#print axioms field_young
end
end UnifiedTheory.Audit.KFCausalQuarticFieldSlopeBound

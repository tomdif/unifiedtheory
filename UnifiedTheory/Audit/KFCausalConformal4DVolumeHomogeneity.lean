/- Exact coordinate homogeneity of the actual normalized volume, its
parameter slope and the radial Jacobian factor. -/
import UnifiedTheory.Audit.KFCausalConformal4DNormalizedVolume

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DVolumeHomogeneity
noncomputable section
open Real
open KFCausalConformal4DNormalizedVolume

theorem moment_scaling (n : ℕ) (l t r : ℝ) :
    normalizedMoment n (l*t) (l*r)=l^n*normalizedMoment n t r := by
  unfold normalizedMoment
  rw [average_scaling]
  simp only [mul_pow,average_smul]

theorem jacobian_scaling (c l t r : ℝ) :
    jacobianFactor c (l*t) (l*r)=jacobianFactor (c*l^2) t r := by
  unfold jacobianFactor
  rw [average_scaling]
  congr 1
  funext x
  ring

theorem parameter_slope_scaling (c l t r : ℝ) :
    parameterSlope c (l*t) (l*r)=l^2*parameterSlope (c*l^2) t r := by
  unfold parameterSlope
  simp only [moment_scaling]
  ring

theorem normalized_ray_hasDerivAt (c l t r : ℝ) :
    HasDerivAt (fun k => normalized c (k*t) (k*r))
      (2*c*l*parameterSlope (c*l^2) t r) l := by
  have hd := (normalized_hasDerivAt (c*l^2) t r).comp l
    ((hasDerivAt_pow 2 l).const_mul c)
  have he : (fun k => normalized c (k*t) (k*r)) =
      fun k => normalized (c*k^2) t r := funext (fun k => normalized_scaling c k t r)
  rw [he]
  convert hd using 1
  ring

theorem normalized_neg (c t r : ℝ) : normalized c (-t) (-r)=normalized c t r := by
  simpa only [neg_one_mul,neg_one_sq,mul_one] using normalized_scaling c (-1) t r

theorem jacobian_neg (c t r : ℝ) : jacobianFactor c (-t) (-r)=jacobianFactor c t r := by
  simpa only [neg_one_mul,neg_one_sq,mul_one] using jacobian_scaling c (-1) t r

#print axioms moment_scaling
#print axioms jacobian_scaling
#print axioms parameter_slope_scaling
#print axioms normalized_ray_hasDerivAt
#print axioms normalized_neg
#print axioms jacobian_neg
end
end UnifiedTheory.Audit.KFCausalConformal4DVolumeHomogeneity

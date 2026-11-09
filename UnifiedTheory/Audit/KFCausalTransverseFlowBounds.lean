/- Uniform bounds on every transverse direction under the actual shear
flow. These retain the fifth-coordinate mixing terms. -/
import UnifiedTheory.Audit.KFCausalTransverseDerivativeScaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalTransverseFlowBounds
noncomputable section
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseDerivativeScaling

theorem flow_affine (t r : ℝ) (x v : Transverse) :
    flow t (x+r • v)=flow t x+r • flow t v := by
  change (flowEquiv t) (x+r • v)=(flowEquiv t) x+r • (flowEquiv t) v
  rw [map_add,map_smul]

theorem flow_norm_bound (t : ℝ) (v : Transverse) :
    ‖flow t v‖ ≤ 5*(1+scale t)*‖v‖ := by
  have hs : 0 < scale t := Real.exp_pos _
  have hv (i : Fin 5) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hsum : |v 2+v 3| ≤ 2*‖v‖ := (abs_add_le _ _).trans (by linarith [hv 2,hv 3])
  have hsc : |scale t-1| ≤ 1+scale t := abs_le.mpr ⟨by linarith,by linarith⟩
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  by_cases hi : i=4
  · subst i
    rw [flow,if_pos rfl,Real.norm_eq_abs]
    calc
      _ ≤ |v 4|+|2*(scale t-1)*(v 2+v 3)| := abs_add_le _ _
      _ = |v 4|+2*|scale t-1| * |v 2+v 3| := by norm_num [abs_mul]
      _ ≤ ‖v‖+2*(1+scale t)*(2*‖v‖) := by gcongr; exact hv 4
      _ ≤ _ := by nlinarith [mul_nonneg hs.le (norm_nonneg v)]
  · rw [flow,if_neg hi,Real.norm_eq_abs,abs_mul,abs_of_pos hs]
    have hm := mul_le_mul_of_nonneg_left (hv i) hs.le
    nlinarith [norm_nonneg v,mul_nonneg hs.le (norm_nonneg v)]

theorem flow_norm_square_bound (t : ℝ) (v : Transverse) :
    ‖flow (-t) v‖^2 ≤ 50*(1+Real.exp (-t))*‖v‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (flow (-t) v)) (flow_norm_bound (-t) v) 2
  have hb : (1+scale (-t))^2 ≤ 2*(1+(scale (-t))^2) := by nlinarith [sq_nonneg (scale (-t)-1)]
  have hm := mul_le_mul_of_nonneg_right hb (show 0 ≤ 25*‖v‖^2 by positivity)
  rw [scale_square] at hm
  nlinarith

#print axioms flow_affine
#print axioms flow_norm_bound
#print axioms flow_norm_square_bound

end
end UnifiedTheory.Audit.KFCausalTransverseFlowBounds

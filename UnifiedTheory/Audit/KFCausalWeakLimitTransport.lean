/- Transport of weak limits by continuous linear maps, lower norm bounds,
and conversion of squared inverse-cutoff estimates to vanishing norm error. -/
import UnifiedTheory.Audit.KFCausalHilbertWeakSubsequence
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalWeakLimitTransport
noncomputable section
open Filter TopologicalSpace
open scoped Topology

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

omit [InnerProductSpace ℂ H] in
theorem norm_error_tendsto_zero {d : ℕ → H} {a : ℕ → ℝ} {C : ℝ}
    (ha : Tendsto a atTop atTop) (hb : ∀ n, ‖d n‖^2 ≤ C/a n) :
    Tendsto (fun n => ‖d n‖) atTop (𝓝 0) := by
  have hr : Tendsto (fun n => C/a n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using (tendsto_inv_atTop_zero.comp ha).const_mul C
  have hq := squeeze_zero (fun n => sq_nonneg ‖d n‖) hb hr
  have hs := (Real.continuous_sqrt.tendsto 0).comp hq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hs

theorem weak_map [CompleteSpace E] [CompleteSpace H] (J : E →L[ℂ] H) {u : ℕ → E} {x : E}
    (hu : ∀ y, Tendsto (fun n => inner ℂ (u n) y) atTop (𝓝 (inner ℂ x y))) :
    ∀ y, Tendsto (fun n => inner ℂ (J (u n)) y) atTop (𝓝 (inner ℂ (J x) y)) := by
  intro y
  simpa only [ContinuousLinearMap.adjoint_inner_right] using hu (J.adjoint y)

theorem weak_norm_le {u : ℕ → H} {x : H} {C : ℝ}
    (hb : ∀ n, ‖u n‖ ≤ C)
    (hu : ∀ y, Tendsto (fun n => inner ℂ (u n) y) atTop (𝓝 (inner ℂ x y))) : ‖x‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg (u 0)).trans (hb 0)
  have hh : ‖inner ℂ x x‖ ≤ C*‖x‖ := le_of_tendsto (hu x).norm (Filter.Eventually.of_forall
    (fun n => (norm_inner_le_norm (u n) x).trans (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg x))))
  rw [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_norm] at hh
  nlinarith [norm_nonneg x]

#print axioms norm_error_tendsto_zero
#print axioms weak_map
#print axioms weak_norm_le

end
end UnifiedTheory.Audit.KFCausalWeakLimitTransport

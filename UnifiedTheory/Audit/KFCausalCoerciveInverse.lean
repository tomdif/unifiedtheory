/- A coercive symmetric bounded operator on a complex Hilbert space has
a constructed bounded inverse. Surjectivity is proved from closed and
dense range, rather than supplied as an extra assumption. -/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCoerciveInverse
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_lower_bound (A : E →L[ℂ] E) (c : ℝ)
    (hq : ∀ x, c*‖x‖^2 ≤ (inner ℂ (A x) x).re) (x : E) : c*‖x‖ ≤ ‖A x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  apply (mul_le_mul_iff_right₀ hp).mp
  have hi : (inner ℂ (A x) x).re ≤ ‖A x‖*‖x‖ := re_inner_le_norm (𝕜 := ℂ) (A x) x
  nlinarith [hq x]

theorem coercive_antilipschitz (A : E →L[ℂ] E) (c : ℝ) (hc : 0 < c)
    (hq : ∀ x, c*‖x‖^2 ≤ (inner ℂ (A x) x).re) :
    AntilipschitzWith ⟨c⁻¹,(inv_pos.mpr hc).le⟩ A := by
  apply ContinuousLinearMap.antilipschitz_of_bound
  intro x
  exact (le_inv_mul_iff₀ hc).mpr (norm_lower_bound A c hq x)

theorem coercive_ker (A : E →L[ℂ] E) (c : ℝ) (hc : 0 < c)
    (hq : ∀ x, c*‖x‖^2 ≤ (inner ℂ (A x) x).re) : A.ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr (coercive_antilipschitz A c hc hq).injective

variable [CompleteSpace E]

theorem coercive_range (A : E →L[ℂ] E) (c : ℝ) (hc : 0 < c)
    (hq : ∀ x, c*‖x‖^2 ≤ (inner ℂ (A x) x).re)
    (hs : A.toLinearMap.IsSymmetric) : A.range = ⊤ := by
  have hk := coercive_ker A c hc hq
  have hd : Dense (A.range : Set E) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    apply Submodule.topologicalClosure_eq_top_iff.mpr
    rw [hs.orthogonal_range,hk]
  have hr : IsClosed (A.range : Set E) :=
    (coercive_antilipschitz A c hc hq).isClosed_range A.uniformContinuous
  exact SetLike.coe_injective (hr.closure_eq.symm.trans hd.closure_eq)

theorem coercive_isUnit (A : E →L[ℂ] E) (c : ℝ) (hc : 0 < c)
    (hq : ∀ x, c*‖x‖^2 ≤ (inner ℂ (A x) x).re)
    (hs : A.toLinearMap.IsSymmetric) : IsUnit A := by
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  exact ⟨(coercive_antilipschitz A c hc hq).injective,
    LinearMap.range_eq_top.mp (coercive_range A c hc hq hs)⟩

omit [CompleteSpace E] in
theorem inverse_apply_left (A : E →L[ℂ] E) (ha : IsUnit A) (x : E) :
    Ring.inverse A (A x) = x := by
  have h := congrArg (fun T : E →L[ℂ] E => T x) (Ring.inverse_mul_cancel A ha)
  exact h

omit [CompleteSpace E] in
theorem inverse_apply_right (A : E →L[ℂ] E) (ha : IsUnit A) (x : E) :
    A (Ring.inverse A x) = x := by
  have h := congrArg (fun T : E →L[ℂ] E => T x) (Ring.mul_inverse_cancel A ha)
  exact h

theorem inverse_norm_bound (A : E →L[ℂ] E) (c : ℝ) (hc : 0 < c)
    (hq : ∀ x, c*‖x‖^2 ≤ (inner ℂ (A x) x).re)
    (hs : A.toLinearMap.IsSymmetric) : ‖Ring.inverse A‖ ≤ c⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_pos.mpr hc).le
  intro x
  have hb := norm_lower_bound A c hq (Ring.inverse A x)
  rw [inverse_apply_right A (coercive_isUnit A c hc hq hs)] at hb
  exact (le_inv_mul_iff₀ hc).mpr hb

#print axioms norm_lower_bound
#print axioms coercive_range
#print axioms coercive_isUnit
#print axioms inverse_apply_left
#print axioms inverse_apply_right
#print axioms inverse_norm_bound

end
end UnifiedTheory.Audit.KFCausalCoerciveInverse

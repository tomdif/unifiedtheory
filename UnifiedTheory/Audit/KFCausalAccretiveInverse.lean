/- Coercivity of the real diagonal suffices for bounded invertibility;
self-adjointness is not required. The adjoint has the same real diagonal. -/
import UnifiedTheory.Audit.KFCausalCoerciveInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalAccretiveInverse
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalCoerciveInverse
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem adjoint_real_diagonal (A : E →L[ℂ] E) (x : E) :
    (inner ℂ (A.adjoint x) x).re = (inner ℂ (A x) x).re := by
  rw [A.adjoint_inner_left]
  exact inner_re_symm (𝕜 := ℂ) _ _

theorem coercive_range (A : E →L[ℂ] E) (c : ℝ) (hc : 0 < c)
    (hq : ∀ x, c*‖x‖^2 ≤ (inner ℂ (A x) x).re) : A.range = ⊤ := by
  have hk : A.adjoint.ker = ⊥ := coercive_ker A.adjoint c hc
    (fun x => (hq x).trans_eq (adjoint_real_diagonal A x).symm)
  have hd : Dense (A.range : Set E) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    apply Submodule.topologicalClosure_eq_top_iff.mpr
    rw [ContinuousLinearMap.orthogonal_range,hk]
  have hr : IsClosed (A.range : Set E) :=
    (coercive_antilipschitz A c hc hq).isClosed_range A.uniformContinuous
  exact SetLike.coe_injective (hr.closure_eq.symm.trans hd.closure_eq)

theorem coercive_isUnit (A : E →L[ℂ] E) (c : ℝ) (hc : 0 < c)
    (hq : ∀ x, c*‖x‖^2 ≤ (inner ℂ (A x) x).re) : IsUnit A := by
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  exact ⟨(coercive_antilipschitz A c hc hq).injective,
    LinearMap.range_eq_top.mp (coercive_range A c hc hq)⟩

theorem inverse_norm (A : E →L[ℂ] E) (c : ℝ) (hc : 0 < c)
    (hq : ∀ x, c*‖x‖^2 ≤ (inner ℂ (A x) x).re) : ‖Ring.inverse A‖ ≤ c⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_pos.mpr hc).le
  intro x
  have hb := norm_lower_bound A c hq (Ring.inverse A x)
  rw [inverse_apply_right A (coercive_isUnit A c hc hq)] at hb
  exact (le_inv_mul_iff₀ hc).mpr hb

#print axioms adjoint_real_diagonal
#print axioms coercive_range
#print axioms coercive_isUnit
#print axioms inverse_norm
end
end UnifiedTheory.Audit.KFCausalAccretiveInverse

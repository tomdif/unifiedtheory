/- The physical mass pairing on a Hilbert form space. An injective
embedding gives a positive injective Gram operator with dense range. -/
import UnifiedTheory.Audit.KFCausalBoundedFormCurve
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalMassGram
noncomputable section
open UnifiedTheory.Audit.KFCausalBoundedFormCurve

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem gram_left_pairing (J : E →L[ℂ] H) (x y : E) :
    inner ℂ (gram J x) y = inner ℂ (J x) (J y) := J.adjoint_inner_left y (J x)

theorem gram_right_pairing (J : E →L[ℂ] H) (x y : E) :
    inner ℂ x (gram J y) = inner ℂ (J x) (J y) := J.adjoint_inner_right x (J y)

theorem gram_inner_symm (J : E →L[ℂ] H) (x y : E) :
    inner ℂ (gram J x) y = inner ℂ x (gram J y) := by rw [gram_left_pairing,gram_right_pairing]

theorem gram_adjoint (J : E →L[ℂ] H) : (gram J).adjoint = gram J := by
  simp [gram,ContinuousLinearMap.adjoint_comp]

theorem gram_injective (J : E →L[ℂ] H) (hj : Function.Injective J) : Function.Injective (gram J) := by
  intro x y h
  apply hj
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have hh : gram J (x-y) = 0 := by rw [map_sub,h,sub_self]
  rw [← map_sub,← gram_left_pairing,hh,inner_zero_left]

theorem gram_dense (J : E →L[ℂ] H) (hj : Function.Injective J) : DenseRange (gram J) := by
  change Dense ((gram J).range : Set E)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  rw [ContinuousLinearMap.orthogonal_range,gram_adjoint]
  exact LinearMap.ker_eq_bot.mpr (gram_injective J hj)

omit [CompleteSpace E] in
theorem norm_le_of_inner_bound (x : E) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ y, ‖inner ℂ x y‖ ≤ C*‖y‖) : ‖x‖ ≤ C := by
  have hh := hb x
  rw [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_norm] at hh
  nlinarith [norm_nonneg x]

#print axioms gram_left_pairing
#print axioms gram_inner_symm
#print axioms gram_injective
#print axioms gram_dense
#print axioms norm_le_of_inner_bound

end
end UnifiedTheory.Audit.KFCausalMassGram

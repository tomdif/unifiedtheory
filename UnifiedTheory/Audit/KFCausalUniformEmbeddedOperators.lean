/- Uniform form-space operator bounds and their transfer to physical norm. -/
import UnifiedTheory.Audit.KFCausalEmbeddedAdjointBound
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalUniformEmbeddedOperators
noncomputable section
open Set
variable {V H ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem uniform_opNorm [CompleteSpace V] (F : ι → V →L[ℂ] V)
    (h : ∀ x, ∃ C : ℝ, ∀ t, ‖F t x‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖F t‖ ≤ C := by
  obtain ⟨C,hC⟩ := banach_steinhaus h
  exact ⟨max C 0,le_max_right _ _,fun t => (hC t).trans (le_max_left _ _)⟩

omit [InnerProductSpace ℂ V] in
theorem compact_pointwise (I : Set ℝ) (hI : IsCompact I) (f : ℝ → V → V)
    (hc : ∀ x, ContinuousOn (fun t => f t x) I) :
    ∀ x, ∃ C : ℝ, ∀ t : I, ‖f t x‖ ≤ C := by
  intro x
  obtain ⟨C,hC⟩ := hI.exists_bound_of_continuousOn (hc x)
  exact ⟨C,fun t => hC t t.property⟩

theorem compact_norm_bound {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (hI : IsCompact I) (f : ℝ → E) (hc : ContinuousOn f I) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : I, ‖f t‖ ≤ C := by
  obtain ⟨C,hC⟩ := hI.exists_bound_of_continuousOn hc
  exact ⟨max C 0,le_max_right _ _,fun t => (hC t t.property).trans (le_max_left _ _)⟩

theorem embedded_opNorm (J : V →L[ℂ] H) (hJ : DenseRange J) (T S : V →L[ℂ] V)
    (E : H →L[ℂ] H) (hpair : ∀ x y, inner ℂ (J (T x)) (J y) = inner ℂ (J x) (J (S y)))
    (he : ∀ x, E (J x) = J (T x)) (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hT : ‖T‖ ≤ B) (hS : ‖S‖ ≤ C) : ‖E‖ ≤ Real.sqrt (C*B) := by
  have hn (x : V) : ‖E (J x)‖ ≤ Real.sqrt (C*B)*‖J x‖ := by
    rw [he]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hC hB)]
    exact (KFCausalEmbeddedAdjointBound.adjoint_pair_bound J T S hpair x).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul hS hT (norm_nonneg _) hC) (sq_nonneg _))
  have hc : IsClosed {x : H | ‖E x‖ ≤ Real.sqrt (C*B)*‖x‖} :=
    isClosed_le E.continuous.norm (continuous_const.mul continuous_norm)
  have hi : range J ⊆ {x : H | ‖E x‖ ≤ Real.sqrt (C*B)*‖x‖} := by
    rintro x ⟨v,rfl⟩
    exact hn v
  exact E.opNorm_le_bound (Real.sqrt_nonneg _) (fun x => closure_minimal hi hc (hJ x))

theorem adjoint_composition_bound [CompleteSpace V] (P F A : V →L[ℂ] V)
    (B C : ℝ) (hB : 0 ≤ B) (hF : ‖F‖ ≤ B) (hA : ‖A‖ ≤ C) :
    ‖P*F.adjoint*A‖ ≤ ‖P‖*B*C := by
  have hadj : ‖F.adjoint‖ = ‖F‖ := ContinuousLinearMap.adjoint.norm_map F
  calc
    ‖P*F.adjoint*A‖ ≤ ‖P*F.adjoint‖*‖A‖ := norm_mul_le _ _
    _ ≤ (‖P‖*‖F.adjoint‖)*‖A‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = (‖P‖*‖F‖)*‖A‖ := by rw [hadj]
    _ ≤ (‖P‖*B)*C := mul_le_mul
      (mul_le_mul_of_nonneg_left hF (norm_nonneg _)) hA (norm_nonneg _) (mul_nonneg (norm_nonneg _) hB)

#print axioms uniform_opNorm
#print axioms compact_pointwise
#print axioms compact_norm_bound
#print axioms embedded_opNorm
#print axioms adjoint_composition_bound
end
end UnifiedTheory.Audit.KFCausalUniformEmbeddedOperators

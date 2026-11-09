/- Extend an embedded operator with a bounded physical adjoint, then pass
an exact closed graph identity from the dense embedding to the full space. -/
import UnifiedTheory.Audit.KFCausalEmbeddedAdjointBound
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalEmbeddedGraphExtension
noncomputable section
open Set
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_extension (J : V →L[ℂ] H) (hJ : DenseRange J) (T S : V →L[ℂ] V)
    (hpair : ∀ x y, inner ℂ (J (T x)) (J y) = inner ℂ (J x) (J (S y))) :
    ∃ E : H →L[ℂ] H, ∀ x, E (J x) = J (T x) := by
  have hn (x : V) : ‖J (T x)‖ ≤ Real.sqrt (‖S‖*‖T‖)*‖J x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact KFCausalEmbeddedAdjointBound.adjoint_pair_bound J T S hpair x
  let f := J.toLinearMap.comp T.toLinearMap
  exact ⟨f.extendOfNorm J.toLinearMap,fun x =>
    LinearMap.extendOfNorm_eq hJ ⟨Real.sqrt (‖S‖*‖T‖),hn⟩ x⟩

omit [CompleteSpace H] in
theorem closed_graph_extension (J : V →L[ℂ] H) (hJ : DenseRange J)
    (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (P E : H →L[ℂ] H)
    (hg : ∀ v, (P (J v),E (J v)) ∈ T.graph) : ∀ f, (P f,E f) ∈ T.graph := by
  have hc : IsClosed {f : H | (P f,E f) ∈ T.graph} :=
    hT.preimage (P.continuous.prodMk E.continuous)
  have hi : range J ⊆ {f : H | (P f,E f) ∈ T.graph} := by
    rintro f ⟨v,rfl⟩
    exact hg v
  intro f
  exact closure_minimal hi hc (hJ f)

omit [CompleteSpace H] in
theorem domain_of_resolvent (T₀ T₁ : H →ₗ.[ℂ] H) (U R E : H →L[ℂ] H) (a : ℝ)
    (hleft : ∀ x : T₀.domain, R (a • (x:H)+T₀ x) = (x:H))
    (hg : ∀ f, (U (R f),E f) ∈ T₁.graph) (x : T₀.domain) : U x ∈ T₁.domain := by
  have hd := LinearPMap.mem_domain_of_mem_graph (hg (a • (x:H)+T₀ x))
  simpa only [hleft] using hd

omit [CompleteSpace H] in
theorem exists_output_bound (T₀ T₁ : H →ₗ.[ℂ] H) (U R E : H →L[ℂ] H)
    (hleft : ∀ x : T₀.domain, R ((x:H)+T₀ x) = (x:H))
    (hg : ∀ f, (U (R f),E f) ∈ T₁.graph) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : T₀.domain, ∃ hx : U x ∈ T₁.domain,
      ‖T₁ ⟨U x,hx⟩‖ ≤ C*(‖(x:H)‖+‖T₀ x‖) := by
  refine ⟨‖E‖,norm_nonneg _,fun x => ?_⟩
  have hp : (U x,E ((x:H)+T₀ x)) ∈ T₁.graph := by simpa only [hleft] using hg ((x:H)+T₀ x)
  have hx : U x ∈ T₁.domain := LinearPMap.mem_domain_of_mem_graph hp
  refine ⟨hx,?_⟩
  have he : T₁ ⟨U x,hx⟩ = E ((x:H)+T₀ x) :=
    T₁.mem_graph_snd_inj' (T₁.mem_graph ⟨U x,hx⟩) hp rfl
  rw [he]
  exact (E.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _))

#print axioms exists_extension
#print axioms closed_graph_extension
#print axioms domain_of_resolvent
#print axioms exists_output_bound
end
end UnifiedTheory.Audit.KFCausalEmbeddedGraphExtension

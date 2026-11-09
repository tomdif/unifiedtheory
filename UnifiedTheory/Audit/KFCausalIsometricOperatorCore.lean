/- Transport an operator on an invariant pre-Hilbert domain through an
isometric embedding, retaining its actual domain and graph. -/
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalIsometricOperatorCore
noncomputable section
variable {D H : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def rangeEquiv (J : D →ₗᵢ[ℂ] H) : D ≃ₗ[ℂ] J.toLinearMap.range :=
  LinearEquiv.ofInjective J.toLinearMap J.injective

def core (J : D →ₗᵢ[ℂ] H) (T : D →ₗ[ℂ] D) : H →ₗ.[ℂ] H where
  domain := J.toLinearMap.range
  toFun := J.toLinearMap.comp (T.comp (rangeEquiv J).symm.toLinearMap)

theorem core_graph (J : D →ₗᵢ[ℂ] H) (T : D →ₗ[ℂ] D) (u : D) :
    (J u, J (T u)) ∈ (core J T).graph := by
  have hg := (core J T).mem_graph (rangeEquiv J u)
  change (J u, J (T ((rangeEquiv J).symm (rangeEquiv J u)))) ∈ _ at hg
  rwa [LinearEquiv.symm_apply_apply] at hg

theorem symmetric (J : D →ₗᵢ[ℂ] H) (T : D →ₗ[ℂ] D)
    (hs : ∀ u v, inner ℂ (T u) v = inner ℂ u (T v)) :
    (core J T).IsFormalAdjoint (core J T) := by
  intro u v
  obtain ⟨x, rfl⟩ := (rangeEquiv J).surjective u
  obtain ⟨y, rfl⟩ := (rangeEquiv J).surjective v
  change inner ℂ (J (T ((rangeEquiv J).symm (rangeEquiv J x)))) (J y) =
    inner ℂ (J x) (J (T ((rangeEquiv J).symm (rangeEquiv J y))))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    J.inner_map_map, J.inner_map_map]
  exact hs x y

#print axioms core_graph
#print axioms symmetric
end
end UnifiedTheory.Audit.KFCausalIsometricOperatorCore

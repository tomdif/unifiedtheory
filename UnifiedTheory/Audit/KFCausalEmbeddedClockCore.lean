/- The bounded inverse of a clock identifies its form-composition domain.
Strong residual decay supplies explicit approximants in this domain. -/
import UnifiedTheory.Audit.KFCausalInvariantRangeCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalEmbeddedClockCore
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalInvariantRangeCore
variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem clock_range_iff (J : V →L[ℂ] H) (F : V →L[ℂ] V) (D : H →L[ℂ] H)
    (C : H →ₗ.[ℂ] H) (c : ℂ) (hc : c ≠ 0) (hJ : Function.Injective J)
    (hF : ∀ u, J (F u) = D (J u))
    (hCD : ∀ f, (D f,c • f) ∈ C.graph)
    (hDC : ∀ f g, (f,g) ∈ C.graph → D g = c • f) (u : V) :
    u ∈ Set.range F ↔ ∃ v : V, (J u,J v) ∈ C.graph := by
  constructor
  · rintro ⟨w,rfl⟩
    refine ⟨c • w,?_⟩
    simpa only [map_smul,hF] using hCD (J w)
  · rintro ⟨v,hv⟩
    refine ⟨c⁻¹ • v,hJ ?_⟩
    rw [hF,map_smul,map_smul,hDC _ _ hv,smul_smul,inv_mul_cancel₀ hc,one_smul]

theorem range_dense (F : V →L[ℂ] V)
    (hdec : ∀ u, Tendsto (fun n : ℕ => (residual F : V → V)^[n] u) atTop (𝓝 0)) :
    Dense (Set.range F) := by
  intro u
  apply isClosed_closure.mem_of_tendsto (approximation_tendsto F u (hdec u))
  exact Filter.Eventually.of_forall (fun n => subset_closure ⟨geometricSum F u n,rfl⟩)

theorem approximation (F : V →L[ℂ] V)
    (hdec : ∀ u, Tendsto (fun n : ℕ => (residual F : V → V)^[n] u) atTop (𝓝 0)) (u : V) :
    (∀ n, F (geometricSum F u n) ∈ Set.range F) ∧
      Tendsto (fun n => F (geometricSum F u n)) atTop (𝓝 u) :=
  ⟨fun n => ⟨geometricSum F u n,rfl⟩,approximation_tendsto F u (hdec u)⟩

#print axioms clock_range_iff
#print axioms range_dense
#print axioms approximation
end
end UnifiedTheory.Audit.KFCausalEmbeddedClockCore

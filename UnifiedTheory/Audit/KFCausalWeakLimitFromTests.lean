/- Weak compactness and Cauchy convergence on embedded form tests determine
a unique weak limit in the full form space. No closed-range assumption on
the embedding is required. -/
import UnifiedTheory.Audit.KFCausalWeakLimitTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalWeakLimitFromTests
noncomputable section
open Filter TopologicalSpace
open scoped Topology
open UnifiedTheory.Audit.KFCausalHilbertWeakSubsequence
open UnifiedTheory.Audit.KFCausalWeakLimitTransport

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem embedded_tests_separate (J : E →L[ℂ] H) (hj : Function.Injective J) {x z : E}
    (he : ∀ v, inner ℂ (J x) (J v) = inner ℂ (J z) (J v)) : x = z := by
  apply hj
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have hh := he (x-z)
  rw [map_sub] at hh
  rw [inner_sub_left,hh,sub_self]

theorem exists_weak_limit_of_test_cauchy [CompleteSpace E] [CompleteSpace H] [SeparableSpace E]
    (J : E →L[ℂ] H) (hj : Function.Injective J) (u : ℕ → E) (C : ℝ)
    (hb : ∀ n, ‖u n‖ ≤ C)
    (hc : ∀ v, CauchySeq (fun n => inner ℂ (J (u n)) (J v))) :
    ∃ x : E, ‖x‖ ≤ C ∧ ∀ y, Tendsto (fun n => inner ℂ (u n) y) atTop (𝓝 (inner ℂ x y)) := by
  obtain ⟨x,hx,φ,hφ,hlim⟩ := bounded_weak_subsequence u C hb
  have htest (v : E) : Tendsto (fun n => inner ℂ (J (u n)) (J v)) atTop
      (𝓝 (inner ℂ (J x) (J v))) :=
    tendsto_nhds_of_cauchySeq_of_subseq (hc v) hφ.tendsto_atTop ((weak_map J hlim) (J v))
  refine ⟨x,hx,?_⟩
  intro y
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨z,_,ψ,hψ,hz⟩ := bounded_weak_subsequence (fun n => u (ns n)) C (fun n => hb (ns n))
  have he : x = z := embedded_tests_separate J hj (fun v =>
    tendsto_nhds_unique (((htest v).comp hns).comp hψ.tendsto_atTop) ((weak_map J hz) (J v)))
  exact ⟨ψ,by simpa only [← he] using hz y⟩

#print axioms embedded_tests_separate
#print axioms exists_weak_limit_of_test_cauchy

end
end UnifiedTheory.Audit.KFCausalWeakLimitFromTests

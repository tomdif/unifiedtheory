/- Strong state convergence and bounded generator outputs preserve a
resolvent graph through weak compactness. No strong output limit is assumed. -/
import UnifiedTheory.Audit.KFCausalHilbertWeakSubsequence
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalWeakResolventGraphLimit
noncomputable section
open Set Filter Topology TopologicalSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem weak_image (R : V →L[ℂ] V) (u : ℕ → V) (x : V)
    (hu : ∀ z, Tendsto (fun n => inner ℂ (u n) z) atTop (𝓝 (inner ℂ x z))) :
    ∀ z, Tendsto (fun n => inner ℂ (R (u n)) z) atTop (𝓝 (inner ℂ (R x) z)) := by
  intro z
  simpa only [← R.adjoint_inner_right] using hu (R.adjoint z)

theorem graph_limit (T : V →ₗ.[ℂ] V) (R : V →L[ℂ] V) (lam : ℝ)
    (hR : ∀ f, (R f,lam • R f-f) ∈ T.graph)
    (hleft : ∀ x y, (x,y) ∈ T.graph → R (lam • x-y) = x)
    (u v : ℕ → V) (x y : V) (hg : ∀ n, (u n,v n) ∈ T.graph)
    (hu : Tendsto u atTop (𝓝 x))
    (hv : ∀ z, Tendsto (fun n => inner ℂ (v n) z) atTop (𝓝 (inner ℂ y z))) :
    (x,y) ∈ T.graph := by
  have hweak : ∀ z, Tendsto (fun n => inner ℂ (lam • u n-v n) z) atTop
      (𝓝 (inner ℂ (lam • x-y) z)) := by
    intro z
    simpa only [inner_sub_left] using
      (((hu.const_smul lam).inner (𝕜 := ℂ) (tendsto_const_nhds (x := z))).sub (hv z))
  have he : R (lam • x-y) = x := by
    apply ext_inner_right ℂ
    intro z
    apply tendsto_nhds_unique (weak_image R (fun n => lam • u n-v n) (lam • x-y) hweak z)
    simpa only [hleft _ _ (hg _)] using hu.inner (𝕜 := ℂ) (tendsto_const_nhds (x := z))
  have hy : lam • x-(lam • x-y) = y := by abel
  simpa only [he,hy] using hR (lam • x-y)

theorem bounded_graph_limit [SeparableSpace V]
    (T : V →ₗ.[ℂ] V) (R : V →L[ℂ] V) (lam : ℝ)
    (hR : ∀ f, (R f,lam • R f-f) ∈ T.graph)
    (hleft : ∀ x y, (x,y) ∈ T.graph → R (lam • x-y) = x)
    (u v : ℕ → V) (x : V) (C : ℝ) (hg : ∀ n, (u n,v n) ∈ T.graph)
    (hu : Tendsto u atTop (𝓝 x)) (hv : ∀ᶠ n in atTop, ‖v n‖ ≤ C) :
    ∃ y : V, ‖y‖ ≤ C ∧ (x,y) ∈ T.graph := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hv
  obtain ⟨y,hy,phi,hphi,hweak⟩ := KFCausalHilbertWeakSubsequence.bounded_weak_subsequence
    (fun n => v (n+N)) C (fun n => hN (n+N) (Nat.le_add_left N n))
  have hshift : Tendsto (fun n : ℕ => n+N) atTop atTop := tendsto_add_atTop_nat N
  exact ⟨y,hy,graph_limit T R lam hR hleft
    (fun n => u (phi n+N)) (fun n => v (phi n+N)) x y
    (fun n => hg (phi n+N)) (hu.comp (hshift.comp hphi.tendsto_atTop)) hweak⟩

#print axioms weak_image
#print axioms graph_limit
#print axioms bounded_graph_limit
end
end UnifiedTheory.Audit.KFCausalWeakResolventGraphLimit

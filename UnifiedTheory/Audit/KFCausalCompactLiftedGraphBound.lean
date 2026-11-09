/- Transfer a uniformly bounded coordinate graph to the moving lifted graph
through the exact mass identity and continuous coordinate coefficients. -/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCompactLiftedGraphBound
noncomputable section
open Set
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem mass_graph (M Q S D : V →L[ℂ] V) (G L : V →ₗ.[ℂ] V)
    (c : ℂ) (hc : c ≠ 0) (hL : ∀ x y, (x,y) ∈ L.graph ↔ Q x = M y)
    (hm : ∀ x : G.domain, M (S (G x)+D x) = c • Q (S x))
    (x y : V) (hg : (x,y) ∈ G.graph) :
    (S x,c⁻¹ • (S y+D x)) ∈ L.graph := by
  have hx : x ∈ G.domain := LinearPMap.mem_domain_of_mem_graph hg
  have hy : G ⟨x,hx⟩ = y := G.mem_graph_snd_inj' (G.mem_graph ⟨x,hx⟩) hg rfl
  have he : M (S y+D x) = c • Q (S x) := by simpa only [hy] using hm ⟨x,hx⟩
  apply (hL _ _).mpr
  rw [map_smul,he,smul_smul,inv_mul_cancel₀ hc,one_smul]

theorem compact_transfer (G L : ℝ → V →ₗ.[ℂ] V) (S D : ℝ → V →L[ℂ] V)
    (u : ℝ → V) (c : ℂ) (I : Set ℝ) (hI : IsCompact I)
    (hS : ContinuousOn S I) (hD : ContinuousOn D I) (hu : ContinuousOn u I)
    (htrans : ∀ t ∈ I, ∀ x y, (x,y) ∈ (G t).graph →
      (S t x,c⁻¹ • (S t y+D t x)) ∈ (L t).graph)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ I, ∃ v, ‖v‖ ≤ C ∧ (u t,v) ∈ (G t).graph) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ I, ∃ v, ‖v‖ ≤ B ∧ (S t (u t),v) ∈ (L t).graph := by
  obtain ⟨C,hC,hv⟩ := hb
  obtain ⟨B₀,hB₀⟩ := hI.exists_bound_of_continuousOn hS
  obtain ⟨B₁,hB₁⟩ := hI.exists_bound_of_continuousOn hD
  obtain ⟨B₂,hB₂⟩ := hI.exists_bound_of_continuousOn hu
  let N₀ := max B₀ 0
  let N₁ := max B₁ 0
  let N₂ := max B₂ 0
  have hn₀ : 0 ≤ N₀ := le_max_right _ _
  have hn₁ : 0 ≤ N₁ := le_max_right _ _
  have hn₂ : 0 ≤ N₂ := le_max_right _ _
  refine ⟨‖c⁻¹‖*(N₀*C+N₁*N₂),by positivity,?_⟩
  intro t ht
  obtain ⟨v,hvn,hvg⟩ := hv t ht
  refine ⟨c⁻¹ • (S t v+D t (u t)),?_,htrans t ht (u t) v hvg⟩
  rw [norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact ((S t).le_opNorm v).trans (mul_le_mul
      ((hB₀ t ht).trans (le_max_left _ _)) hvn (norm_nonneg _) hn₀)
  · exact ((D t).le_opNorm (u t)).trans (mul_le_mul
      ((hB₁ t ht).trans (le_max_left _ _)) ((hB₂ t ht).trans (le_max_left _ _))
      (norm_nonneg _) hn₁)

theorem normalize_initial (G : ℝ → V →ₗ.[ℂ] V) (S R : ℝ → V →L[ℂ] V)
    (F : ℝ → V → V) (l r : ℝ) (hinit : S l = 1)
    (hb : ∀ x y, (x,y) ∈ (G l).graph → ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc l r,
      ∃ v, ‖v‖ ≤ C ∧ (R t (F t (S l x)),v) ∈ (G t).graph)
    (x : (G l).domain) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc l r, ∃ v, ‖v‖ ≤ C ∧ (R t (F t x),v) ∈ (G t).graph := by
  simpa only [hinit,ContinuousLinearMap.one_apply] using hb x (G l x) ((G l).mem_graph x)

theorem remove_inverse (L : ℝ → V →ₗ.[ℂ] V) (S R : ℝ → V →L[ℂ] V)
    (u : ℝ → V) (I : Set ℝ) (hi : ∀ t, S t (R t (u t)) = u t)
    (hb : ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ I, ∃ v, ‖v‖ ≤ B ∧ (S t (R t (u t)),v) ∈ (L t).graph) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ I, ∃ v, ‖v‖ ≤ B ∧ (u t,v) ∈ (L t).graph := by
  simpa only [hi] using hb

theorem on_subtype (L : ℝ → V →ₗ.[ℂ] V) (u : ℝ → V) (I : Set ℝ)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ I, ∃ v, ‖v‖ ≤ C ∧ (u t,v) ∈ (L t).graph) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : I, ∃ v, ‖v‖ ≤ C ∧ (u t,v) ∈ (L t).graph := by
  obtain ⟨C,hC,hv⟩ := hb
  exact ⟨C,hC,fun t => hv t t.property⟩

#print axioms mass_graph
#print axioms compact_transfer
#print axioms normalize_initial
#print axioms remove_inverse
#print axioms on_subtype
end
end UnifiedTheory.Audit.KFCausalCompactLiftedGraphBound

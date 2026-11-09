/- Resolvent identities under a bounded domain identification, before
the bounded connection is incorporated by a Neumann inverse. -/
import UnifiedTheory.Audit.KFCausalMassFormOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalConjugatedPartialResolvent
noncomputable section
open UnifiedTheory.Audit.KFCausalMassFormOperator (graph_domain_iff)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def conjugated (S U R : V →L[ℂ] V) : V →L[ℂ] V := U*(R*S)

theorem action_from_transport (S C D : V →L[ℂ] V) (c : ℂ) (w g z : V)
    (hc : S (C w) = -D w) (he : S g+D w = c • z) : S (g-C w) = c • z := by
  rw [map_sub,hc,sub_neg_eq_add]
  exact he

theorem graph_unique (T : V →ₗ.[ℂ] V) (x y z : V)
    (hy : (x,y) ∈ T.graph) (hz : (x,z) ∈ T.graph) : y = z := by
  obtain ⟨hx,he⟩ := (graph_domain_iff T x y).mp hy
  obtain ⟨_,hf⟩ := (graph_domain_iff T x z).mp hz
  exact he.symm.trans hf

theorem conjugated_graph (T G : V →ₗ.[ℂ] V) (S U C : V →L[ℂ] V) (c : ℂ)
    (hi : ∀ x, U (S x) = x)
    (hd : ∀ x, S x ∈ T.domain ↔ x ∈ G.domain)
    (ha : ∀ x : G.domain, ∃ z, (S x,z) ∈ T.graph ∧ S (G x-C x) = c • z)
    (x z : V) (hz : (S x,z) ∈ T.graph) :
    (x,U (c • z)+C x) ∈ G.graph := by
  have hx := (hd x).mp (LinearPMap.mem_domain_of_mem_graph hz)
  obtain ⟨v,hv,he⟩ := ha ⟨x,hx⟩
  have hvz := graph_unique T (S x) v z hv hz
  apply (graph_domain_iff G x _).mpr
  refine ⟨hx,?_⟩
  have he' := congrArg (fun w : V => U w) he
  dsimp only at he'
  rw [hi,hvz] at he'
  exact eq_add_of_sub_eq he'

theorem conjugated_resolvent_graph (T G : V →ₗ.[ℂ] V) (S U C R : V →L[ℂ] V)
    (c : ℂ) (b : ℝ) (out : V → V)
    (hi : ∀ x, S (U x) = x) (hr : ∀ x, U (S x) = x)
    (hg : ∀ x z, (S x,z) ∈ T.graph → (x,U (c • z)+C x) ∈ G.graph)
    (hR : ∀ f, (R f,out f) ∈ T.graph)
    (he : ∀ f, b • R f-c • out f = f) (f : V) :
    (conjugated S U R f,b • conjugated S U R f-f+C (conjugated S U R f)) ∈ G.graph := by
  have h := hg (U (R (S f))) (out (S f)) (by rw [hi]; exact hR (S f))
  have hval : U (c • out (S f)) = b • U (R (S f))-f := by
    have h := congrArg (fun w : V => U w) (he (S f))
    dsimp only at h
    rw [map_sub,ContinuousLinearMap.map_smul_of_tower,hr] at h
    exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp h).symm)
  simpa only [hval] using h

theorem conjugated_resolvent_left (T G : V →ₗ.[ℂ] V) (S U C R : V →L[ℂ] V)
    (c : ℂ) (b : ℝ) (hr : ∀ x, U (S x) = x)
    (ha : ∀ x : G.domain, ∃ z, (S x,z) ∈ T.graph ∧ S (G x-C x) = c • z)
    (hl : ∀ x : T.domain, R (b • (x:V)-c • T x) = (x:V)) (x : G.domain) :
    conjugated S U R (b • (x:V)-G x+C x) = (x:V) := by
  obtain ⟨z,hz,he⟩ := ha x
  obtain ⟨hx,hval⟩ := (graph_domain_iff T (S x) z).mp hz
  have hleft : R (b • S x-c • z) = S x := by simpa only [hval] using hl ⟨S x,hx⟩
  have hs : S (b • (x:V)-G x+C x) = b • S x-c • z := by
    rw [← he]
    simp only [map_sub,map_add,ContinuousLinearMap.map_smul_of_tower]
    abel
  change U (R (S (b • (x:V)-G x+C x))) = _
  rw [hs,hleft,hr]

theorem conjugated_norm_bound (S U R : V →L[ℂ] V) (b K : ℝ)
    (hb : 0 < b) (hK : 0 ≤ K) (hR : ∀ f, ‖b • R f‖ ≤ K*‖f‖) (f : V) :
    ‖conjugated S U R f‖ ≤ (‖U‖*K*‖S‖)/b*‖f‖ := by
  have hr (v : V) : ‖R v‖ ≤ K/b*‖v‖ := by
    have he := hR v
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hb] at he
    rw [div_mul_eq_mul_div,le_div_iff₀ hb]
    nlinarith only [he]
  calc
    _ ≤ ‖U‖*‖R (S f)‖ := U.le_opNorm _
    _ ≤ ‖U‖*(K/b*‖S f‖) := mul_le_mul_of_nonneg_left (hr _) (norm_nonneg _)
    _ ≤ ‖U‖*(K/b*(‖S‖*‖f‖)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (S.le_opNorm _) (div_nonneg hK hb.le)) (norm_nonneg _)
    _ = _ := by ring

theorem left_of_eq (T G : V →ₗ.[ℂ] V) (S U C R Z : V →L[ℂ] V)
    (c : ℂ) (b : ℝ) (hZ : Z = conjugated S U R) (hr : ∀ x, U (S x) = x)
    (ha : ∀ x : G.domain, ∃ z, (S x,z) ∈ T.graph ∧ S (G x-C x) = c • z)
    (hl : ∀ x : T.domain, R (b • (x:V)-c • T x) = (x:V)) (x : G.domain) :
    Z (b • (x:V)-G x+C x) = (x:V) := by
  rw [hZ]
  exact conjugated_resolvent_left T G S U C R c b hr ha hl x

theorem left_graph_of_eq (T G : V →ₗ.[ℂ] V) (S U C R Z : V →L[ℂ] V)
    (c : ℂ) (b : ℝ) (hZ : Z = conjugated S U R) (hr : ∀ x, U (S x) = x)
    (ha : ∀ x : G.domain, ∃ z, (S x,z) ∈ T.graph ∧ S (G x-C x) = c • z)
    (hl : ∀ x : T.domain, R (b • (x:V)-c • T x) = (x:V))
    (x y : V) (hxy : (x,y) ∈ G.graph) : Z (b • x-y+C x) = x := by
  obtain ⟨hx,hval⟩ := (graph_domain_iff G x y).mp hxy
  simpa only [hval] using left_of_eq T G S U C R Z c b hZ hr ha hl ⟨x,hx⟩

#print axioms graph_unique
#print axioms action_from_transport
#print axioms conjugated_graph
#print axioms conjugated_resolvent_graph
#print axioms conjugated_resolvent_left
#print axioms conjugated_norm_bound
#print axioms left_of_eq
#print axioms left_graph_of_eq
end
end UnifiedTheory.Audit.KFCausalConjugatedPartialResolvent

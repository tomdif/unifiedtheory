/- A closed partially defined operator from an injective mass map and
a bounded form map. No inverse of the mass map on the whole space is assumed. -/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalMassFormOperator
noncomputable section
open Set
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def relation (M Q : V →L[ℂ] V) : Submodule ℂ (V × V) where
  carrier := {p | Q p.1 = M p.2}
  zero_mem' := by simp only [Set.mem_setOf_eq,map_zero,Prod.fst_zero,Prod.snd_zero]
  add_mem' := by
    intro p q hp hq
    change Q (p.1+q.1) = M (p.2+q.2)
    rw [map_add,map_add,hp,hq]
  smul_mem' := by
    intro c p hp
    change Q (c • p.1) = M (c • p.2)
    rw [map_smul,map_smul,hp]

def operator (M Q : V →L[ℂ] V) : V →ₗ.[ℂ] V := (relation M Q).toLinearPMap

theorem operator_graph (M Q : V →L[ℂ] V) (hi : Function.Injective M) :
    (operator M Q).graph = relation M Q := by
  apply Submodule.toLinearPMap_graph_eq
  intro p hp h0
  apply hi
  change Q p.1 = M p.2 at hp
  rw [h0,map_zero] at hp
  exact hp.symm.trans (map_zero M).symm

theorem graph_iff (M Q : V →L[ℂ] V) (hi : Function.Injective M) (w v : V) :
    (w,v) ∈ (operator M Q).graph ↔ Q w = M v := by
  rw [operator_graph M Q hi]
  rfl

theorem domain_iff (M Q : V →L[ℂ] V) (hi : Function.Injective M) (w : V) :
    w ∈ (operator M Q).domain ↔ ∃ v, Q w = M v := by
  rw [LinearPMap.mem_domain_iff]
  exact exists_congr (fun v => graph_iff M Q hi w v)

theorem operator_closed (M Q : V →L[ℂ] V) (hi : Function.Injective M) :
    (operator M Q).IsClosed := by
  change IsClosed ((operator M Q).graph : Set (V × V))
  rw [operator_graph M Q hi]
  exact isClosed_eq (Q.continuous.comp continuous_fst) (M.continuous.comp continuous_snd)

theorem shifted_resolves (M Q P : V →L[ℂ] V) (hi : Function.Injective M) (a : ℝ)
    (hr : ∀ w, a • M (P w)+Q (P w) = w) (f : V) :
    (P (M f),f-a • P (M f)) ∈ (operator M Q).graph := by
  apply (graph_iff M Q hi _ _).mpr
  have hh := hr (M f)
  rw [map_sub,ContinuousLinearMap.map_smul_of_tower]
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans hh)

theorem operator_dense (M Q P : V →L[ℂ] V) (hi : Function.Injective M)
    (hM : DenseRange M) (hP : Function.Surjective P) (a : ℝ)
    (hr : ∀ w, a • M (P w)+Q (P w) = w) :
    Dense ((operator M Q).domain : Set V) := by
  have hd := hP.denseRange.comp hM P.continuous
  apply hd.mono
  rintro w ⟨f,rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph (shifted_resolves M Q P hi a hr f)

theorem graph_domain_iff (T : V →ₗ.[ℂ] V) (x y : V) :
    (x,y) ∈ T.graph ↔ ∃ hx : x ∈ T.domain, T ⟨x,hx⟩ = y := by
  constructor
  · intro hp
    obtain ⟨u,hx,hy⟩ := T.mem_graph_iff.mp hp
    change (u:V) = x at hx
    change T u = y at hy
    subst x
    exact ⟨u.property,hy⟩
  · rintro ⟨hx,hy⟩
    exact T.mem_graph_iff.mpr ⟨⟨x,hx⟩,rfl,hy⟩

theorem transport_relation (M Q₁ Q₂ S : V →L[ℂ] V) (a : ℝ)
    (hs : ∀ w, a • M (S w)+Q₂ (S w) = a • M w+Q₁ w)
    (w v : V) (hw : Q₁ w = M v) :
    Q₂ (S w) = M (v+a • w-a • S w) := by
  have hh := hs w
  rw [hw] at hh
  rw [map_sub,map_add,ContinuousLinearMap.map_smul_of_tower,
    ContinuousLinearMap.map_smul_of_tower]
  apply eq_sub_iff_add_eq.mpr
  exact (add_comm _ _).trans (hh.trans (add_comm _ _))

theorem domain_transport_iff (T₁ T₂ : V →ₗ.[ℂ] V) (S R : V →L[ℂ] V)
    (hs : ∀ w v, (w,v) ∈ T₁.graph → ∃ z, (S w,z) ∈ T₂.graph)
    (hr : ∀ w v, (w,v) ∈ T₂.graph → ∃ z, (R w,z) ∈ T₁.graph)
    (hi : ∀ w, R (S w) = w) (w : V) : S w ∈ T₂.domain ↔ w ∈ T₁.domain := by
  constructor
  · intro hw
    obtain ⟨v,hv⟩ := LinearPMap.mem_domain_iff.mp hw
    obtain ⟨z,hz⟩ := hr (S w) v hv
    rw [hi] at hz
    exact LinearPMap.mem_domain_of_mem_graph hz
  · intro hw
    obtain ⟨v,hv⟩ := LinearPMap.mem_domain_iff.mp hw
    obtain ⟨z,hz⟩ := hs w v hv
    exact LinearPMap.mem_domain_of_mem_graph hz

#print axioms operator_graph
#print axioms graph_iff
#print axioms domain_iff
#print axioms operator_closed
#print axioms shifted_resolves
#print axioms operator_dense
#print axioms graph_domain_iff
#print axioms transport_relation
#print axioms domain_transport_iff
end
end UnifiedTheory.Audit.KFCausalMassFormOperator

/- Resolvent images of a proved dense source space are graph dense for a
closed operator in a reducing sector. Density is taken in the operator graph,
not only in the state Hilbert space. -/
import UnifiedTheory.Audit.KFCausalResolventGraphCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalHamiltonianCoreFromSources
noncomputable section
open Set
open KFCausalPositiveResolventBounds (Resolves)

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def graphMap (R : X →L[ℂ] X) (a : ℝ) : X →L[ℂ] X × X :=
  R.prod (ContinuousLinearMap.id ℂ X-a • R)

theorem graphMap_apply (R : X →L[ℂ] X) (a : ℝ) (f : X) :
    graphMap R a f = (R f,f-a • R f) := rfl

def sectorGraph (T : X →ₗ.[ℂ] X) (K : Submodule ℂ X) : Submodule ℂ (X × X) :=
  T.graph ⊓ K.comap (LinearMap.fst ℂ X X)

theorem sectorGraph_closed (T : X →ₗ.[ℂ] X) (hc : T.IsClosed)
    (K : Submodule ℂ X) (hK : IsClosed (K : Set X)) :
    IsClosed (sectorGraph T K : Set (X × X)) :=
  hc.inter (hK.preimage continuous_fst)

theorem source_graph_closure (T : X →ₗ.[ℂ] X) (R : X →L[ℂ] X) (a : ℝ)
    (hr : Resolves T R a) (hl : ∀ x : T.domain, R (T x+a • (x:X)) = x)
    (hc : T.IsClosed) (K D : Submodule ℂ X) (hK : IsClosed (K : Set X))
    (hd : D.topologicalClosure = K) (hR : ∀ f ∈ K, R f ∈ K)
    (hT : ∀ x : T.domain, (x:X) ∈ K → T x ∈ K) :
    (D.map (graphMap R a).toLinearMap).topologicalClosure = sectorGraph T K := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ _ (sectorGraph_closed T hc K hK)
    rintro p ⟨f,hf,rfl⟩
    obtain ⟨hx,hv⟩ := hr f
    exact ⟨T.mem_graph_iff.mpr ⟨⟨R f,hx⟩,rfl,hv⟩,
      hR f (hd ▸ D.le_topologicalClosure hf)⟩
  · intro p hp
    obtain ⟨x,rfl⟩ := T.mem_graph_iff'.mp hp.1
    have hx : (x:X) ∈ K := hp.2
    have hf : T x+a • (x:X) ∈ D.topologicalClosure := by
      rw [hd]
      exact K.add_mem (hT x hx) ((K.restrictScalars ℝ).smul_mem a hx)
    have hm := Submodule.topologicalClosure_map (graphMap R a) D
      ⟨T x+a • (x:X),hf,rfl⟩
    change (R (T x+a • (x:X)),T x+a • (x:X)-a • R (T x+a • (x:X))) ∈
      (D.map (graphMap R a).toLinearMap).topologicalClosure at hm
    simpa only [hl x,add_sub_cancel_right] using hm

#print axioms graphMap_apply
#print axioms sectorGraph_closed
#print axioms source_graph_closure
end
end UnifiedTheory.Audit.KFCausalHamiltonianCoreFromSources

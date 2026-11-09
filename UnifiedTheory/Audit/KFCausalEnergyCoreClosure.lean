/- A positive algebraic energy factorization has a closed Friedrichs form.
The output need not be dense in the ambient energy space. -/
import UnifiedTheory.Audit.KFCausalSeparatedGraphClosure
import UnifiedTheory.Audit.KFCausalClosedGraphForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalEnergyCoreClosure
noncomputable section
open KFCausalSeparatedGraphClosure

variable {V H K : Type*} [AddCommGroup V] [Module ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem closure_vertical_zero (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K) (T : V →ₗ[ℂ] H)
    (hp : ∀ u v, inner ℂ (O u) (O v) = inner ℂ (T u) (I v))
    (z : H × K) (hz : z ∈ (graphRange I O).topologicalClosure) (hx : z.1 = 0) :
    z.2 = 0 := by
  have ho (v : V) : inner ℂ (O v) z.2 = 0 := by
    simpa only [hx, inner_zero_right] using closure_pairing I O (T v) (O v) (hp v) z hz
  have hc : IsClosed {w : H × K | inner ℂ w.2 z.2 = 0} :=
    isClosed_eq (continuous_snd.inner continuous_const) continuous_const
  have hi : (graphRange I O : Set (H × K)) ⊆ {w | inner ℂ w.2 z.2 = 0} := by
    rintro w ⟨v, rfl⟩
    exact ho v
  have hh : inner ℂ z.2 z.2 = 0 :=
    closure_minimal hi hc
      (by simpa only [Submodule.topologicalClosure_coe] using hz)
  exact inner_self_eq_zero.mp hh

theorem closedOperator_graph (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K) (T : V →ₗ[ℂ] H)
    (hp : ∀ u v, inner ℂ (O u) (O v) = inner ℂ (T u) (I v)) :
    (closedOperator I O).graph = (graphRange I O).topologicalClosure :=
  Submodule.toLinearPMap_graph_eq _ (closure_vertical_zero I O T hp)

theorem core_energy_graph (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K) (T : V →ₗ[ℂ] H)
    (hp : ∀ u v, inner ℂ (O u) (O v) = inner ℂ (T u) (I v)) (v : V) :
    (I v, O v) ∈ (closedOperator I O).graph := by
  rw [closedOperator_graph I O T hp]
  exact (graphRange I O).le_topologicalClosure ⟨v, rfl⟩

def formData (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K) (T : V →ₗ[ℂ] H)
    (hd : DenseRange I) (hp : ∀ u v, inner ℂ (O u) (O v) = inner ℂ (T u) (I v)) :
    KFCausalClosedGraphForm.Data H K where
  operator := closedOperator I O
  closed := by
    rw [LinearPMap.IsClosed, closedOperator_graph I O T hp]
    exact (graphRange I O).isClosed_topologicalClosure
  dense := hd.mono (by
    rintro _ ⟨v, rfl⟩
    exact (closedOperator I O).mem_domain_of_mem_graph (core_energy_graph I O T hp v))

def coreVector (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K) (T : V →ₗ[ℂ] H)
    (hd : DenseRange I) (hp : ∀ u v, inner ℂ (O u) (O v) = inner ℂ (T u) (I v))
    (v : V) : KFCausalClosedGraphForm.FormSpace (formData I O T hd hp) :=
  ⟨WithLp.toLp 2 (I v, O v), core_energy_graph I O T hp v⟩

variable [CompleteSpace H] [CompleteSpace K]

def hamiltonian (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K) (T : V →ₗ[ℂ] H)
    (hd : DenseRange I) (hp : ∀ u v, inner ℂ (O u) (O v) = inner ℂ (T u) (I v)) :
    H →ₗ.[ℂ] H := KFCausalClosedGraphForm.hamiltonian (formData I O T hd hp)

theorem selfAdjoint (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K) (T : V →ₗ[ℂ] H)
    (hd : DenseRange I) (hp : ∀ u v, inner ℂ (O u) (O v) = inner ℂ (T u) (I v)) :
    IsSelfAdjoint (hamiltonian I O T hd hp) :=
  KFCausalClosedGraphForm.hamiltonian_selfAdjoint _

theorem core_graph (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K) (T : V →ₗ[ℂ] H)
    (hd : DenseRange I) (hp : ∀ u v, inner ℂ (O u) (O v) = inner ℂ (T u) (I v))
    (u : V) : (I u, T u) ∈ (hamiltonian I O T hd hp).graph := by
  have hq : ∀ v : KFCausalClosedGraphForm.FormSpace (formData I O T hd hp),
      inner ℂ (O u) (KFCausalClosedGraphForm.energyOutput _ v) =
      inner ℂ (T u) (KFCausalClosedGraphForm.embedding _ v) := by
    intro v
    exact closure_pairing I O (T u) (O u) (hp u) _
      ((closedOperator_graph I O T hp) ▸ v.property)
  obtain ⟨hx, hy⟩ := (KFCausalClosedGraphForm.hamiltonian_domain_characterization
    (formData I O T hd hp) (coreVector I O T hd hp u) (T u)).mpr hq
  rw [LinearPMap.mem_graph_iff]
  exact ⟨⟨I u, hx⟩, rfl, hy⟩

theorem positive (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K) (T : V →ₗ[ℂ] H)
    (hd : DenseRange I) (hp : ∀ u v, inner ℂ (O u) (O v) = inner ℂ (T u) (I v))
    (x : (hamiltonian I O T hd hp).domain) :
    0 ≤ (inner ℂ (hamiltonian I O T hd hp x) (x : H)).re :=
  KFCausalClosedGraphForm.hamiltonian_positive _ x

end
end UnifiedTheory.Audit.KFCausalEnergyCoreClosure

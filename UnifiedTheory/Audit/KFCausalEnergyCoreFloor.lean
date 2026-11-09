/- A lower bound on an algebraic energy core passes to its closed form
and to the full domain of its Friedrichs Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalEnergyCoreClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalEnergyCoreFloor
noncomputable section
open KFCausalSeparatedGraphClosure KFCausalEnergyCoreClosure KFCausalClosedGraphForm

variable {V H K : Type*} [AddCommGroup V] [Module ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K) (T : V →ₗ[ℂ] H)
  (hd : DenseRange I) (hp : ∀ u v, inner ℂ (O u) (O v) = inner ℂ (T u) (I v))
  (δ : ℝ) (hb : ∀ v, δ * ‖I v‖ ^ 2 ≤ ‖O v‖ ^ 2)

include hb in
theorem closure_lower (z : H × K) (hz : z ∈ (graphRange I O).topologicalClosure) :
    δ * ‖z.1‖ ^ 2 ≤ ‖z.2‖ ^ 2 := by
  have hc : IsClosed {w : H × K | δ * ‖w.1‖ ^ 2 ≤ ‖w.2‖ ^ 2} :=
    isClosed_le (continuous_const.mul (continuous_fst.norm.pow 2))
      (continuous_snd.norm.pow 2)
  have hi : (graphRange I O : Set (H × K)) ⊆ {w | δ * ‖w.1‖ ^ 2 ≤ ‖w.2‖ ^ 2} := by
    rintro w ⟨v, rfl⟩
    exact hb v
  exact closure_minimal hi hc (by simpa only [Submodule.topologicalClosure_coe] using hz)

include hb in
theorem form_lower (u : FormSpace (formData I O T hd hp)) :
    δ * ‖embedding (formData I O T hd hp) u‖ ^ 2 ≤
      ‖energyOutput (formData I O T hd hp) u‖ ^ 2 :=
  closure_lower I O δ hb _ ((KFCausalEnergyCoreClosure.closedOperator_graph I O T hp) ▸ u.property)

variable [CompleteSpace H] [CompleteSpace K]

include hb in
theorem hamiltonian_lower (x : (KFCausalEnergyCoreClosure.hamiltonian I O T hd hp).domain) :
    δ * ‖(x : H)‖ ^ 2 ≤
      (inner ℂ (KFCausalEnergyCoreClosure.hamiltonian I O T hd hp x) (x : H)).re := by
  have hf := form_lower I O T hd hp δ hb (formLift (formData I O T hd hp) x)
  rwa [embedding_formLift, ← hamiltonian_energy] at hf

end
end UnifiedTheory.Audit.KFCausalEnergyCoreFloor

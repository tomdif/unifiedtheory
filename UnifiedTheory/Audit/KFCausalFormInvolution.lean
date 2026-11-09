/- Involutive isometries of an energy graph preserve the full variational
Hamiltonian domain and intertwine the self-adjoint operator. -/
import UnifiedTheory.Audit.KFCausalClosedGraphForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalFormInvolution
noncomputable section
open KFCausalClosedGraphForm

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (D : Data H K) (U : H ≃ₗᵢ[ℂ] H) (V : K ≃ₗᵢ[ℂ] K)
  (hg : ∀ z : H × K, z ∈ D.operator.graph → (U z.1, V z.2) ∈ D.operator.graph)

def transform : FormSpace D →ₗ[ℂ] FormSpace D :=
  (((U.withLpProdCongr 2 V).toLinearMap).comp (energyGraph D).subtype).codRestrict
    (energyGraph D) (by intro u; exact hg _ u.property)

theorem embedding_transform (u : FormSpace D) : embedding D (transform D U V hg u) = U (embedding D u) := rfl

theorem output_transform (u : FormSpace D) : energyOutput D (transform D U V hg u) = V (energyOutput D u) := rfl

theorem inner_involution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (W : E ≃ₗᵢ[ℂ] E) (hw : Function.Involutive W) (x y : E) :
    inner ℂ (W x) y = inner ℂ x (W y) := by
  have h := W.inner_map_map x (W y)
  rwa [hw y] at h

include hg in
theorem hamiltonian_graph (hU : Function.Involutive U) (hV : Function.Involutive V)
    (x : (hamiltonian D).domain) :
    (U (x : H), U (hamiltonian D x)) ∈ (hamiltonian D).graph := by
  have hq : ∀ v : FormSpace D,
      inner ℂ (energyOutput D (transform D U V hg (formLift D x))) (energyOutput D v) =
        inner ℂ (U (hamiltonian D x)) (embedding D v) := by
    intro v
    rw [output_transform, inner_involution V hV, inner_involution U hU]
    have hp := hamiltonian_represents_form D x (transform D U V hg v)
    simpa only [output_transform, embedding_transform] using hp
  obtain ⟨hx, hy⟩ := (hamiltonian_domain_characterization D
    (transform D U V hg (formLift D x)) (U (hamiltonian D x))).mpr hq
  rw [LinearPMap.mem_graph_iff]
  refine ⟨⟨_, hx⟩, ?_, hy⟩
  change embedding D (transform D U V hg (formLift D x)) = U (x : H)
  rw [embedding_transform, embedding_formLift]

end
end UnifiedTheory.Audit.KFCausalFormInvolution

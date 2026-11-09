/- An operator graph is closable when continuous pairings with a
separating family transfer to the input. The clock application supplies
these pairings from Fourier Fubini and explicit integrable Gaussians. -/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSeparatedGraphClosure
noncomputable section

variable {V H K J : Type*} [AddCommGroup V] [Module ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def graphRange (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K) : Submodule ℂ (H × K) := (I.prod O).range
def initialOperator (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K) : H →ₗ.[ℂ] K :=
  (graphRange I O).toLinearPMap
def closedOperator (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K) : H →ₗ.[ℂ] K :=
  (graphRange I O).topologicalClosure.toLinearPMap

theorem closure_pairing (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K) (a : H) (b : K)
    (hp : ∀ v, inner ℂ b (O v)=inner ℂ a (I v))
    (z : H × K) (hz : z ∈ (graphRange I O).topologicalClosure) :
    inner ℂ b z.2=inner ℂ a z.1 := by
  have hc : IsClosed {z : H × K | inner ℂ b z.2=inner ℂ a z.1} :=
    isClosed_eq (continuous_const.inner continuous_snd) (continuous_const.inner continuous_fst)
  have hi : (graphRange I O : Set (H × K)) ⊆ {z : H × K | inner ℂ b z.2=inner ℂ a z.1} := by
    rintro z ⟨v,rfl⟩
    exact hp v
  exact closure_minimal hi hc (by simpa only [Submodule.topologicalClosure_coe] using hz)

theorem closure_vertical_zero (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K)
    (a : J → H) (b : J → K)
    (hsep : ∀ y : K, (∀ j, inner ℂ (b j) y=0) → y=0)
    (hp : ∀ v j, inner ℂ (b j) (O v)=inner ℂ (a j) (I v))
    (z : H × K) (hz : z ∈ (graphRange I O).topologicalClosure) (hx : z.1=0) : z.2=0 := by
  apply hsep
  intro j
  simpa only [hx,inner_zero_right] using closure_pairing I O (a j) (b j) (fun v => hp v j) z hz

theorem closedOperator_graph (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K)
    (a : J → H) (b : J → K)
    (hsep : ∀ y : K, (∀ j, inner ℂ (b j) y=0) → y=0)
    (hp : ∀ v j, inner ℂ (b j) (O v)=inner ℂ (a j) (I v)) :
    (closedOperator I O).graph=(graphRange I O).topologicalClosure :=
  Submodule.toLinearPMap_graph_eq _ (closure_vertical_zero I O a b hsep hp)

theorem initialOperator_graph (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K)
    (a : J → H) (b : J → K)
    (hsep : ∀ y : K, (∀ j, inner ℂ (b j) y=0) → y=0)
    (hp : ∀ v j, inner ℂ (b j) (O v)=inner ℂ (a j) (I v)) :
    (initialOperator I O).graph=graphRange I O := by
  apply Submodule.toLinearPMap_graph_eq
  intro z hz hx
  exact closure_vertical_zero I O a b hsep hp z ((graphRange I O).le_topologicalClosure hz) hx

theorem operator_closable (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K)
    (a : J → H) (b : J → K)
    (hsep : ∀ y : K, (∀ j, inner ℂ (b j) y=0) → y=0)
    (hp : ∀ v j, inner ℂ (b j) (O v)=inner ℂ (a j) (I v)) :
    (initialOperator I O).IsClosable := by
  refine ⟨closedOperator I O,?_⟩
  rw [initialOperator_graph I O a b hsep hp,closedOperator_graph I O a b hsep hp]

theorem operator_closed (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K)
    (a : J → H) (b : J → K)
    (hsep : ∀ y : K, (∀ j, inner ℂ (b j) y=0) → y=0)
    (hp : ∀ v j, inner ℂ (b j) (O v)=inner ℂ (a j) (I v)) :
    (closedOperator I O).IsClosed := by
  rw [LinearPMap.IsClosed,closedOperator_graph I O a b hsep hp]
  exact (graphRange I O).isClosed_topologicalClosure

#print axioms closure_vertical_zero
#print axioms operator_closable
#print axioms operator_closed

end
end UnifiedTheory.Audit.KFCausalSeparatedGraphClosure

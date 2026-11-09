/- A mixed vacuum graph transports to two independent charge angles.
The intermediate operator is arbitrary and keeps its natural graph. -/
import UnifiedTheory.Audit.KFCausalSingleGaussianTwoAngleSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalChargeConjugatedInsertion
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (action action_compose action_zero)
open KFCausalClockFloorVacuumSquare (square)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalSingleGaussianTwoAngleSquare (squareAt squareAt_graph)

variable (h : ℝ) (hh : h ≠ 0) (T : Hilbert →ₗ.[ℂ] Hilbert)

def operatorAt (θ : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  (T.graph.comap ((action h hh θ).toLinearMap.prodMap
    (action h hh θ).toLinearMap)).toLinearPMap

theorem operatorAt_graph (θ : ℝ) (f g : Hilbert) :
    (f,g) ∈ (operatorAt h hh T θ).graph ↔
      (action h hh θ f,action h hh θ g) ∈ T.graph := by
  have he : (operatorAt h hh T θ).graph =
      T.graph.comap ((action h hh θ).toLinearMap.prodMap (action h hh θ).toLinearMap) := by
    apply Submodule.toLinearPMap_graph_eq
    intro z hz hz0
    apply (action h hh θ).injective
    change (action h hh θ z.1,action h hh θ z.2) ∈ T.graph at hz
    rw [hz0,map_zero] at hz
    exact (T.graph_fst_eq_zero_snd hz rfl).trans (map_zero _).symm
  rw [he]
  rfl

theorem invariant_input_graph (ψ u : Hilbert) (hψ : ∀ θ, action h hh θ ψ=ψ)
    (hg : (ψ,u) ∈ T.graph) (θ : ℝ) :
    (ψ,action h hh (-θ) u) ∈ (operatorAt h hh T θ).graph := by
  apply (operatorAt_graph h hh T θ _ _).mpr
  rw [hψ,action_compose,neg_add_cancel,action_zero]
  exact hg

variable (ε : ℝ) (hε : 0 < ε)

theorem mixed_graph (u : Hilbert) (v : ℝ → Hilbert)
    (hm : ∀ η, (action h hh η u,v η) ∈ (square ε hε h).graph) (θ φ : ℝ) :
    (action h hh (-θ) u,action h hh (-φ) (v (φ-θ))) ∈ (squareAt ε hε h hh φ).graph := by
  apply (squareAt_graph ε hε h hh φ _ _).mpr
  rw [action_compose,action_compose,neg_add_cancel,action_zero]
  simpa only [show -θ+φ=φ-θ by ring] using hm (φ-θ)

theorem two_angle_graph (ψ u : Hilbert) (v : ℝ → Hilbert)
    (hψ : ∀ θ, action h hh θ ψ=ψ) (hg : (ψ,u) ∈ T.graph)
    (hm : ∀ η, (action h hh η u,v η) ∈ (square ε hε h).graph) (θ φ : ℝ) :
    (ψ,action h hh (-φ) (v (φ-θ))) ∈
      (composition (squareAt ε hε h hh φ) (operatorAt h hh T θ)).graph :=
  (composition_graph _ _ _ _).mpr ⟨action h hh (-θ) u,
    invariant_input_graph h hh T ψ u hψ hg θ,mixed_graph h hh ε hε u v hm θ φ⟩

#print axioms operatorAt_graph
#print axioms invariant_input_graph
#print axioms mixed_graph
#print axioms two_angle_graph
end
end UnifiedTheory.Audit.KFCausalChargeConjugatedInsertion

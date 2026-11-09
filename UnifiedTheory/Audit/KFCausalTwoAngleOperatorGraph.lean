/- Independent charge-angle transport of a proved pair of arbitrary
natural operator graphs on an invariant initial vector. -/
import UnifiedTheory.Audit.KFCausalChargeConjugatedInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalTwoAngleOperatorGraph
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (action action_compose action_zero)
open KFCausalChargeConjugatedInsertion (operatorAt operatorAt_graph invariant_input_graph)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable (h : ℝ) (hh : h ≠ 0) (S T : Hilbert →ₗ.[ℂ] Hilbert)

theorem mixed_graph (u : Hilbert) (v : ℝ → Hilbert)
    (hm : ∀ η, (action h hh η u,v η) ∈ S.graph) (θ φ : ℝ) :
    (action h hh (-θ) u,action h hh (-φ) (v (φ-θ))) ∈ (operatorAt h hh S φ).graph := by
  apply (operatorAt_graph h hh S φ _ _).mpr
  rw [action_compose,action_compose,neg_add_cancel,action_zero]
  simpa only [show -θ+φ=φ-θ by ring] using hm (φ-θ)

theorem two_angle_graph (ψ u : Hilbert) (v : ℝ → Hilbert)
    (hψ : ∀ θ, action h hh θ ψ=ψ) (hg : (ψ,u) ∈ T.graph)
    (hm : ∀ η, (action h hh η u,v η) ∈ S.graph) (θ φ : ℝ) :
    (ψ,action h hh (-φ) (v (φ-θ))) ∈
      (composition (operatorAt h hh S φ) (operatorAt h hh T θ)).graph :=
  (composition_graph _ _ _ _).mpr ⟨action h hh (-θ) u,
    invariant_input_graph h hh T ψ u hψ hg θ,mixed_graph h hh S u v hm θ φ⟩

#print axioms mixed_graph
#print axioms two_angle_graph
end
end UnifiedTheory.Audit.KFCausalTwoAngleOperatorGraph

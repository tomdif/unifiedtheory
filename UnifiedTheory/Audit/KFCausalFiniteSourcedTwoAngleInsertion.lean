/- Independent charge angles for the actual finite-family field
insertions. The inner operator is the charge conjugate of L Q. -/
import UnifiedTheory.Audit.KFCausalChargeConjugatedInsertion
import UnifiedTheory.Audit.KFCausalFiniteSourcedSymmetricSquare
import UnifiedTheory.Audit.KFCausalFiniteSourcedPointFieldSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalFiniteSourcedTwoAngleInsertion
noncomputable section
open KFCausalPhysicalCircleAction (action)
open KFCausalClockFloorVacuumSquare (square)
open KFCausalOrderedOperatorComposition (composition)
open KFCausalPhysicalField (physicalField)
open KFCausalPhysicalSpectatorGraph (symmetricPosition)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalSingleGaussianTwoAngleSquare (squareAt)
open KFCausalChargeConjugatedInsertion (operatorAt)
open KFCausalReciprocalNeutralSuperposition (state)
open KFCausalFiniteSourcedMixedVacuum (action_state)
open KFCausalFiniteSourcedFirstField (fieldOutput field_after_square_graph)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε/10)
local notation "ψ" => state n ε h a w p C b P hε ha hh hw

theorem point_two_angle_graph (θ φ : ℝ) :
    (ψ,action h hh (-φ)
      (KFCausalFiniteSourcedPointFieldSquare.secondOutput n ε h a w p C b P hε ha hh hw hb (φ-θ))) ∈
      (composition (squareAt ε hε h hh φ)
        (operatorAt h hh (composition (physicalField pointField) (square ε hε h)) θ)).graph :=
  KFCausalChargeConjugatedInsertion.two_angle_graph h hh _ ε hε ψ
    (fieldOutput n ε h a w p C b P hε ha hh hw hb pointField) _
    (action_state n ε h a w p C b P hε ha hh hw)
    (field_after_square_graph n ε h a w p C b P hε ha hh hw hb pointField)
    (KFCausalFiniteSourcedPointFieldSquare.mixed_graph n ε h a w p C b P hε ha hh hw hb) θ φ

include hb in
theorem point_two_angle_domain (θ φ : ℝ) :
    ψ ∈ (composition (squareAt ε hε h hh φ)
      (operatorAt h hh (composition (physicalField pointField) (square ε hε h)) θ)).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (point_two_angle_graph n ε h a w p C b P hε ha hh hw hb θ φ)

theorem symmetric_two_angle_graph (j : Fin 2) (θ φ : ℝ) :
    (ψ,action h hh (-φ)
      (KFCausalFiniteSourcedSymmetricSquare.secondOutput n ε h a w p C b P j hε ha hh hw hb (φ-θ))) ∈
      (composition (squareAt ε hε h hh φ)
        (operatorAt h hh (composition (physicalField (symmetricPosition j)) (square ε hε h)) θ)).graph :=
  KFCausalChargeConjugatedInsertion.two_angle_graph h hh _ ε hε ψ
    (fieldOutput n ε h a w p C b P hε ha hh hw hb (symmetricPosition j)) _
    (action_state n ε h a w p C b P hε ha hh hw)
    (field_after_square_graph n ε h a w p C b P hε ha hh hw hb (symmetricPosition j))
    (KFCausalFiniteSourcedSymmetricSquare.mixed_graph n ε h a w p C b P j hε ha hh hw hb) θ φ

include hb in
theorem symmetric_two_angle_domain (j : Fin 2) (θ φ : ℝ) :
    ψ ∈ (composition (squareAt ε hε h hh φ)
      (operatorAt h hh (composition (physicalField (symmetricPosition j)) (square ε hε h)) θ)).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (symmetric_two_angle_graph n ε h a w p C b P hε ha hh hw hb j θ φ)

#print axioms point_two_angle_graph
#print axioms point_two_angle_domain
#print axioms symmetric_two_angle_graph
#print axioms symmetric_two_angle_domain
end
end UnifiedTheory.Audit.KFCausalFiniteSourcedTwoAngleInsertion

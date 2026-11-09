/- The two antisymmetric kinetic second actions from their two actual
maximal momentum graphs, retaining forward and reverse factor witnesses. -/
import UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph
import UnifiedTheory.Audit.KFCausalEnergyReverseFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalAntisymmetricKineticGraphAssembly
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorBoundedInverse (inverseL inverseL_graph)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)
open KFCausalAntisymmetricMomentumCoordinates (antiDirection)
open KFCausalClockFloorAntisymmetricGraph (antiIndex antiIndex_factor)
open KFCausalClockFloorKineticSquare (reverse square)
open KFCausalClockFloorTrialMomentum (clockMomentum)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2)

def kineticSecond : Hilbert →ₗ.[ℂ] Hilbert :=
  composition (reverseFactor ε hε h modelDirections pointField (antiIndex i))
    (energyFactor ε hε h modelDirections pointField (antiIndex i))

theorem reverseFactor_eq :
    reverseFactor ε hε h modelDirections pointField (antiIndex i)=reverse ε h (antiDirection i) := by
  fin_cases i <;> rfl

theorem kineticSecond_eq : kineticSecond ε hε h i=square ε h (antiDirection i) := by
  rw [kineticSecond,reverseFactor_eq,antiIndex_factor]
  rfl

theorem actual_forward_graph (f u : Hilbert)
    (hu : (inverseL ε hε f,u) ∈ (transverseMomentum h (antiDirection i)).graph) :
    (f,u) ∈ (energyFactor ε hε h modelDirections pointField (antiIndex i)).graph := by
  rw [antiIndex_factor]
  exact (composition_graph _ _ _ _).mpr ⟨_,(inverseL_graph ε hε f _).mpr rfl,hu⟩

theorem actual_reverse_graph (u q : Hilbert)
    (hq : (u,q) ∈ (transverseMomentum h (antiDirection i)).graph) :
    (u,inverseL ε hε q) ∈ (reverseFactor ε hε h modelDirections pointField (antiIndex i)).graph := by
  rw [reverseFactor_eq]
  exact (composition_graph _ _ _ _).mpr ⟨q,hq,(inverseL_graph ε hε q _).mpr rfl⟩

theorem actual_second_graph (f u q : Hilbert)
    (hu : (inverseL ε hε f,u) ∈ (transverseMomentum h (antiDirection i)).graph)
    (hq : (u,q) ∈ (transverseMomentum h (antiDirection i)).graph) :
    (f,inverseL ε hε q) ∈ (kineticSecond ε hε h i).graph :=
  (composition_graph _ _ _ _).mpr ⟨u,actual_forward_graph ε hε h i f u hu,
    actual_reverse_graph ε hε h i u q hq⟩

theorem actual_second_graph_iff (f z : Hilbert) :
    (f,z) ∈ (kineticSecond ε hε h i).graph ↔ ∃ u q,
      (inverseL ε hε f,u) ∈ (transverseMomentum h (antiDirection i)).graph ∧
      (u,q) ∈ (transverseMomentum h (antiDirection i)).graph ∧ z=inverseL ε hε q := by
  rw [kineticSecond_eq]
  exact KFCausalClockFloorKineticSquare.square_graph ε hε h (antiDirection i) f z

#print axioms reverseFactor_eq
#print axioms kineticSecond_eq
#print axioms actual_forward_graph
#print axioms actual_reverse_graph
#print axioms actual_second_graph
#print axioms actual_second_graph_iff
end
end UnifiedTheory.Audit.KFCausalAntisymmetricKineticGraphAssembly

/- Explicit natural reverse factors for all eight clock-floor energy
operators. Their graph witnesses give the duality needed for the strong
Hamiltonian domain; no commutation of ordered matter factors is used. -/
import UnifiedTheory.Audit.KFCausalJointSecondPairing
import UnifiedTheory.Audit.KFCausalClockFloorKineticSquare
import UnifiedTheory.Audit.KFCausalClockFloorMatterClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalEnergyReverseFactors
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalClockFloorClockHalf
open KFCausalClockFloorExponential
open KFCausalClockFloorTrialSpectralDomain (reversedExponential)
open KFCausalClockFloorMatterClosure (reversedMatterFactor matterFactor_formalAdjoint)
open KFCausalPhysicalField (physicalField physicalField_selfAdjoint)
open KFCausalTransverseFieldSquare (fieldSquare fieldSquare_selfAdjoint)
open KFCausalPhysicalTransverseMomentum (transverseMomentum_selfAdjoint)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalOrderedOperatorComposition

def reverseFactor (ε : ℝ) (hε : 0 < ε) (h : ℝ) (v : Fin 4 → Transverse)
    (l : Transverse →L[ℝ] ℝ) : Fin 8 → Hilbert →ₗ.[ℂ] Hilbert :=
  ![clockHalf ε,KFCausalClockFloorKineticSquare.reverse ε h (v 0),
    KFCausalClockFloorKineticSquare.reverse ε h (v 1),
    KFCausalClockFloorKineticSquare.reverse ε h (v 2),
    KFCausalClockFloorKineticSquare.reverse ε h (v 3),
    reversedMatterFactor ε hε h (physicalField l),
    reversedMatterFactor ε hε h (fieldSquare l),reversedExponential ε hε h]

theorem factor_formalAdjoint (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    (energyFactor ε hε h v l i).IsFormalAdjoint (reverseFactor ε hε h v l i) := by
  fin_cases i
  · intro f g
    exact selfAdjoint_graph_pairing _ (clockHalf_selfAdjoint ε) _ _ _ _
      ((clockHalf ε).mem_graph f) ((clockHalf ε).mem_graph g)
  · exact composition_formalAdjoint _ _ (transverseMomentum_selfAdjoint h (v 0)) (inverseClockHalf_selfAdjoint ε)
  · exact composition_formalAdjoint _ _ (transverseMomentum_selfAdjoint h (v 1)) (inverseClockHalf_selfAdjoint ε)
  · exact composition_formalAdjoint _ _ (transverseMomentum_selfAdjoint h (v 2)) (inverseClockHalf_selfAdjoint ε)
  · exact composition_formalAdjoint _ _ (transverseMomentum_selfAdjoint h (v 3)) (inverseClockHalf_selfAdjoint ε)
  · exact matterFactor_formalAdjoint ε h hε _ (physicalField_selfAdjoint l)
  · exact matterFactor_formalAdjoint ε h hε _ (fieldSquare_selfAdjoint l)
  · exact composition_formalAdjoint _ _
      (longitudinal_exponential_selfAdjoint ε hε h (1/2)) (inverseClockHalf_selfAdjoint ε)

theorem factor_pairing (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8)
    (u z f g : Hilbert) (huz : (u,z) ∈ (reverseFactor ε hε h v l i).graph)
    (hfg : (f,g) ∈ (energyFactor ε hε h v l i).graph) :
    inner ℂ u g = inner ℂ z f :=
  KFCausalJointSecondPairing.formal_graph_pairing _ _ (factor_formalAdjoint ε hε h v l i)
    u z f g huz hfg

#print axioms factor_formalAdjoint
#print axioms factor_pairing
end
end UnifiedTheory.Audit.KFCausalEnergyReverseFactors

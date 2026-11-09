/- The two symmetric kinetic second actions from their two actual
maximal momentum graphs, retaining forward and reverse factor witnesses. -/
import UnifiedTheory.Audit.KFCausalClockFloorSymmetricOrbitGraph
import UnifiedTheory.Audit.KFCausalEnergyReverseFactors
import UnifiedTheory.Audit.KFCausalSymmetricMixedDerivativeGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalSymmetricKineticGraphAssembly
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorBoundedInverse (inverseL inverseL_graph)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)
open KFCausalSymmetricMomentumCoordinates (symmetricDirection)
open KFCausalClockFloorSymmetricOrbitGraph (symmetricEnergyIndex symmetricIndex_factor)
open KFCausalClockFloorKineticSquare (reverse square)
open KFCausalClockFloorTrialMomentum (clockMomentum)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2)

def kineticSecond : Hilbert →ₗ.[ℂ] Hilbert :=
  composition (reverseFactor ε hε h modelDirections pointField (symmetricEnergyIndex i))
    (energyFactor ε hε h modelDirections pointField (symmetricEnergyIndex i))

theorem reverseFactor_eq :
    reverseFactor ε hε h modelDirections pointField (symmetricEnergyIndex i)=reverse ε h (symmetricDirection i) := by
  fin_cases i <;> rfl

theorem kineticSecond_eq : kineticSecond ε hε h i=square ε h (symmetricDirection i) := by
  rw [kineticSecond,reverseFactor_eq,symmetricIndex_factor]
  rfl

theorem actual_forward_graph (f u : Hilbert)
    (hu : (inverseL ε hε f,u) ∈ (transverseMomentum h (symmetricDirection i)).graph) :
    (f,u) ∈ (energyFactor ε hε h modelDirections pointField (symmetricEnergyIndex i)).graph := by
  rw [symmetricIndex_factor]
  exact (composition_graph _ _ _ _).mpr ⟨_,(inverseL_graph ε hε f _).mpr rfl,hu⟩

theorem actual_reverse_graph (u q : Hilbert)
    (hq : (u,q) ∈ (transverseMomentum h (symmetricDirection i)).graph) :
    (u,inverseL ε hε q) ∈ (reverseFactor ε hε h modelDirections pointField (symmetricEnergyIndex i)).graph := by
  rw [reverseFactor_eq]
  exact (composition_graph _ _ _ _).mpr ⟨q,hq,(inverseL_graph ε hε q _).mpr rfl⟩

theorem actual_second_graph (f u q : Hilbert)
    (hu : (inverseL ε hε f,u) ∈ (transverseMomentum h (symmetricDirection i)).graph)
    (hq : (u,q) ∈ (transverseMomentum h (symmetricDirection i)).graph) :
    (f,inverseL ε hε q) ∈ (kineticSecond ε hε h i).graph :=
  (composition_graph _ _ _ _).mpr ⟨u,actual_forward_graph ε hε h i f u hu,
    actual_reverse_graph ε hε h i u q hq⟩

theorem actual_second_graph_iff (f z : Hilbert) :
    (f,z) ∈ (kineticSecond ε hε h i).graph ↔ ∃ u q,
      (inverseL ε hε f,u) ∈ (transverseMomentum h (symmetricDirection i)).graph ∧
      (u,q) ∈ (transverseMomentum h (symmetricDirection i)).graph ∧ z=inverseL ε hε q := by
  rw [kineticSecond_eq]
  exact KFCausalClockFloorKineticSquare.square_graph ε hε h (symmetricDirection i) f z


theorem derivative_second_graphs (hh : h ≠ 0) (f d d₂ : Hilbert)
    (ρ σ τ : KFCausalEuclideanProductCoordinates.Block 2 × KFCausalEuclideanProductCoordinates.Block 4 → ℂ)
    (hf : KFCausalClockFloorMixedRadial.clockMixed ε hε (inverseL ε hε f) =ᵐ[MeasureTheory.volume] ρ)
    (hd : KFCausalClockFloorMixedRadial.clockMixed ε hε d =ᵐ[MeasureTheory.volume] σ)
    (hd₂ : KFCausalClockFloorMixedRadial.clockMixed ε hε d₂ =ᵐ[MeasureTheory.volume] τ)
    (hder : ∀ x : KFCausalEuclideanProductCoordinates.Joint 2 4,
      HasDerivAt (fun t : ℝ => ρ (KFCausalEuclideanProductCoordinates.split 2 4
        (x+t • KFCausalSymmetricMixedTranslation.velocity ε hε i (x (.inr 0)))))
        (σ (KFCausalEuclideanProductCoordinates.split 2 4 x)) 0)
    (hder₂ : ∀ x : KFCausalEuclideanProductCoordinates.Joint 2 4,
      HasDerivAt (fun t : ℝ => σ (KFCausalEuclideanProductCoordinates.split 2 4
        (x+t • KFCausalSymmetricMixedTranslation.velocity ε hε i (x (.inr 0)))))
        (τ (KFCausalEuclideanProductCoordinates.split 2 4 x)) 0) :
    (f,(-Complex.I*(h:ℂ)) • d) ∈
      (energyFactor ε hε h modelDirections pointField (symmetricEnergyIndex i)).graph ∧
    ((-Complex.I*(h:ℂ)) • d,inverseL ε hε ((-(h:ℂ)^2) • d₂)) ∈
      (reverseFactor ε hε h modelDirections pointField (symmetricEnergyIndex i)).graph ∧
    (f,inverseL ε hε ((-(h:ℂ)^2) • d₂)) ∈ (kineticSecond ε hε h i).graph := by
  obtain ⟨h₁,h₂⟩ := KFCausalSymmetricMixedDerivativeGraph.second_derivative_graph
    ε hε i h hh (inverseL ε hε f) d d₂ ρ σ τ hf hd hd₂ hder hder₂
  exact ⟨actual_forward_graph ε hε h i f _ h₁,
    actual_reverse_graph ε hε h i _ _ h₂,
    actual_second_graph ε hε h i f _ _ h₁ h₂⟩

#print axioms reverseFactor_eq
#print axioms kineticSecond_eq
#print axioms actual_forward_graph
#print axioms actual_reverse_graph
#print axioms actual_second_graph
#print axioms actual_second_graph_iff
#print axioms derivative_second_graphs
end
end UnifiedTheory.Audit.KFCausalSymmetricKineticGraphAssembly

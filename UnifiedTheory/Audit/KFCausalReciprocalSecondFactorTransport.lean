/- Exact reciprocal-squeeze transport for all natural second actions.
Every first-factor scaling appears twice. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianClockKineticSquare
import UnifiedTheory.Audit.KFCausalReciprocalGaussianVacuumSquare
import UnifiedTheory.Audit.KFCausalReciprocalSqueezeMatterSquare
import UnifiedTheory.Audit.KFCausalEnergyReverseFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalReciprocalSecondFactorTransport
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalSqueezeTransport (transport)
open KFCausalReciprocalSqueezeEnergy (factorScale degree)
open KFCausalReciprocalSqueezeKinetic (half_graph kineticScale)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalOrderedOperatorComposition (composition composition_graph)

theorem clock_square_transport (ε a : ℝ) (f z : Hilbert)
    (hfz : (f,z) ∈ (composition (clockHalf ε) (clockHalf ε)).graph) :
    (transport a f,transport a z) ∈ (composition (clockHalf ε) (clockHalf ε)).graph := by
  obtain ⟨u,hu,hz⟩ := (composition_graph _ _ _ _).mp hfz
  exact (composition_graph _ _ _ _).mpr ⟨_,half_graph ε a f u hu,half_graph ε a u z hz⟩

theorem second_graph_transport (ε : ℝ) (hε : 0 < ε) (h a : ℝ) (j : Fin 8) (f z : Hilbert)
    (hfz : (f,z) ∈ (composition (reverseFactor ε hε h modelDirections pointField j)
      (energyFactor ε hε h modelDirections pointField j)).graph) :
    (transport a f,factorScale a j^2 • transport a z) ∈
      (composition (reverseFactor ε hε h modelDirections pointField j)
        (energyFactor ε hε h modelDirections pointField j)).graph := by
  fin_cases j
  · simpa [factorScale,degree] using clock_square_transport ε a f z hfz
  · simpa [factorScale,degree,kineticScale] using
      KFCausalReciprocalGaussianClockKineticSquare.model_square_transport ε hε h a 0 f z hfz
  · simpa [factorScale,degree,kineticScale] using
      KFCausalReciprocalGaussianClockKineticSquare.model_square_transport ε hε h a 1 f z hfz
  · simpa [factorScale,degree,kineticScale] using
      KFCausalReciprocalGaussianClockKineticSquare.model_square_transport ε hε h a 2 f z hfz
  · simpa [factorScale,degree,kineticScale] using
      KFCausalReciprocalGaussianClockKineticSquare.model_square_transport ε hε h a 3 f z hfz
  · simpa [factorScale,degree,pow_two] using
      KFCausalReciprocalSqueezeMatterSquare.linear_square_graph ε hε h a f z hfz
  · simpa [factorScale,degree,pow_two] using
      KFCausalReciprocalSqueezeMatterSquare.quadratic_square_graph ε hε h a f z hfz
  · simpa [factorScale,degree] using
      KFCausalReciprocalGaussianVacuumSquare.square_graph_transport ε hε h a f z hfz

#print axioms clock_square_transport
#print axioms second_graph_transport
end
end UnifiedTheory.Audit.KFCausalReciprocalSecondFactorTransport

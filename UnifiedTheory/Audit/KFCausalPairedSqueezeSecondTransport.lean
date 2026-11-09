/- Paired squeeze transports all eight actual natural second-component
graphs. Both primitive witnesses are retained; no closedness of a
composed second operator is assumed. -/
import UnifiedTheory.Audit.KFCausalPairedSqueezeKinetic
import UnifiedTheory.Audit.KFCausalPairedSqueezeMatterSquare
import UnifiedTheory.Audit.KFCausalClockFloorKineticSquare
import UnifiedTheory.Audit.KFCausalEnergyReverseFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalPairedSqueezeSecondTransport
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalPairedSqueezeTransport (transport)
open KFCausalPairedSqueezeFlow (squeeze squeeze_directions)
open KFCausalPairedSqueezeClockCommutation (inverse_half_commutes)
open KFCausalPairedSqueezeKinetic (kineticScale half_graph)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorKineticSquare (square square_graph)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalOrderedOperatorComposition (composition composition_graph)

def degree : Fin 8 → ℝ := ![0,-1,-1,1,1,1,2,0]
def factorScale (a : ℝ) (j : Fin 8) : ℂ := Real.exp (a*degree j)

theorem kinetic_square_transport (ε : ℝ) (hε : 0 < ε) (h a q : ℝ) (v : Transverse)
    (hv : squeeze a v = Real.exp q • v) (f z : Hilbert)
    (hfz : (f,z) ∈ (square ε h v).graph) :
    (transport a f,(Real.exp (-q):ℂ)^2 • transport a z) ∈ (square ε h v).graph := by
  obtain ⟨u,r,hdu,hur,hz⟩ := (square_graph ε hε h v f z).mp hfz
  have h1 := KFCausalPairedSqueezeKinetic.momentum_graph h a q v hv _ _ hdu
  rw [inverse_half_commutes] at h1
  have h2 := (transverseMomentum h v).graph.smul_mem (Real.exp (-q):ℂ)
    (KFCausalPairedSqueezeKinetic.momentum_graph h a q v hv _ _ hur)
  apply (square_graph ε hε h v _ _).mpr
  refine ⟨_,_,h1,h2,?_⟩
  change (Real.exp (-q):ℂ)^2 • transport a z =
    inverseL ε hε ((Real.exp (-q):ℂ) • ((Real.exp (-q):ℂ) • transport a r))
  rw [hz,inverse_half_commutes,map_smul,map_smul,smul_smul,pow_two]

theorem model_square_transport (ε : ℝ) (hε : 0 < ε) (h a : ℝ) (i : Fin 4)
    (f z : Hilbert) (hfz : (f,z) ∈ (square ε h (modelDirections i)).graph) :
    (transport a f,kineticScale a i^2 • transport a z) ∈
      (square ε h (modelDirections i)).graph := by
  by_cases hi : i < 2
  · have hv : squeeze a (modelDirections i) = Real.exp a • modelDirections i := by
      simpa only [hi,if_true] using squeeze_directions a i
    simpa only [kineticScale,hi,if_true] using kinetic_square_transport ε hε h a a _ hv f z hfz
  · have hv : squeeze a (modelDirections i) = Real.exp (-a) • modelDirections i := by
      simpa only [hi,if_false] using squeeze_directions a i
    simpa only [kineticScale,hi,if_false,neg_neg] using kinetic_square_transport ε hε h a (-a) _ hv f z hfz

theorem clock_square_transport (ε a : ℝ) (f z : Hilbert)
    (hfz : (f,z) ∈ (composition (clockHalf ε) (clockHalf ε)).graph) :
    (transport a f,transport a z) ∈ (composition (clockHalf ε) (clockHalf ε)).graph := by
  obtain ⟨u,hu,hz⟩ := (composition_graph _ _ _ _).mp hfz
  exact (composition_graph _ _ _ _).mpr ⟨_,half_graph ε a f u hu,half_graph ε a u z hz⟩

private theorem vacuum_square_transport (ε : ℝ) (hε : 0 < ε) (h a : ℝ) (f z : Hilbert)
    (hfz : (f,z) ∈ (KFCausalClockFloorVacuumSquare.square ε hε h).graph) :
    (transport a f,transport a z) ∈ (KFCausalClockFloorVacuumSquare.square ε hε h).graph := by
  obtain ⟨u,hu,hz⟩ := (composition_graph _ _ _ _).mp hfz
  exact (composition_graph _ _ _ _).mpr ⟨_,
    KFCausalPairedSqueezeExponential.ordered_graph_squeeze ε hε h a f u hu,
    KFCausalPairedSqueezeMatterSquare.reversed_exponential_graph ε hε h a u z hz⟩

theorem second_graph_transport (ε : ℝ) (hε : 0 < ε) (h a : ℝ) (j : Fin 8) (f z : Hilbert)
    (hfz : (f,z) ∈ (composition (reverseFactor ε hε h modelDirections pointField j)
      (energyFactor ε hε h modelDirections pointField j)).graph) :
    (transport a f,factorScale a j^2 • transport a z) ∈
      (composition (reverseFactor ε hε h modelDirections pointField j)
        (energyFactor ε hε h modelDirections pointField j)).graph := by
  fin_cases j
  · simpa [factorScale,degree] using clock_square_transport ε a f z hfz
  · simpa [factorScale,degree,kineticScale] using model_square_transport ε hε h a 0 f z hfz
  · simpa [factorScale,degree,kineticScale] using model_square_transport ε hε h a 1 f z hfz
  · simpa [factorScale,degree,kineticScale] using model_square_transport ε hε h a 2 f z hfz
  · simpa [factorScale,degree,kineticScale] using model_square_transport ε hε h a 3 f z hfz
  · simpa [factorScale,degree,pow_two] using
      KFCausalPairedSqueezeMatterSquare.linear_square_graph ε hε h a f z hfz
  · simpa [factorScale,degree,pow_two,mul_comm a 2] using
      KFCausalPairedSqueezeMatterSquare.quadratic_square_graph ε hε h a f z hfz
  · simpa [factorScale,degree] using vacuum_square_transport ε hε h a f z hfz

#print axioms kinetic_square_transport
#print axioms model_square_transport
#print axioms clock_square_transport
#print axioms second_graph_transport
end
end UnifiedTheory.Audit.KFCausalPairedSqueezeSecondTransport

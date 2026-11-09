/- Natural reverse-after-forward component graphs assemble into the
original averaged Hamiltonian graph on the zero-charge sector. Middle
factor witnesses are extracted from actual composition graphs. -/
import UnifiedTheory.Audit.KFCausalFixedStrongHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalNaturalSecondHamiltonianGraph
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalStandingChargeOperator (zeroSector zeroProjection)
open KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalJointSecondPairing (secondWeighted)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)

def component (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 8) : Hilbert →ₗ.[ℂ] Hilbert :=
  composition (reverseFactor ε hε h modelDirections pointField i)
    (energyFactor ε hε h modelDirections pointField i)

theorem hamiltonian_graph (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)
    (f : Hilbert) (hf : f ∈ zeroSector h hh) (z : Fin 8 → Hilbert)
    (hz : ∀ i, (f,z i) ∈ (component ε hε h i).graph) :
    (f,zeroProjection h hh (secondWeighted (energyWeight mass2 quartic vacuum t) z)) ∈
      (hamiltonian ε hε h hh hb mass2 quartic vacuum t).graph := by
  have hm : ∀ i, ∃ g : Hilbert,
      (f,g) ∈ (energyFactor ε hε h modelDirections pointField i).graph ∧
      (g,z i) ∈ (reverseFactor ε hε h modelDirections pointField i).graph := by
    intro i
    exact (composition_graph _ _ _ _).mp (hz i)
  choose g hg hzg using hm
  exact KFCausalFixedStrongHamiltonian.hamiltonian_graph ε h hε hh hb
    mass2 quartic vacuum t f hf g z hg hzg

theorem hamiltonian_domain (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)
    (f : Hilbert) (hf : f ∈ zeroSector h hh) (z : Fin 8 → Hilbert)
    (hz : ∀ i, (f,z i) ∈ (component ε hε h i).graph) :
    f ∈ (hamiltonian ε hε h hh hb mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (hamiltonian_graph ε h hε hh hb mass2 quartic vacuum t f hf z hz)

#print axioms hamiltonian_graph
#print axioms hamiltonian_domain
end
end UnifiedTheory.Audit.KFCausalNaturalSecondHamiltonianGraph

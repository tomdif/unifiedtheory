/- Six of eight second-factor requirements are proved for the reciprocal
state and its actual clock momentum. The full strong Hamiltonian domain
reduces to the two explicitly stated reverse matter graphs. -/
import UnifiedTheory.Audit.KFCausalFixedStrongHamiltonian
import UnifiedTheory.Audit.KFCausalReciprocalGaussianVacuumSquare
import UnifiedTheory.Audit.KFCausalReciprocalGaussianClockKineticSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianStrongReduction
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalJointSecondPairing (secondWeighted)
open KFCausalReciprocalGaussianClockKineticSquare
  (clockOutput momentumClockOutput kineticOutput momentumKineticOutput)
open KFCausalReciprocalGaussianMomentum (output momentum momentumOutput output_graph momentumOutput_graph)
open KFCausalGaussianVacuumSquare (original_strip)

private theorem reverse_of_composition (T R : Hilbert →ₗ.[ℂ] Hilbert) (f u z : Hilbert)
    (hfu : (f,u) ∈ T.graph) (hfz : (f,z) ∈ (composition R T).graph) :
    (u,z) ∈ R.graph := by
  obtain ⟨u',hu',hz⟩ := (composition_graph R T f z).mp hfz
  have he := T.mem_graph_snd_inj' hu' hfu rfl
  dsimp only at he
  rwa [he] at hz

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "ψ" => KFCausalReciprocalGaussianCharge.state ε a h w hε ha hh (by linarith)
local notation "Bψ" => momentum ε a h w hε ha hh hw
local notation "u" => output ε a h w hε ha hh hw hb₀
local notation "v" => momentumOutput ε a h w hε ha hh hw hb₀
local notation "R" => reverseFactor ε hε h modelDirections pointField

def stateSeconds (z5 z6 : Hilbert) : Fin 8 → Hilbert :=
  ![clockOutput ε a h w hε ha hh hw,
    kineticOutput ε a h w hε ha hh 0,kineticOutput ε a h w hε ha hh 1,
    kineticOutput ε a h w hε ha hh 2,kineticOutput ε a h w hε ha hh 3,z5,z6,
    KFCausalReciprocalGaussianVacuumSquare.stateOutput ε a h w hε ha hh hw hb]

def momentumSeconds (z5 z6 : Hilbert) : Fin 8 → Hilbert :=
  ![momentumClockOutput ε a h w hε ha hh hw,
    momentumKineticOutput ε a h w hε ha hh 0,momentumKineticOutput ε a h w hε ha hh 1,
    momentumKineticOutput ε a h w hε ha hh 2,momentumKineticOutput ε a h w hε ha hh 3,z5,z6,
    KFCausalReciprocalGaussianVacuumSquare.momentumOutput ε a h w hε ha hh hw hb]

theorem state_reverse_graphs (z5 z6 : Hilbert)
    (h5 : (u 5,z5) ∈ (R 5).graph) (h6 : (u 6,z6) ∈ (R 6).graph) (j : Fin 8) :
    (u j,stateSeconds ε a h w hε ha hh hw hb z5 z6 j) ∈ (R j).graph := by
  fin_cases j
  · exact KFCausalReciprocalGaussianClockKineticSquare.clock_graph ε a h w hε ha hh hw hb₀
  · exact reverse_of_composition _ _ _ _ _ (output_graph ε a h w hε ha hh hw hb₀ 1)
      (KFCausalReciprocalGaussianClockKineticSquare.kinetic_graph ε a h w hε ha hh hw 0)
  · exact reverse_of_composition _ _ _ _ _ (output_graph ε a h w hε ha hh hw hb₀ 2)
      (KFCausalReciprocalGaussianClockKineticSquare.kinetic_graph ε a h w hε ha hh hw 1)
  · exact reverse_of_composition _ _ _ _ _ (output_graph ε a h w hε ha hh hw hb₀ 3)
      (KFCausalReciprocalGaussianClockKineticSquare.kinetic_graph ε a h w hε ha hh hw 2)
  · exact reverse_of_composition _ _ _ _ _ (output_graph ε a h w hε ha hh hw hb₀ 4)
      (KFCausalReciprocalGaussianClockKineticSquare.kinetic_graph ε a h w hε ha hh hw 3)
  · exact h5
  · exact h6
  · exact reverse_of_composition _ _ _ _ _ (output_graph ε a h w hε ha hh hw hb₀ 7)
      (KFCausalReciprocalGaussianVacuumSquare.state_graph ε a h w hε ha hh hw hb)

theorem momentum_reverse_graphs (z5 z6 : Hilbert)
    (h5 : (v 5,z5) ∈ (R 5).graph) (h6 : (v 6,z6) ∈ (R 6).graph) (j : Fin 8) :
    (v j,momentumSeconds ε a h w hε ha hh hw hb z5 z6 j) ∈ (R j).graph := by
  fin_cases j
  · exact KFCausalReciprocalGaussianClockKineticSquare.momentum_clock_graph ε a h w hε ha hh hw hb₀
  · exact reverse_of_composition _ _ _ _ _ (momentumOutput_graph ε a h w hε ha hh hw hb₀ 1)
      (KFCausalReciprocalGaussianClockKineticSquare.momentum_kinetic_graph ε a h w hε ha hh hw 0)
  · exact reverse_of_composition _ _ _ _ _ (momentumOutput_graph ε a h w hε ha hh hw hb₀ 2)
      (KFCausalReciprocalGaussianClockKineticSquare.momentum_kinetic_graph ε a h w hε ha hh hw 1)
  · exact reverse_of_composition _ _ _ _ _ (momentumOutput_graph ε a h w hε ha hh hw hb₀ 3)
      (KFCausalReciprocalGaussianClockKineticSquare.momentum_kinetic_graph ε a h w hε ha hh hw 2)
  · exact reverse_of_composition _ _ _ _ _ (momentumOutput_graph ε a h w hε ha hh hw hb₀ 4)
      (KFCausalReciprocalGaussianClockKineticSquare.momentum_kinetic_graph ε a h w hε ha hh hw 3)
  · exact h5
  · exact h6
  · exact reverse_of_composition _ _ _ _ _ (momentumOutput_graph ε a h w hε ha hh hw hb₀ 7)
      (KFCausalReciprocalGaussianVacuumSquare.momentum_graph ε a h w hε ha hh hw hb)

theorem state_hamiltonian_graph_of_matter (z5 z6 : Hilbert)
    (h5 : (u 5,z5) ∈ (R 5).graph) (h6 : (u 6,z6) ∈ (R 6).graph)
    (mass2 quartic vacuum t : ℝ) :
    (ψ,zeroProjection h hh (secondWeighted (energyWeight mass2 quartic vacuum t)
      (stateSeconds ε a h w hε ha hh hw hb z5 z6))) ∈
        (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).graph :=
  KFCausalFixedStrongHamiltonian.hamiltonian_graph ε h hε hh hb₀ mass2 quartic vacuum t ψ
    (KFCausalReciprocalGaussianCharge.state_zeroSector ε a h w hε ha hh (by linarith)) u _
    (output_graph ε a h w hε ha hh hw hb₀)
    (state_reverse_graphs ε a h w hε ha hh hw hb z5 z6 h5 h6)

theorem momentum_hamiltonian_graph_of_matter (z5 z6 : Hilbert)
    (h5 : (v 5,z5) ∈ (R 5).graph) (h6 : (v 6,z6) ∈ (R 6).graph)
    (mass2 quartic vacuum t : ℝ) :
    (Bψ,zeroProjection h hh (secondWeighted (energyWeight mass2 quartic vacuum t)
      (momentumSeconds ε a h w hε ha hh hw hb z5 z6))) ∈
        (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).graph :=
  KFCausalFixedStrongHamiltonian.hamiltonian_graph ε h hε hh hb₀ mass2 quartic vacuum t Bψ
    (KFCausalReciprocalGaussianMomentum.momentum_zeroSector ε a h w hε ha hh hw) v _
    (momentumOutput_graph ε a h w hε ha hh hw hb₀)
    (momentum_reverse_graphs ε a h w hε ha hh hw hb z5 z6 h5 h6)

#print axioms state_reverse_graphs
#print axioms momentum_reverse_graphs
#print axioms state_hamiltonian_graph_of_matter
#print axioms momentum_hamiltonian_graph_of_matter
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianStrongReduction

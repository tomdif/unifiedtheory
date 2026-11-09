/- The full interacting Hamiltonian output lies in the actual maximal
pure-clock domain for the entire correlated clustered family. Both B H
and H B are defined and their original finite outputs converge strongly.
This is a domain/graph result, not an evolution-invariant core or a uniform
energy-relative response estimate. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPotentialSecondClock
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredHamiltonianClockRemainder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredHamiltonianClockLimit
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredAllSecondLimit (inputSeconds)
open KFCausalCorrelatedClusteredPotentialSecondClock (matterDerivative vacuumDerivative)
open KFCausalCorrelatedClusteredClockKineticSecondCommutator (derivative)
open KFCausalCorrelatedClusteredStrongHamiltonianLimit
open KFCausalCorrelatedClusteredHamiltonianClockRemainder (finiteHamiltonianDerivative finitePotentialDerivative potentialPart)
open KFCausalProjectedSecondClockDecomposition (total high)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
local notation "B" => pureMomentum ε hε h
local notation "L" => inputSeconds f ε h a p hε hh ha hb
local notation "d" => derivative f ε h a p hε hh ha hb
local notation "D" => KFCausalCorrelatedClusteredFiniteSecondPureClock.finiteDerivative f ε h a p hε hh ha hb
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha
local notation "ψδ" => KFCausalCorrelatedClusteredInputProfiles.finiteState f ε h a p hε hh ha

def secondDerivative : Fin 8 → Hilbert := ![d 0,d 1,d 2,d 3,d 4,
  matterDerivative f ε h a p hε hh ha hb 0,matterDerivative f ε h a p hε hh ha hb 1,
  vacuumDerivative f ε h a p hε hh ha hb]

theorem second_derivative_graph (j : Fin 8) :
    (L j,secondDerivative f ε h a p hε hh ha hb j) ∈ (B).graph := by
  fin_cases j
  · exact KFCausalCorrelatedClusteredClockKineticSecondCommutator.derivative_graph f ε h a p hε hh ha hb 0
  · exact KFCausalCorrelatedClusteredClockKineticSecondCommutator.derivative_graph f ε h a p hε hh ha hb 1
  · exact KFCausalCorrelatedClusteredClockKineticSecondCommutator.derivative_graph f ε h a p hε hh ha hb 2
  · exact KFCausalCorrelatedClusteredClockKineticSecondCommutator.derivative_graph f ε h a p hε hh ha hb 3
  · exact KFCausalCorrelatedClusteredClockKineticSecondCommutator.derivative_graph f ε h a p hε hh ha hb 4
  · exact KFCausalCorrelatedClusteredPotentialSecondClock.matter_graph f ε h a p hε hh ha hb 0
  · exact KFCausalCorrelatedClusteredPotentialSecondClock.matter_graph f ε h a p hε hh ha hb 1
  · exact KFCausalCorrelatedClusteredPotentialSecondClock.vacuum_graph f ε h a p hε hh ha hb

theorem second_clock_domain (j : Fin 8) : L j ∈ (B).domain :=
  LinearPMap.mem_domain_of_mem_graph (second_derivative_graph f ε h a p hε hh ha hb j)

theorem second_derivative_tendsto (j : Fin 8) :
    Tendsto (fun δ => D δ j) (𝓝[>] 0) (𝓝 (secondDerivative f ε h a p hε hh ha hb j)) := by
  fin_cases j
  · exact KFCausalCorrelatedClusteredClockKineticSecondCommutator.derivative_tendsto f ε h a p hε hh ha hb 0
  · exact KFCausalCorrelatedClusteredClockKineticSecondCommutator.derivative_tendsto f ε h a p hε hh ha hb 1
  · exact KFCausalCorrelatedClusteredClockKineticSecondCommutator.derivative_tendsto f ε h a p hε hh ha hb 2
  · exact KFCausalCorrelatedClusteredClockKineticSecondCommutator.derivative_tendsto f ε h a p hε hh ha hb 3
  · exact KFCausalCorrelatedClusteredClockKineticSecondCommutator.derivative_tendsto f ε h a p hε hh ha hb 4
  · exact KFCausalCorrelatedClusteredPotentialSecondClock.matter_derivative_tendsto f ε h a p hε hh ha hb 0
  · exact KFCausalCorrelatedClusteredPotentialSecondClock.matter_derivative_tendsto f ε h a p hε hh ha hb 1
  · exact KFCausalCorrelatedClusteredPotentialSecondClock.vacuum_derivative_tendsto f ε h a p hε hh ha hb

variable (mass2 quartic vacuum t : ℝ)
local notation "c" => energyWeight mass2 quartic vacuum t
local notation "H" => hamiltonian ε hε h hh (KFCausalGaussianVacuumSquare.original_strip ε h hε hb) mass2 quartic vacuum t
local notation "Hψ" => inputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t

def hamiltonianDerivative : Hilbert := total h hh c (secondDerivative f ε h a p hε hh ha hb)
def potentialDerivative : Hilbert := high h hh c (secondDerivative f ε h a p hε hh ha hb)

theorem hamiltonian_clock_graph :
    (Hψ,hamiltonianDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t) ∈ (B).graph :=
  KFCausalProjectedSecondClockDecomposition.total_graph h hh c ε hε L
    (secondDerivative f ε h a p hε hh ha hb) (second_derivative_graph f ε h a p hε hh ha hb)

theorem hamiltonian_clock_domain : Hψ ∈ (B).domain :=
  LinearPMap.mem_domain_of_mem_graph (hamiltonian_clock_graph f ε h a p hε hh ha hb mass2 quartic vacuum t)

theorem potential_clock_graph :
    (potentialPart f ε h a p hε hh ha hb mass2 quartic vacuum t,
      potentialDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t) ∈ (B).graph :=
  KFCausalProjectedSecondClockDecomposition.high_graph h hh c ε hε L
    (secondDerivative f ε h a p hε hh ha hb) (fun j => second_derivative_graph f ε h a p hε hh ha hb (KFCausalProjectedSecondClockDecomposition.highIndex j))

theorem hamiltonian_derivative_tendsto :
    Tendsto (finiteHamiltonianDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t) (𝓝[>] 0)
      (𝓝 (hamiltonianDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t)) := by
  apply (zeroProjection h hh).continuous.tendsto _ |>.comp
  exact tendsto_finset_sum Finset.univ (fun j _ =>
    tendsto_const_nhds.smul (second_derivative_tendsto f ε h a p hε hh ha hb j))

theorem potential_derivative_tendsto :
    Tendsto (finitePotentialDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t) (𝓝[>] 0)
      (𝓝 (potentialDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t)) := by
  apply (zeroProjection h hh).continuous.tendsto _ |>.comp
  exact tendsto_finset_sum Finset.univ (fun j _ =>
    tendsto_const_nhds.smul (second_derivative_tendsto f ε h a p hε hh ha hb _))

theorem clock_hamiltonian_graph :
    (ψ,hamiltonianDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t) ∈ (composition B H).graph :=
  (composition_graph _ _ _ _).mpr ⟨Hψ,
    input_hamiltonian_graph f ε h a p hε hh ha hb mass2 quartic vacuum t,
    hamiltonian_clock_graph f ε h a p hε hh ha hb mass2 quartic vacuum t⟩

include hb in
theorem clock_hamiltonian_domain : ψ ∈ (composition B H).domain :=
  LinearPMap.mem_domain_of_mem_graph (clock_hamiltonian_graph f ε h a p hε hh ha hb mass2 quartic vacuum t)

include hb in
theorem both_composition_domains : ψ ∈ (composition B H).domain ∧ ψ ∈ (composition H B).domain :=
  ⟨clock_hamiltonian_domain f ε h a p hε hh ha hb mass2 quartic vacuum t,
   hamiltonian_momentum_domain f ε h a p hε hh ha hb mass2 quartic vacuum t⟩

theorem clock_hamiltonian_graph_tendsto :
    Tendsto (fun δ => (ψδ δ,finiteHamiltonianDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t δ)) (𝓝[>] 0)
      (𝓝 (ψ,hamiltonianDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t)) :=
  (KFCausalCorrelatedClusteredInputGraphLimit.state_tendsto f ε h a p hε hh ha).prodMk_nhds
    (hamiltonian_derivative_tendsto f ε h a p hε hh ha hb mass2 quartic vacuum t)

theorem commutator_tendsto :
    Tendsto (fun δ => finiteHamiltonianDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t δ-
      finiteMomentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t δ) (𝓝[>] 0)
      (𝓝 (hamiltonianDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t-
        momentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t)) :=
  (hamiltonian_derivative_tendsto f ε h a p hε hh ha hb mass2 quartic vacuum t).sub
    (momentumHamiltonian_tendsto f ε h a p hε hh ha hb mass2 quartic vacuum t)

#print axioms second_derivative_graph
#print axioms second_clock_domain
#print axioms second_derivative_tendsto
#print axioms hamiltonian_clock_graph
#print axioms hamiltonian_clock_domain
#print axioms potential_clock_graph
#print axioms hamiltonian_derivative_tendsto
#print axioms potential_derivative_tendsto
#print axioms clock_hamiltonian_graph
#print axioms clock_hamiltonian_domain
#print axioms both_composition_domains
#print axioms clock_hamiltonian_graph_tendsto
#print axioms commutator_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredHamiltonianClockLimit

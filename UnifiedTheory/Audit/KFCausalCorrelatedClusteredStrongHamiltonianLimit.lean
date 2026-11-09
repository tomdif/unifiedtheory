/- The full interacting averaged Hamiltonian acts on both the clustered
state and its actual clock momentum. The original finite Hamiltonian
outputs converge, including the composition H B. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredAllSecondLimit
import UnifiedTheory.Audit.KFCausalFixedStrongHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredStrongHamiltonianLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredPhysicalClockLimit (lift)
open KFCausalCorrelatedClusteredAllSecondLimit
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalJointSecondPairing (secondWeighted)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
  (mass2 quartic vacuum t : ℝ)
local notation "hb₀" => original_strip ε h hε hb
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha
local notation "b" => KFCausalCorrelatedClusteredPureMomentumLimit.limitingMomentum f ε h a p hε hh ha
local notation "H" => hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t
local notation "c" => energyWeight mass2 quartic vacuum t

def inputHamiltonian : Hilbert := zeroProjection h hh
  (secondWeighted c (inputSeconds f ε h a p hε hh ha hb))

theorem input_hamiltonian_graph :
    (ψ,inputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t) ∈ (H).graph :=
  KFCausalFixedStrongHamiltonian.hamiltonian_graph ε h hε hh hb₀ mass2 quartic vacuum t ψ
    (KFCausalCorrelatedClusteredInputGraphLimit.limitingState_zeroSector f ε h a p hε hh ha)
    (KFCausalCorrelatedClusteredAllFactorLimit.output f ε h a p hε hh hb₀ ha)
    (inputSeconds f ε h a p hε hh ha hb)
    (KFCausalCorrelatedClusteredAllFactorLimit.output_graph f ε h a p hε hh hb₀ ha)
    (input_reverse_graph f ε h a p hε hh ha hb)

include hb in
theorem input_hamiltonian_domain : ψ ∈ (H).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (input_hamiltonian_graph f ε h a p hε hh ha hb mass2 quartic vacuum t)

def finiteInputHamiltonian (δ : ℝ) : Hilbert := zeroProjection h hh
  (secondWeighted c (KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteSeconds f ε h a p hε hh ha hb δ))

theorem inputHamiltonian_tendsto :
    Tendsto (finiteInputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t)
      (𝓝[>] 0) (𝓝 (inputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t)) := by
  apply (zeroProjection h hh).continuous.tendsto _ |>.comp
  exact tendsto_finset_sum Finset.univ (fun j _ =>
    (tendsto_const_nhds.smul (inputSeconds_tendsto f ε h a p hε hh ha hb j)))

def momentumHamiltonian : Hilbert := zeroProjection h hh
  (secondWeighted c (momentumSeconds f ε h a p hε hh ha hb))

theorem momentum_hamiltonian_graph :
    (b,momentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t) ∈ (H).graph :=
  KFCausalFixedStrongHamiltonian.hamiltonian_graph ε h hε hh hb₀ mass2 quartic vacuum t b
    (KFCausalCorrelatedClusteredPureMomentumLimit.momentum_zeroSector f ε h a p hε hh ha)
    (KFCausalCorrelatedClusteredAllFactorLimit.momentumOutput f ε h a p hε hh hb₀ ha)
    (momentumSeconds f ε h a p hε hh ha hb)
    (KFCausalCorrelatedClusteredAllFactorLimit.momentumOutput_graph f ε h a p hε hh hb₀ ha)
    (momentum_reverse_graph f ε h a p hε hh ha hb)

include hb in
theorem momentum_hamiltonian_domain : b ∈ (H).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (momentum_hamiltonian_graph f ε h a p hε hh ha hb mass2 quartic vacuum t)

def finiteMomentumHamiltonian (δ : ℝ) : Hilbert := zeroProjection h hh
  (secondWeighted c (KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteMomentumSeconds f ε h a p hε hh ha hb δ))

theorem momentumHamiltonian_tendsto :
    Tendsto (finiteMomentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t)
      (𝓝[>] 0) (𝓝 (momentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t)) := by
  apply (zeroProjection h hh).continuous.tendsto _ |>.comp
  exact tendsto_finset_sum Finset.univ (fun j _ =>
    (tendsto_const_nhds.smul (momentumSeconds_tendsto f ε h a p hε hh ha hb j)))

theorem hamiltonian_momentum_graph :
    (ψ,momentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t) ∈
      (composition H (pureMomentum ε hε h)).graph :=
  (composition_graph _ _ _ _).mpr ⟨b,
    KFCausalCorrelatedClusteredPureMomentumLimit.limiting_graph f ε h a p hε hh ha,
    momentum_hamiltonian_graph f ε h a p hε hh ha hb mass2 quartic vacuum t⟩

include hb in
theorem hamiltonian_momentum_domain : ψ ∈ (composition H (pureMomentum ε hε h)).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (hamiltonian_momentum_graph f ε h a p hε hh ha hb mass2 quartic vacuum t)

theorem strong_pairing :
    inner ℂ (inputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t) b =
      inner ℂ ψ (momentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t) :=
  KFCausalOrderedOperatorComposition.selfAdjoint_graph_pairing H
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_selfAdjoint ε hε h hh hb₀ mass2 quartic vacuum t)
    _ _ _ _ (input_hamiltonian_graph f ε h a p hε hh ha hb mass2 quartic vacuum t)
    (momentum_hamiltonian_graph f ε h a p hε hh ha hb mass2 quartic vacuum t)

theorem input_hamiltonian_graph_tendsto :
    Tendsto (fun δ => (KFCausalCorrelatedClusteredInputProfiles.finiteState f ε h a p hε hh ha δ,
      finiteInputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t δ))
      (𝓝[>] 0) (𝓝 (ψ,inputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t)) :=
  (KFCausalCorrelatedClusteredInputGraphLimit.state_tendsto f ε h a p hε hh ha).prodMk_nhds
    (inputHamiltonian_tendsto f ε h a p hε hh ha hb mass2 quartic vacuum t)

theorem momentum_hamiltonian_graph_tendsto :
    Tendsto (fun δ => (KFCausalCorrelatedClusteredPureMomentumLimit.finiteMomentum f ε h a p hε hh ha δ,
      finiteMomentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t δ))
      (𝓝[>] 0) (𝓝 (b,momentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t)) :=
  (KFCausalCorrelatedClusteredPureMomentumLimit.momentum_tendsto f ε h a p hε hh ha).prodMk_nhds
    (momentumHamiltonian_tendsto f ε h a p hε hh ha hb mass2 quartic vacuum t)

theorem hamiltonian_momentum_graph_tendsto :
    Tendsto (fun δ => (KFCausalCorrelatedClusteredInputProfiles.finiteState f ε h a p hε hh ha δ,
      finiteMomentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t δ))
      (𝓝[>] 0) (𝓝 (ψ,momentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t)) :=
  (KFCausalCorrelatedClusteredInputGraphLimit.state_tendsto f ε h a p hε hh ha).prodMk_nhds
    (momentumHamiltonian_tendsto f ε h a p hε hh ha hb mass2 quartic vacuum t)

theorem finite_input_hamiltonian_graph (δ : ℝ) (hδ : 0 < δ) :
    (KFCausalCorrelatedClusteredInputProfiles.finiteState f ε h a p hε hh ha δ,
      finiteInputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t δ) ∈ (H).graph := by
  have hg := KFCausalReciprocalNeutralStrongHamiltonian.hamiltonian_graph
    (count f) ε h (lift f a) (widths f δ) (lift f p) (coefficients f δ) (sources f) (polynomials f)
    hε (fun k => ha (index f k).1) hh (widths_admissible f δ hδ.le) hb mass2 quartic vacuum t
  simpa only [KFCausalCorrelatedClusteredInputProfiles.finiteState,finiteInputHamiltonian,secondWeighted,
    KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteSeconds,dif_pos hδ,
    KFCausalReciprocalNeutralStrongHamiltonian.hamiltonianOutput] using hg

theorem finite_momentum_hamiltonian_graph (δ : ℝ) (hδ : 0 < δ) :
    (KFCausalCorrelatedClusteredPureMomentumLimit.finiteMomentum f ε h a p hε hh ha δ,
      finiteMomentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t δ) ∈ (H).graph := by
  have hg := KFCausalReciprocalNeutralMomentumStrongHamiltonian.hamiltonian_graph
    (count f) ε h (lift f a) (widths f δ) (lift f p) (coefficients f δ) (sources f) (polynomials f)
    hε (fun k => ha (index f k).1) hh (widths_admissible f δ hδ.le) hb mass2 quartic vacuum t
  simpa only [KFCausalCorrelatedClusteredPureMomentumLimit.finiteMomentum,finiteMomentumHamiltonian,secondWeighted,
    KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteMomentumSeconds,dif_pos hδ,
    KFCausalReciprocalNeutralMomentumStrongHamiltonian.hamiltonianOutput] using hg

theorem finite_hamiltonian_momentum_graph (δ : ℝ) (hδ : 0 < δ) :
    (KFCausalCorrelatedClusteredInputProfiles.finiteState f ε h a p hε hh ha δ,
      finiteMomentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t δ) ∈
      (composition H (pureMomentum ε hε h)).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,
    KFCausalCorrelatedClusteredPureMomentumLimit.finite_graph f ε h a p hε hh ha δ hδ,
    finite_momentum_hamiltonian_graph f ε h a p hε hh ha hb mass2 quartic vacuum t δ hδ⟩

#print axioms input_hamiltonian_graph
#print axioms input_hamiltonian_domain
#print axioms inputHamiltonian_tendsto
#print axioms momentum_hamiltonian_graph
#print axioms momentum_hamiltonian_domain
#print axioms momentumHamiltonian_tendsto
#print axioms hamiltonian_momentum_graph
#print axioms hamiltonian_momentum_domain
#print axioms strong_pairing
#print axioms input_hamiltonian_graph_tendsto
#print axioms momentum_hamiltonian_graph_tendsto
#print axioms hamiltonian_momentum_graph_tendsto
#print axioms finite_input_hamiltonian_graph
#print axioms finite_momentum_hamiltonian_graph
#print axioms finite_hamiltonian_momentum_graph
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredStrongHamiltonianLimit

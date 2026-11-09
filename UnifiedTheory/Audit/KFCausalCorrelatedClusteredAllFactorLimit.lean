/- The physical clustered state and its actual pure-clock momentum
belong to the common natural domain of all eight energy factors.
Every original factor output converges strongly. This is a first-factor
domain result, not a strong-Hamiltonian second-action assertion. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumKineticLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredHalfMomentumLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredHalfClockLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumPotentialLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredAllFactorLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredInputGraphLimit (limitingState)
open KFCausalCorrelatedClusteredPureMomentumLimit (limitingMomentum)
open KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain commonEnergyDomain_iff)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalClockFloorPureClockMomentum (pureMomentum)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (ha : ∀ i, 0 < a i)
local notation "ψ" => limitingState f ε h a p hε hh ha
local notation "b" => limitingMomentum f ε h a p hε hh ha
local notation "V" => KFCausalCorrelatedClusteredPotentialGraphLimit.limitingOutput f ε h a p hε hh hb ha
local notation "W" => KFCausalCorrelatedClusteredMomentumPotentialLimit.limitingOutput f ε h a p hε hh hb ha
local notation "K" => KFCausalCorrelatedClusteredInputKineticLimit.limitingOutput f ε h a p hε hh ha
local notation "L" => KFCausalCorrelatedClusteredMomentumKineticLimit.limitingOutput f ε h a p hε hh ha

def output (j : Fin 8) : Hilbert :=
  ![KFCausalCorrelatedClusteredHalfClockLimit.limitingOutput f ε h a p hε hh hb ha,
    K 0,K 1,K 2,K 3,V 1,V 2,V 0] j

def momentumOutput (j : Fin 8) : Hilbert :=
  ![KFCausalCorrelatedClusteredHalfMomentumLimit.limitingOutput f ε h a p hε hh hb ha,
    L 0,L 1,L 2,L 3,W 1,W 2,W 0] j

theorem output_graph (j : Fin 8) : (ψ,output f ε h a p hε hh hb ha j) ∈
    (energyFactor ε hε h modelDirections pointField j).graph := by
  fin_cases j
  · exact KFCausalCorrelatedClusteredHalfClockLimit.limiting_graph f ε h a p hε hh hb ha
  · exact KFCausalCorrelatedClusteredInputKineticLimit.limiting_graph f ε h a p hε hh ha 0
  · exact KFCausalCorrelatedClusteredInputKineticLimit.limiting_graph f ε h a p hε hh ha 1
  · exact KFCausalCorrelatedClusteredInputKineticLimit.limiting_graph f ε h a p hε hh ha 2
  · exact KFCausalCorrelatedClusteredInputKineticLimit.limiting_graph f ε h a p hε hh ha 3
  · exact KFCausalCorrelatedClusteredInputGraphLimit.limiting_potential_graph f ε h a p hε hh ha hb 1
  · exact KFCausalCorrelatedClusteredInputGraphLimit.limiting_potential_graph f ε h a p hε hh ha hb 2
  · exact KFCausalCorrelatedClusteredInputGraphLimit.limiting_potential_graph f ε h a p hε hh ha hb 0

theorem momentumOutput_graph (j : Fin 8) : (b,momentumOutput f ε h a p hε hh hb ha j) ∈
    (energyFactor ε hε h modelDirections pointField j).graph := by
  fin_cases j
  · exact KFCausalCorrelatedClusteredHalfMomentumLimit.limiting_graph f ε h a p hε hh hb ha
  · exact KFCausalCorrelatedClusteredMomentumKineticLimit.limiting_graph f ε h a p hε hh ha 0
  · exact KFCausalCorrelatedClusteredMomentumKineticLimit.limiting_graph f ε h a p hε hh ha 1
  · exact KFCausalCorrelatedClusteredMomentumKineticLimit.limiting_graph f ε h a p hε hh ha 2
  · exact KFCausalCorrelatedClusteredMomentumKineticLimit.limiting_graph f ε h a p hε hh ha 3
  · exact KFCausalCorrelatedClusteredMomentumPotentialLimit.limiting_potential_graph f ε h a p hε hh hb ha 1
  · exact KFCausalCorrelatedClusteredMomentumPotentialLimit.limiting_potential_graph f ε h a p hε hh hb ha 2
  · exact KFCausalCorrelatedClusteredMomentumPotentialLimit.limiting_potential_graph f ε h a p hε hh hb ha 0

include hb in
theorem common_domains : ψ ∈ commonEnergyDomain ε hε h modelDirections pointField ∧
    b ∈ commonEnergyDomain ε hε h modelDirections pointField :=
  ⟨(commonEnergyDomain_iff ε hε h modelDirections pointField ψ).mpr (fun j =>
    LinearPMap.mem_domain_of_mem_graph (output_graph f ε h a p hε hh hb ha j)),
   (commonEnergyDomain_iff ε hε h modelDirections pointField b).mpr (fun j =>
    LinearPMap.mem_domain_of_mem_graph (momentumOutput_graph f ε h a p hε hh hb ha j))⟩

theorem composition_graph_limit (j : Fin 8) :
    (ψ,momentumOutput f ε h a p hε hh hb ha j) ∈
      (composition (energyFactor ε hε h modelDirections pointField j) (pureMomentum ε hε h)).graph :=
  (composition_graph _ _ _ _).mpr ⟨b,
    KFCausalCorrelatedClusteredPureMomentumLimit.limiting_graph f ε h a p hε hh ha,
    momentumOutput_graph f ε h a p hε hh hb ha j⟩

theorem output_tendsto (j : Fin 8) :
    Tendsto (fun δ => KFCausalCorrelatedClusteredPhysicalCauchy.finiteOutput f ε h a p hε hh hb ha δ j)
      (𝓝[>] 0) (𝓝 (output f ε h a p hε hh hb ha j)) := by
  fin_cases j
  · exact KFCausalCorrelatedClusteredHalfClockLimit.output_tendsto f ε h a p hε hh hb ha
  · exact KFCausalCorrelatedClusteredInputKineticLimit.output_tendsto f ε h a p hε hh ha hb 0
  · exact KFCausalCorrelatedClusteredInputKineticLimit.output_tendsto f ε h a p hε hh ha hb 1
  · exact KFCausalCorrelatedClusteredInputKineticLimit.output_tendsto f ε h a p hε hh ha hb 2
  · exact KFCausalCorrelatedClusteredInputKineticLimit.output_tendsto f ε h a p hε hh ha hb 3
  · exact KFCausalCorrelatedClusteredPotentialGraphLimit.output_tendsto f ε h a p hε hh hb ha 1
  · exact KFCausalCorrelatedClusteredPotentialGraphLimit.output_tendsto f ε h a p hε hh hb ha 2
  · exact KFCausalCorrelatedClusteredPotentialGraphLimit.output_tendsto f ε h a p hε hh hb ha 0

theorem momentumOutput_tendsto (j : Fin 8) :
    Tendsto (fun δ => KFCausalCorrelatedClusteredMomentumPotentialProfiles.finiteMomentumOutput f ε h a p hε hh hb ha δ j)
      (𝓝[>] 0) (𝓝 (momentumOutput f ε h a p hε hh hb ha j)) := by
  fin_cases j
  · exact KFCausalCorrelatedClusteredHalfMomentumLimit.output_tendsto f ε h a p hε hh hb ha
  · exact KFCausalCorrelatedClusteredMomentumKineticLimit.output_tendsto f ε h a p hε hh ha hb 0
  · exact KFCausalCorrelatedClusteredMomentumKineticLimit.output_tendsto f ε h a p hε hh ha hb 1
  · exact KFCausalCorrelatedClusteredMomentumKineticLimit.output_tendsto f ε h a p hε hh ha hb 2
  · exact KFCausalCorrelatedClusteredMomentumKineticLimit.output_tendsto f ε h a p hε hh ha hb 3
  · exact KFCausalCorrelatedClusteredMomentumPotentialLimit.output_tendsto f ε h a p hε hh hb ha 1
  · exact KFCausalCorrelatedClusteredMomentumPotentialLimit.output_tendsto f ε h a p hε hh hb ha 2
  · exact KFCausalCorrelatedClusteredMomentumPotentialLimit.output_tendsto f ε h a p hε hh hb ha 0

#print axioms output_graph
#print axioms momentumOutput_graph
#print axioms common_domains
#print axioms composition_graph_limit
#print axioms output_tendsto
#print axioms momentumOutput_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredAllFactorLimit

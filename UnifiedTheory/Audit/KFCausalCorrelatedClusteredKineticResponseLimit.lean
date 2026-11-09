/- Both kinetic/clock-momentum composition orders and their actual
form response on the physical clustered limit. The response constant
1/(4*epsilon) is independent of the family and all polynomial degrees. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumKineticLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredKineticResponseLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorPureClockKinetic (correction)
open KFCausalClockFloorTrialMomentum (clockMomentum)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalCorrelatedClusteredInputKineticLimit (energyFactor_kinetic)
open KFCausalCoherentFactorResponseBounds (kineticIndex)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha
local notation "b" => KFCausalCorrelatedClusteredPureMomentumLimit.limitingMomentum f ε h a p hε hh ha
local notation "K" => KFCausalCorrelatedClusteredInputKineticLimit.limitingOutput f ε h a p hε hh ha
local notation "L" => KFCausalCorrelatedClusteredMomentumKineticLimit.limitingOutput f ε h a p hε hh ha

private theorem input_graph (j : Fin 4) : (ψ,K j) ∈ (clockMomentum ε h (modelDirections j)).graph := by
  rw [← energyFactor_kinetic ε h hε j]
  exact KFCausalCorrelatedClusteredInputKineticLimit.limiting_graph f ε h a p hε hh ha j

private theorem momentum_graph (j : Fin 4) : (b,L j) ∈ (clockMomentum ε h (modelDirections j)).graph := by
  rw [← energyFactor_kinetic ε h hε j]
  exact KFCausalCorrelatedClusteredMomentumKineticLimit.limiting_graph f ε h a p hε hh ha j

theorem composition_graph_limit (j : Fin 4) :
    (ψ,L j) ∈ (composition (clockMomentum ε h (modelDirections j)) (pureMomentum ε hε h)).graph :=
  (composition_graph _ _ _ _).mpr ⟨b,
    KFCausalCorrelatedClusteredPureMomentumLimit.limiting_graph f ε h a p hε hh ha,
    momentum_graph f ε h a p hε hh ha j⟩

theorem reverse_graph (j : Fin 4) :
    (K j,L j+correction ε hε h (K j)) ∈ (pureMomentum ε hε h).graph :=
  KFCausalClockFloorPureClockKinetic.kinetic_momentum_graph ε hε h (modelDirections j) hh ψ (K j) b (L j)
    (input_graph f ε h a p hε hh ha j)
    (KFCausalCorrelatedClusteredPureMomentumLimit.limiting_graph f ε h a p hε hh ha)
    (momentum_graph f ε h a p hε hh ha j)

theorem reverse_composition_graph (j : Fin 4) :
    (ψ,L j+correction ε hε h (K j)) ∈
      (composition (pureMomentum ε hε h) (clockMomentum ε h (modelDirections j))).graph :=
  (composition_graph _ _ _ _).mpr ⟨K j,input_graph f ε h a p hε hh ha j,
    reverse_graph f ε h a p hε hh ha j⟩

theorem both_composition_domains (j : Fin 4) :
    ψ ∈ (composition (clockMomentum ε h (modelDirections j)) (pureMomentum ε hε h)).domain ∧
      ψ ∈ (composition (pureMomentum ε hε h) (clockMomentum ε h (modelDirections j))).domain :=
  ⟨LinearPMap.mem_domain_of_mem_graph (composition_graph_limit f ε h a p hε hh ha j),
   LinearPMap.mem_domain_of_mem_graph (reverse_composition_graph f ε h a p hε hh ha j)⟩

theorem response_identity (j : Fin 4) : (-2/h)*(inner ℂ (K j) (L j)).im =
    KFCausalClockFloorPureClockKineticResponse.response ε hε (K j) :=
  KFCausalClockFloorPureClockKineticResponse.weak_response ε hε h hh (modelDirections j) ψ (K j) b (L j)
    (input_graph f ε h a p hε hh ha j)
    (KFCausalCorrelatedClusteredPureMomentumLimit.limiting_graph f ε h a p hε hh ha)
    (momentum_graph f ε h a p hε hh ha j)

theorem response_bounds (j : Fin 4) :
    0 ≤ (-2/h)*(inner ℂ (K j) (L j)).im ∧
      (-2/h)*(inner ℂ (K j) (L j)).im ≤ (1/(4*ε))*‖K j‖^2 := by
  rw [response_identity f ε h a p hε hh ha j]
  exact KFCausalClockFloorPureClockKineticResponse.response_bounds ε hε (K j)

theorem response_tendsto (hb : |h| ≤ 2*Real.pi*ε/3) (j : Fin 4) :
    Tendsto (fun δ => (-2/h)*(inner ℂ
      (KFCausalCorrelatedClusteredPhysicalCauchy.finiteOutput f ε h a p hε hh hb ha δ (kineticIndex j))
      (KFCausalCorrelatedClusteredMomentumPotentialProfiles.finiteMomentumOutput f ε h a p hε hh hb ha δ (kineticIndex j))).im)
      (𝓝[>] 0) (𝓝 ((-2/h)*(inner ℂ (K j) (L j)).im)) := by
  have hp := (KFCausalCorrelatedClusteredInputKineticLimit.output_tendsto f ε h a p hε hh ha hb j).inner (𝕜 := ℂ)
    (KFCausalCorrelatedClusteredMomentumKineticLimit.output_tendsto f ε h a p hε hh ha hb j)
  exact ((Complex.continuous_im.tendsto _).comp hp).const_mul (-2/h)

#print axioms composition_graph_limit
#print axioms reverse_graph
#print axioms reverse_composition_graph
#print axioms both_composition_domains
#print axioms response_identity
#print axioms response_bounds
#print axioms response_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredKineticResponseLimit

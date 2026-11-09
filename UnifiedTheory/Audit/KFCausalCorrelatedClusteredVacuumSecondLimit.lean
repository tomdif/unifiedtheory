/- The natural vacuum second action exists on both the clustered state
and its actual pure-clock momentum. The original finite second outputs
converge to these constructed actions; the two matter seconds remain separate. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredDoubleVacuumLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockSecondLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredAllFactorLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredVacuumSecondLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential reversedExponential)
open KFCausalClockFloorVacuumSquare (square)
open KFCausalVacuumParameterRescale (doubled_square_graph doubled_reverse_graph)
open KFCausalCorrelatedClusteredDoubleVacuumLimit
  (limitingOutput limitingMomentumOutput output_tendsto momentumOutput_tendsto limiting_graph limitingMomentum_graph)
open KFCausalCorrelatedClusteredOriginalKineticSeconds (finiteSeconds finiteMomentumSeconds)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor factor_pairing)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha
local notation "B" => KFCausalCorrelatedClusteredPureMomentumLimit.limitingMomentum f ε h a p hε hh ha
local notation "A" => KFCausalCorrelatedClusteredAllFactorLimit.output f ε h a p hε hh hb₀ ha
local notation "M" => KFCausalCorrelatedClusteredAllFactorLimit.momentumOutput f ε h a p hε hh hb₀ ha
local notation "U" => KFCausalCorrelatedClusteredDoubleVacuumProfiles.finiteOutput f ε h a p hε hh ha hb
local notation "V" => KFCausalCorrelatedClusteredDoubleVacuumProfiles.finiteMomentumOutput f ε h a p hε hh ha hb

def inputSecond : Hilbert := inverseL ε hε (limitingOutput f ε h a p hε hh ha hb)
def momentumSecond : Hilbert := inverseL ε hε (limitingMomentumOutput f ε h a p hε hh ha hb)

theorem input_second_graph : (ψ,inputSecond f ε h a p hε hh ha hb) ∈ (square ε hε h).graph :=
  doubled_square_graph ε hε h _ _ (limiting_graph f ε h a p hε hh ha hb)

theorem momentum_second_graph : (B,momentumSecond f ε h a p hε hh ha hb) ∈ (square ε hε h).graph :=
  doubled_square_graph ε hε h _ _ (limitingMomentum_graph f ε h a p hε hh ha hb)

include hb in
theorem second_domains : ψ ∈ (square ε hε h).domain ∧ B ∈ (square ε hε h).domain :=
  ⟨LinearPMap.mem_domain_of_mem_graph (input_second_graph f ε h a p hε hh ha hb),
   LinearPMap.mem_domain_of_mem_graph (momentum_second_graph f ε h a p hε hh ha hb)⟩

theorem input_reverse_graph : (A 7,inputSecond f ε h a p hε hh ha hb) ∈
    (reverseFactor ε hε h modelDirections pointField 7).graph :=
  doubled_reverse_graph ε hε h ψ (A 7) _
    (KFCausalCorrelatedClusteredAllFactorLimit.output_graph f ε h a p hε hh hb₀ ha 7)
    (limiting_graph f ε h a p hε hh ha hb)

theorem momentum_reverse_graph : (M 7,momentumSecond f ε h a p hε hh ha hb) ∈
    (reverseFactor ε hε h modelDirections pointField 7).graph :=
  doubled_reverse_graph ε hε h B (M 7) _
    (KFCausalCorrelatedClusteredAllFactorLimit.momentumOutput_graph f ε h a p hε hh hb₀ ha 7)
    (limitingMomentum_graph f ε h a p hε hh ha hb)

theorem finiteSeconds_eq (δ : ℝ) (hδ : 0 < δ) :
    finiteSeconds f ε h a p hε hh ha hb δ 7 = inverseL ε hε (U δ) := by
  have hz := doubled_reverse_graph ε hε h _ _ _
    (KFCausalCorrelatedClusteredInputGraphLimit.finite_output_graph f ε h a p hε hh ha hb₀ δ hδ 7)
    (KFCausalCorrelatedClusteredDoubleVacuumProfiles.finiteOutput_graph f ε h a p hε hh ha hb δ hδ)
  exact (reversedExponential ε hε h).mem_graph_snd_inj'
    (KFCausalCorrelatedClusteredOriginalKineticSeconds.finite_reverse_graph f ε h a p hε hh ha hb δ hδ 7) hz rfl

theorem finiteMomentumSeconds_eq (δ : ℝ) (hδ : 0 < δ) :
    finiteMomentumSeconds f ε h a p hε hh ha hb δ 7 = inverseL ε hε (V δ) := by
  have hz := doubled_reverse_graph ε hε h _ _ _
    (KFCausalCorrelatedClusteredMomentumPotentialProfiles.finiteMomentumOutput_graph f ε h a p hε hh hb₀ ha δ hδ 7)
    (KFCausalCorrelatedClusteredDoubleVacuumProfiles.finiteMomentumOutput_graph f ε h a p hε hh ha hb δ hδ)
  exact (reversedExponential ε hε h).mem_graph_snd_inj'
    (KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteMomentum_reverse_graph f ε h a p hε hh ha hb δ hδ 7) hz rfl

theorem inputSecond_tendsto : Tendsto (fun δ => finiteSeconds f ε h a p hε hh ha hb δ 7)
    (𝓝[>] 0) (𝓝 (inputSecond f ε h a p hε hh ha hb)) := by
  have ht := ((inverseL ε hε).continuous.tendsto (limitingOutput f ε h a p hε hh ha hb)).comp
    (output_tendsto f ε h a p hε hh ha hb)
  apply Tendsto.congr' _ ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finiteSeconds_eq f ε h a p hε hh ha hb δ hδ).symm

theorem momentumSecond_tendsto : Tendsto (fun δ => finiteMomentumSeconds f ε h a p hε hh ha hb δ 7)
    (𝓝[>] 0) (𝓝 (momentumSecond f ε h a p hε hh ha hb)) := by
  have ht := ((inverseL ε hε).continuous.tendsto (limitingMomentumOutput f ε h a p hε hh ha hb)).comp
    (momentumOutput_tendsto f ε h a p hε hh ha hb)
  apply Tendsto.congr' _ ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finiteMomentumSeconds_eq f ε h a p hε hh ha hb δ hδ).symm

theorem input_second_graph_tendsto : Tendsto (fun δ =>
    (KFCausalCorrelatedClusteredInputProfiles.finiteState f ε h a p hε hh ha δ,
      finiteSeconds f ε h a p hε hh ha hb δ 7)) (𝓝[>] 0)
    (𝓝 (ψ,inputSecond f ε h a p hε hh ha hb)) :=
  (KFCausalCorrelatedClusteredInputGraphLimit.state_tendsto f ε h a p hε hh ha).prodMk_nhds
    (inputSecond_tendsto f ε h a p hε hh ha hb)

theorem momentum_second_graph_tendsto : Tendsto (fun δ =>
    (KFCausalCorrelatedClusteredPureMomentumLimit.finiteMomentum f ε h a p hε hh ha δ,
      finiteMomentumSeconds f ε h a p hε hh ha hb δ 7)) (𝓝[>] 0)
    (𝓝 (B,momentumSecond f ε h a p hε hh ha hb)) :=
  (KFCausalCorrelatedClusteredPureMomentumLimit.momentum_tendsto f ε h a p hε hh ha).prodMk_nhds
    (momentumSecond_tendsto f ε h a p hε hh ha hb)

theorem input_form_pairing (q r : Hilbert)
    (hqr : (q,r) ∈ (energyFactor ε hε h modelDirections pointField 7).graph) :
    inner ℂ (A 7) r = inner ℂ (inputSecond f ε h a p hε hh ha hb) q :=
  factor_pairing ε hε h modelDirections pointField 7 _ _ q r
    (input_reverse_graph f ε h a p hε hh ha hb) hqr

theorem momentum_form_pairing (q r : Hilbert)
    (hqr : (q,r) ∈ (energyFactor ε hε h modelDirections pointField 7).graph) :
    inner ℂ (M 7) r = inner ℂ (momentumSecond f ε h a p hε hh ha hb) q :=
  factor_pairing ε hε h modelDirections pointField 7 _ _ q r
    (momentum_reverse_graph f ε h a p hε hh ha hb) hqr

#print axioms input_second_graph
#print axioms momentum_second_graph
#print axioms second_domains
#print axioms input_reverse_graph
#print axioms momentum_reverse_graph
#print axioms finiteSeconds_eq
#print axioms finiteMomentumSeconds_eq
#print axioms inputSecond_tendsto
#print axioms momentumSecond_tendsto
#print axioms input_second_graph_tendsto
#print axioms momentum_second_graph_tendsto
#print axioms input_form_pairing
#print axioms momentum_form_pairing
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredVacuumSecondLimit

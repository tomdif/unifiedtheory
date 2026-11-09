/- Clock derivatives of the original clock and four kinetic second
outputs converge strongly. The actual limiting graphs use bounded
commutator corrections and retain the full correlated family. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredFiniteSecondPureClock
import UnifiedTheory.Audit.KFCausalClockFloorPureClockKineticSquare
import UnifiedTheory.Audit.KFCausalClockFloorPureClockClockSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockKineticSecondPureLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredFiniteSecondPureClock
open KFCausalCorrelatedClusteredOriginalKineticSeconds (finiteSeconds finiteMomentumSeconds)
open KFCausalCorrelatedClusteredAllSecondLimit (inputSeconds momentumSeconds inputSeconds_tendsto momentumSeconds_tendsto)
open KFCausalClockFloorPureClockMomentum (pureMomentum pure_closed)
open KFCausalClockFloorPureClockKinetic (correction)
open KFCausalCoherentFactorResponseBounds (kineticIndex)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalOrderedOperatorComposition (composition composition_graph)

theorem kinetic_square_eq (ε : ℝ) (hε : 0 < ε) (h : ℝ) (j : Fin 4) :
    composition (reverseFactor ε hε h modelDirections pointField (kineticIndex j))
      (energyFactor ε hε h modelDirections pointField (kineticIndex j)) =
        KFCausalClockFloorKineticSquare.square ε h (modelDirections j) := by fin_cases j <;> rfl

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
local notation "B" => pureMomentum ε hε h
local notation "K" => correction ε hε h
local notation "S" => finiteSeconds f ε h a p hε hh ha hb
local notation "T" => finiteMomentumSeconds f ε h a p hε hh ha hb
local notation "L" => inputSeconds f ε h a p hε hh ha hb
local notation "M" => momentumSeconds f ε h a p hε hh ha hb
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha

theorem finite_clock_eq (δ : ℝ) (hδ : 0 < δ) :
    finiteDerivative f ε h a p hε hh ha hb δ 0=T δ 0-K (S δ 0)-K (S δ 0) :=
  (B).mem_graph_snd_inj' (finite_derivative_graph f ε h a p hε hh ha hb δ hδ 0)
    (KFCausalClockFloorPureClockClockSquare.square_momentum_graph_of_domain ε hε h hh _ _ _ _
      (KFCausalCorrelatedClusteredPureMomentumLimit.finite_graph f ε h a p hε hh ha δ hδ)
      (finite_second_graph f ε h a p hε hh ha hb δ hδ 0)
      (finite_momentum_second_graph f ε h a p hε hh ha hb δ hδ 0)
      (finite_domain f ε h a p hε hh ha hb δ hδ 0)) rfl

theorem finite_kinetic_eq (δ : ℝ) (hδ : 0 < δ) (j : Fin 4) :
    finiteDerivative f ε h a p hε hh ha hb δ (kineticIndex j)=
      T δ (kineticIndex j)+K (S δ (kineticIndex j))+K (S δ (kineticIndex j)) := by
  have hs := finite_second_graph f ε h a p hε hh ha hb δ hδ (kineticIndex j)
  have ht := finite_momentum_second_graph f ε h a p hε hh ha hb δ hδ (kineticIndex j)
  rw [kinetic_square_eq] at hs ht
  exact (B).mem_graph_snd_inj' (finite_derivative_graph f ε h a p hε hh ha hb δ hδ (kineticIndex j))
    (KFCausalClockFloorPureClockKineticSquare.square_momentum_graph ε hε h hh (modelDirections j) _ _ _ _
      (KFCausalCorrelatedClusteredPureMomentumLimit.finite_graph f ε h a p hε hh ha δ hδ) hs ht) rfl

def clockDerivative : Hilbert := M 0-K (L 0)-K (L 0)
def kineticDerivative (j : Fin 4) : Hilbert := M (kineticIndex j)+K (L (kineticIndex j))+K (L (kineticIndex j))

theorem clock_derivative_tendsto :
    Tendsto (fun δ => finiteDerivative f ε h a p hε hh ha hb δ 0) (𝓝[>] 0)
      (𝓝 (clockDerivative f ε h a p hε hh ha hb)) := by
  have hs := (K).continuous.tendsto _ |>.comp (inputSeconds_tendsto f ε h a p hε hh ha hb 0)
  apply Tendsto.congr' _ (((momentumSeconds_tendsto f ε h a p hε hh ha hb 0).sub hs).sub hs)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finite_clock_eq f ε h a p hε hh ha hb δ hδ).symm

theorem kinetic_derivative_tendsto (j : Fin 4) :
    Tendsto (fun δ => finiteDerivative f ε h a p hε hh ha hb δ (kineticIndex j)) (𝓝[>] 0)
      (𝓝 (kineticDerivative f ε h a p hε hh ha hb j)) := by
  have hs := (K).continuous.tendsto _ |>.comp (inputSeconds_tendsto f ε h a p hε hh ha hb (kineticIndex j))
  apply Tendsto.congr' _ (((momentumSeconds_tendsto f ε h a p hε hh ha hb (kineticIndex j)).add hs).add hs)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finite_kinetic_eq f ε h a p hε hh ha hb δ hδ j).symm

theorem clock_derivative_graph : (L 0,clockDerivative f ε h a p hε hh ha hb) ∈ (B).graph := by
  apply (pure_closed ε hε h hh).mem_of_tendsto
    ((inputSeconds_tendsto f ε h a p hε hh ha hb 0).prodMk_nhds (clock_derivative_tendsto f ε h a p hε hh ha hb))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_derivative_graph f ε h a p hε hh ha hb δ hδ 0

theorem kinetic_derivative_graph (j : Fin 4) :
    (L (kineticIndex j),kineticDerivative f ε h a p hε hh ha hb j) ∈ (B).graph := by
  apply (pure_closed ε hε h hh).mem_of_tendsto
    ((inputSeconds_tendsto f ε h a p hε hh ha hb (kineticIndex j)).prodMk_nhds
      (kinetic_derivative_tendsto f ε h a p hε hh ha hb j))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_derivative_graph f ε h a p hε hh ha hb δ hδ (kineticIndex j)

theorem clock_composition_graph : (ψ,clockDerivative f ε h a p hε hh ha hb) ∈
    (composition B (composition (reverseFactor ε hε h modelDirections pointField 0)
      (energyFactor ε hε h modelDirections pointField 0))).graph :=
  (composition_graph _ _ _ _).mpr ⟨L 0,
    KFCausalCorrelatedClusteredClockSecondLimit.input_second_graph f ε h a p hε hh ha hb,
    clock_derivative_graph f ε h a p hε hh ha hb⟩

theorem kinetic_composition_graph (j : Fin 4) : (ψ,kineticDerivative f ε h a p hε hh ha hb j) ∈
    (composition B (composition (reverseFactor ε hε h modelDirections pointField (kineticIndex j))
      (energyFactor ε hε h modelDirections pointField (kineticIndex j)))).graph :=
  (composition_graph _ _ _ _).mpr ⟨L (kineticIndex j),
    (by fin_cases j <;> exact KFCausalCorrelatedClusteredPhysicalKineticSeconds.input_second_graph f ε h a p hε hh ha _),
    kinetic_derivative_graph f ε h a p hε hh ha hb j⟩

#print axioms kinetic_square_eq
#print axioms finite_clock_eq
#print axioms finite_kinetic_eq
#print axioms clock_derivative_tendsto
#print axioms kinetic_derivative_tendsto
#print axioms clock_derivative_graph
#print axioms kinetic_derivative_graph
#print axioms clock_composition_graph
#print axioms kinetic_composition_graph
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockKineticSecondPureLimit

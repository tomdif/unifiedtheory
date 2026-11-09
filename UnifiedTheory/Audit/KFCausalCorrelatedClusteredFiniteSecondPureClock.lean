/- Actual clock derivatives of the original finite second outputs.
Every finite derivative domain is inherited from the proved full neutral
polynomial family, before any clustered limit is taken. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralHamiltonianPureDomain
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredAllSecondLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredFiniteSecondPureClock
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredPhysicalClockLimit (lift)
open KFCausalCorrelatedClusteredOriginalKineticSeconds (finiteSeconds finiteMomentumSeconds)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "B" => pureMomentum ε hε h
local notation "F" => KFCausalCorrelatedClusteredInputProfiles.finiteState f ε h a p hε hh ha
local notation "M" => KFCausalCorrelatedClusteredPureMomentumLimit.finiteMomentum f ε h a p hε hh ha
local notation "S" => finiteSeconds f ε h a p hε hh ha hb
local notation "T" => finiteMomentumSeconds f ε h a p hε hh ha hb

theorem finite_domain (δ : ℝ) (hδ : 0 < δ) (j : Fin 8) : S δ j ∈ (B).domain := by
  rw [finiteSeconds,dif_pos hδ]
  exact KFCausalReciprocalNeutralHamiltonianPureDomain.seconds_domain (count f) ε h
    (lift f a) (widths f δ) (lift f p) (coefficients f δ) (sources f) (polynomials f)
    hε (fun k => ha (index f k).1) hh (widths_admissible f δ hδ.le) hb j

def finiteDerivative (δ : ℝ) (j : Fin 8) : Hilbert := if hδ : 0 < δ then
  (B) ⟨S δ j,finite_domain f ε h a p hε hh ha hb δ hδ j⟩ else 0

theorem finite_derivative_graph (δ : ℝ) (hδ : 0 < δ) (j : Fin 8) :
    (S δ j,finiteDerivative f ε h a p hε hh ha hb δ j) ∈ (B).graph := by
  rw [finiteDerivative,dif_pos hδ]
  exact (B).mem_graph ⟨S δ j,finite_domain f ε h a p hε hh ha hb δ hδ j⟩

theorem finite_second_graph (δ : ℝ) (hδ : 0 < δ) (j : Fin 8) :
    (F δ,S δ j) ∈ (composition (reverseFactor ε hε h modelDirections pointField j)
      (energyFactor ε hε h modelDirections pointField j)).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,
    KFCausalCorrelatedClusteredInputGraphLimit.finite_output_graph f ε h a p hε hh ha hb₀ δ hδ j,
    KFCausalCorrelatedClusteredOriginalKineticSeconds.finite_reverse_graph f ε h a p hε hh ha hb δ hδ j⟩

theorem finite_momentum_second_graph (δ : ℝ) (hδ : 0 < δ) (j : Fin 8) :
    (M δ,T δ j) ∈ (composition (reverseFactor ε hε h modelDirections pointField j)
      (energyFactor ε hε h modelDirections pointField j)).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,
    KFCausalCorrelatedClusteredMomentumPotentialProfiles.finiteMomentumOutput_graph f ε h a p hε hh hb₀ ha δ hδ j,
    KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteMomentum_reverse_graph f ε h a p hε hh ha hb δ hδ j⟩

#print axioms finite_domain
#print axioms finite_derivative_graph
#print axioms finite_second_graph
#print axioms finite_momentum_second_graph
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredFiniteSecondPureClock

/- Both complete matter second actions on the actual clustered clock momentum.
The finite spectral endpoints converge with their distinct shifts;
each unbounded intermediate graph is closed separately. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumMatterSpectralProfiles
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredQuarticLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMatterSecondLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumMatterSecondLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredMomentumMatterSpectralProfiles (finiteSpectral finiteSpectral_coe finiteMomentumSeconds_eq)
open KFCausalReciprocalNeutralMatterSpectral (matterIndex)
open KFCausalMixedFieldGaussianStrip (degree)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalPhysicalField (physicalField)
open KFCausalTransverseFieldSquare (fieldSquare)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorExponential (longitudinalExponential longitudinal_exponential_closed)
open KFCausalClockFloorMatterClosure (reversedMatterFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalOrderedOperatorComposition (composition composition_graph)

open KFCausalCorrelatedClusteredMatterSecondLimit (matterOperator reverseFactor_matter)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "F" => KFCausalCorrelatedClusteredMomentumPotentialProfiles.finiteMomentumOutput f ε h a p hε hh hb₀ ha
local notation "L" => KFCausalCorrelatedClusteredAllFactorLimit.momentumOutput f ε h a p hε hh hb₀ ha
local notation "ψ" => KFCausalCorrelatedClusteredPureMomentumLimit.limitingMomentum f ε h a p hε hh ha

def finiteIntermediate (δ : ℝ) : Fin 2 → Hilbert :=
  ![F δ 6,KFCausalCorrelatedClusteredQuarticIntermediates.finiteMomentumQuartic f ε h a p hε hh ha hb δ]

def limitingIntermediate : Fin 2 → Hilbert :=
  ![L 6,KFCausalCorrelatedClusteredQuarticLimit.momentumQuartic f ε h a p hε hh ha hb]

theorem finite_field_graph (δ : ℝ) (hδ : 0 < δ) (j : Fin 2) :
    (F δ (matterIndex j),finiteIntermediate f ε h a p hε hh ha hb δ j) ∈ (matterOperator j).graph := by
  fin_cases j
  · exact KFCausalCorrelatedClusteredQuarticLimit.linear_graph_of_square _ _ _
      (KFCausalCorrelatedClusteredMomentumPotentialLimit.finite_field_graph f ε h a p hε hh hb₀ ha δ hδ)
      (KFCausalCorrelatedClusteredMomentumPotentialLimit.finite_square_graph f ε h a p hε hh hb₀ ha δ hδ)
  · exact KFCausalCorrelatedClusteredQuarticIntermediates.finiteMomentum_graph f ε h a p hε hh ha hb δ hδ

theorem finite_exponential_graph (δ : ℝ) (hδ : 0 < δ) (j : Fin 2) :
    (finiteIntermediate f ε h a p hε hh ha hb δ j,finiteSpectral f ε h a p hε hh ha hb δ j) ∈
      (longitudinalExponential ε hε h (1/2)).graph := by
  apply KFCausalInverseClockSpectralRecovery.matter_exponential_graph ε hε h (matterOperator j)
    (F δ (matterIndex j)) _ _ (finite_field_graph f ε h a p hε hh ha hb δ hδ j)
  have hr := KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteMomentum_reverse_graph f ε h a p hε hh ha hb δ hδ (matterIndex j)
  rw [finiteMomentumSeconds_eq f ε h a p hε hh ha hb δ hδ j,reverseFactor_matter] at hr
  exact hr

theorem intermediate_tendsto (j : Fin 2) :
    Tendsto (fun δ => finiteIntermediate f ε h a p hε hh ha hb δ j) (𝓝[>] 0)
      (𝓝 (limitingIntermediate f ε h a p hε hh ha hb j)) := by
  fin_cases j
  · exact KFCausalCorrelatedClusteredAllFactorLimit.momentumOutput_tendsto f ε h a p hε hh hb₀ ha 6
  · exact KFCausalCorrelatedClusteredQuarticLimit.momentumQuartic_tendsto f ε h a p hε hh ha hb

theorem intermediate_graph (j : Fin 2) :
    (L (matterIndex j),limitingIntermediate f ε h a p hε hh ha hb j) ∈ (matterOperator j).graph := by
  fin_cases j
  · exact KFCausalCorrelatedClusteredQuarticLimit.momentum_linear_intermediate_graph f ε h a p hε hh ha hb
  · exact KFCausalCorrelatedClusteredQuarticLimit.momentumQuartic_graph f ε h a p hε hh ha hb

theorem spectral_exists_limit (j : Fin 2) :
    ∃ v : Hilbert, Tendsto (fun δ => finiteSpectral f ε h a p hε hh ha hb δ j) (𝓝[>] 0) (𝓝 v) :=
  KFCausalCorrelatedClusteredMixedFieldLimits.momentum_exists_limit f (groundWidth h) (neutralWidth h)
    ε (-h) (-h/2) a p (degree j) (groundWidth_positive h hh) (neutralWidth_positive h hh)
    (neutralWidth_bound h) hε ha (by simpa only [abs_neg] using hb)
    (KFCausalCorrelatedClusteredPhysicalClockLimit.shift_bound ε h hb₀) (neg_ne_zero.mpr hh) h
    (fun δ => finiteSpectral f ε h a p hε hh ha hb δ j)
    (fun δ hδ => finiteSpectral_coe f ε h a p hε hh ha hb δ hδ j)

def limitingSpectral (j : Fin 2) : Hilbert := Classical.choose (spectral_exists_limit f ε h a p hε hh ha hb j)

theorem spectral_tendsto (j : Fin 2) :
    Tendsto (fun δ => finiteSpectral f ε h a p hε hh ha hb δ j) (𝓝[>] 0)
      (𝓝 (limitingSpectral f ε h a p hε hh ha hb j)) :=
  Classical.choose_spec (spectral_exists_limit f ε h a p hε hh ha hb j)

theorem spectral_graph (j : Fin 2) :
    (limitingIntermediate f ε h a p hε hh ha hb j,limitingSpectral f ε h a p hε hh ha hb j) ∈
      (longitudinalExponential ε hε h (1/2)).graph := by
  apply (longitudinal_exponential_closed ε hε h (1/2)).mem_of_tendsto
    ((intermediate_tendsto f ε h a p hε hh ha hb j).prodMk_nhds (spectral_tendsto f ε h a p hε hh ha hb j))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_exponential_graph f ε h a p hε hh ha hb δ hδ j

def second (j : Fin 2) : Hilbert := inverseL ε hε (limitingSpectral f ε h a p hε hh ha hb j)

theorem reverse_graph (j : Fin 2) :
    (L (matterIndex j),second f ε h a p hε hh ha hb j) ∈
      (reverseFactor ε hε h modelDirections pointField (matterIndex j)).graph := by
  rw [reverseFactor_matter]
  exact (composition_graph _ _ _ _).mpr ⟨_,intermediate_graph f ε h a p hε hh ha hb j,
    (KFCausalClockFloorVacuumSquare.reversed_graph ε hε h _ _).mpr
      ⟨_,spectral_graph f ε h a p hε hh ha hb j,rfl⟩⟩

theorem second_graph (j : Fin 2) : (ψ,second f ε h a p hε hh ha hb j) ∈
    (composition (reverseFactor ε hε h modelDirections pointField (matterIndex j))
      (energyFactor ε hε h modelDirections pointField (matterIndex j))).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,
    KFCausalCorrelatedClusteredAllFactorLimit.momentumOutput_graph f ε h a p hε hh hb₀ ha (matterIndex j),
    reverse_graph f ε h a p hε hh ha hb j⟩

include hb in
theorem second_domains (j : Fin 2) : ψ ∈
    (composition (reverseFactor ε hε h modelDirections pointField (matterIndex j))
      (energyFactor ε hε h modelDirections pointField (matterIndex j))).domain :=
  LinearPMap.mem_domain_of_mem_graph (second_graph f ε h a p hε hh ha hb j)

theorem original_second_tendsto (j : Fin 2) :
    Tendsto (fun δ => KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteMomentumSeconds
      f ε h a p hε hh ha hb δ (matterIndex j)) (𝓝[>] 0) (𝓝 (second f ε h a p hε hh ha hb j)) := by
  apply Tendsto.congr' _ ((inverseL ε hε).continuous.tendsto _ |>.comp (spectral_tendsto f ε h a p hε hh ha hb j))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finiteMomentumSeconds_eq f ε h a p hε hh ha hb δ hδ j).symm

#print axioms finite_field_graph
#print axioms finite_exponential_graph
#print axioms intermediate_tendsto
#print axioms intermediate_graph
#print axioms spectral_exists_limit
#print axioms spectral_tendsto
#print axioms spectral_graph
#print axioms reverse_graph
#print axioms second_graph
#print axioms second_domains
#print axioms original_second_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumMatterSecondLimit

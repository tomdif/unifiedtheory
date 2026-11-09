/- Unitary transfer of the proved product totality to the actual physical
Hilbert space. The explicit repaired coupled trials have dense complex span. -/
import UnifiedTheory.Audit.KFCausalDampedProductTotality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoupledTrialDensity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalCoupledUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalNoncompactFourierCoordinates
open UnifiedTheory.Audit.KFCausalCoupledProductDomain
open UnifiedTheory.Audit.KFCausalDampedProductDomain
open UnifiedTheory.Audit.KFCausalDampedProductTotality
open UnifiedTheory.Audit.KFCausalDampedGaussianTotality

def lift (ε : ℝ) (hε : 0 < ε) : FrequencyHilbert ≃ₗᵢ[ℂ] Hilbert :=
  euclideanPullback.symm.trans (coordinates ε hε)

theorem lift_trial (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (v : ℝ × SchwartzMap TailSpace ℂ) :
    lift ε hε (euclideanTrial ε a hε.le ha v) = trialState ε a v.1 hε ha v.2 (v.2.memLp 2 volume) := by
  change coordinates ε hε (euclideanPullback.symm (euclideanTrial ε a hε.le ha v)) =
    coordinates ε hε ((configuration_memLp _ _ (modulated_memLp ε a v.1 hε.le ha)
      (v.2.memLp 2 volume)).toLp _)
  congr 1

def trialFamily (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (v : ℝ × SchwartzMap TailSpace ℂ) : Hilbert :=
  trialState ε a v.1 hε ha v.2 (v.2.memLp 2 volume)

theorem dense_trial_span (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    (Submodule.span ℂ (Set.range (trialFamily ε a hε ha))).topologicalClosure = ⊤ := by
  let L : FrequencyHilbert →L[ℂ] Hilbert := lift ε hε
  have hd : DenseRange L := (lift ε hε).surjective.denseRange
  have he := hd.topologicalClosure_map_submodule (dense_euclidean_trial_span ε a hε.le ha)
  have ht : (L : FrequencyHilbert → Hilbert) ∘ euclideanTrial ε a hε.le ha = trialFamily ε a hε ha :=
    funext (lift_trial ε a hε ha)
  rw [Submodule.map_span,← Set.range_comp] at he
  change (Submodule.span ℂ (Set.range ((L : FrequencyHilbert → Hilbert) ∘ euclideanTrial ε a hε.le ha))).topologicalClosure=⊤ at he
  rw [ht] at he
  exact he

#print axioms lift_trial
#print axioms dense_trial_span

end
end UnifiedTheory.Audit.KFCausalCoupledTrialDensity

/- Strict negativity of an output rate survives unitary orbit averaging
when every form vector with nonzero physical embedding has negative rate. -/
import UnifiedTheory.Audit.KFCausalStrictMultiplierPairing
import UnifiedTheory.Audit.KFCausalAveragedFormProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalAveragedStrictRate
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage (StrongUnitaryGroup)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalAveragedFormSpace
open UnifiedTheory.Audit.KFCausalAveragedFormProjection
open UnifiedTheory.Audit.KFCausalStrictMultiplierPairing

variable {H E K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (U : StrongUnitaryGroup H) (T : ℝ) (J : E →L[ℂ] H) (A : E →L[ℂ] K)
  (R : K →L[ℂ] K) (c : ℝ)

theorem averaged_rate_negative
    (hn : ∀ v : E, J v ≠ 0 → c*(inner ℂ (A v) (R (A v))).im < 0)
    (u : FormSpace U T J) (hu : embedding U T J u ≠ 0) :
    c*(inner ℂ (averagedOutput U T J A u) (R.compLp (averagedOutput U T J A u))).im < 0 := by
  rw [imaginary_pairing_integral]
  apply negative_integral_of_ae_negative angleMeasure _
    ((L2.integrable_inner (𝕜 := ℂ) (averagedOutput U T J A u)
      (R.compLp (averagedOutput U T J A u))).im.const_mul c)
  filter_upwards [compatibility_ae U T J u,A.coeFn_compLp (sectionMap U T J u),
    R.coeFn_compLp (averagedOutput U T J A u)] with θ hj ha hr
  change c*(inner ℂ ((averagedOutput U T J A u) θ)
    ((R.compLp (averagedOutput U T J A u)) θ)).im < 0
  change (averagedOutput U T J A u) θ = A (sectionMap U T J u θ) at ha
  rw [hr,ha]
  apply hn
  intro hz
  apply hu
  apply (U.action (T*θ)).injective
  exact (hj.symm.trans hz).trans (map_zero (U.action (T*θ))).symm

#print axioms averaged_rate_negative

end
end UnifiedTheory.Audit.KFCausalAveragedStrictRate

/- For a charge-invariant physical vector, every bounded pairing of the
averaged energy output equals the corresponding unaveraged pairing. -/
import UnifiedTheory.Audit.KFCausalAveragedFixedEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalAveragedFixedPairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage (StrongUnitaryGroup)
open UnifiedTheory.Audit.KFCausalPeriodicUnitaryMean (fixedSpace)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalAveragedFormSpace
open UnifiedTheory.Audit.KFCausalAveragedFormProjection

variable {H E K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (U : StrongUnitaryGroup H) (T : ℝ) (J : E →L[ℂ] H) (A : E →L[ℂ] K)
  (hJ : Function.Injective J)

include hJ

theorem fixed_output_coe (u : FormSpace U T J) (v : E)
    (he : embedding U T J u = J v) (hf : J v ∈ fixedSpace U) :
    averagedOutput U T J A u =ᵐ[angleMeasure] fun _ => A v := by
  filter_upwards [compatibility_ae U T J u,A.coeFn_compLp (sectionMap U T J u)] with θ hθ hA
  have hs : sectionMap U T J u θ = v :=
    hJ (hθ.trans ((congrArg (U.action (T*θ)) he).trans (hf (T*θ))))
  change A.compLp (sectionMap U T J u) θ = _
  rw [hA,hs]

theorem fixed_pairing (u : FormSpace U T J) (v : E)
    (he : embedding U T J u = J v) (hf : J v ∈ fixedSpace U) (B : K →L[ℂ] K) :
    inner ℂ (averagedOutput U T J A u) (B.compLp (averagedOutput U T J A u)) =
      inner ℂ (A v) (B (A v)) := by
  rw [L2.inner_def]
  calc
    _ = ∫ _θ : ℝ, inner ℂ (A v) (B (A v)) ∂angleMeasure := by
      apply integral_congr_ae
      filter_upwards [fixed_output_coe U T J A hJ u v he hf,
        B.coeFn_compLp (averagedOutput U T J A u)] with θ hA hB
      rw [hB,hA]
    _ = _ := by simp

#print axioms fixed_output_coe
#print axioms fixed_pairing

end
end UnifiedTheory.Audit.KFCausalAveragedFixedPairing

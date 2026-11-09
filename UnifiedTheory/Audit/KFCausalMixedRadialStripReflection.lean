/- Reflection of the actual complex clock inverse and radial strip
family. Both the imaginary clock shift and neutral frequency reverse
under conjugation; the clock branch is fixed by its proved inverse law. -/
import UnifiedTheory.Audit.KFCausalMixedRadialStripFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalMixedRadialStripReflection
noncomputable section
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorMixedRadialStrip (factor multiplier grouped)
open UnifiedTheory.Audit.KFCausalClockFloorMixedHeatStrip (heatFactor)
open UnifiedTheory.Audit.KFCausalNeutralPositionStripPhase (localized phase)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (complexScale mix)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (neutral)
open UnifiedTheory.Audit.KFCausalMixedRadialStripFamily (family mixedTail)
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit (TailSpace)

theorem inverse_conj (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    complexInverse ε (starRingEnd ℂ q) = starRingEnd ℂ (complexInverse ε q) := by
  let z := complexInverse ε q
  have hz : starRingEnd ℂ z ∈ closedStrip := by
    change |(starRingEnd ℂ z : ℂ).im| ≤ Real.pi/2
    simpa only [Complex.conj_im,abs_neg] using (complexInverse_mem ε hε q hq).le
  have he : complexChart ε (starRingEnd ℂ z) = starRingEnd ℂ q := by
    calc
      _ = starRingEnd ℂ (complexChart ε z) := by simp [complexChart,Complex.exp_conj]
      _ = _ := congrArg (starRingEnd ℂ) (complexInverse_right ε hε q hq)
  exact (congrArg (complexInverse ε) he.symm).trans (complexInverse_left ε hε _ hz)

theorem factor_conj (δ v p s r : ℝ) (z : ℂ) :
    starRingEnd ℂ (factor δ (-v) p s r (starRingEnd ℂ z)) = factor δ v p s r z := by
  simp only [factor,heatFactor,localized,phase,neutral,complexScale,
    map_mul,map_add,map_sub,map_neg,map_pow,map_div₀,← Complex.exp_conj,
    Complex.conj_ofReal,Complex.conj_I,map_ofNat,map_one,starRingEnd_self_apply,
    Complex.ofReal_neg,neg_mul,mul_neg,neg_neg]

theorem family_conj (ε h δ v : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : q ∈ targetStrip ε) (z : TailSpace) :
    starRingEnd ℂ (family ε h δ (-v) (starRingEnd ℂ q) z) = family ε h δ v q z := by
  unfold family multiplier
  rw [inverse_conj ε hε q hq,factor_conj]

#print axioms inverse_conj
#print axioms factor_conj
#print axioms family_conj

end
end UnifiedTheory.Audit.KFCausalMixedRadialStripReflection

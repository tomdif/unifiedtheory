/- A symmetric action bound survives integration. Equal opposite
partitions turn the second-difference estimate into a one-sided bound. -/
import UnifiedTheory.Clay.YangMills.CompactDensityEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CompactExponentialMidpoint
noncomputable section
open MeasureTheory CompactDensityEntropy

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem equal_midpoint (A B C : X → ℝ) (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (D : ℝ) (hD : ∀ x, B x + C x - 2 * A x ≤ D)
    (he : (∫ x, Real.exp (-B x) ∂μ) = ∫ x, Real.exp (-C x) ∂μ) :
    Real.exp (-D/2) * (∫ x, Real.exp (-A x) ∂μ) ≤ ∫ x, Real.exp (-B x) ∂μ := by
  let b : X → ℝ := fun x => Real.exp (-B x/2)
  let c : X → ℝ := fun x => Real.exp (-C x/2)
  have hb : Continuous b := (hB.neg.div_const 2).rexp
  have hc : Continuous c := (hC.neg.div_const 2).rexp
  have hp (x : X) : Real.exp (-D/2) * Real.exp (-A x) ≤ b x*c x := by
    dsimp only [b, c]
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hD x]
  have hi := integral_mono ((continuous_integrable μ _ hA.neg.rexp).const_mul (Real.exp (-D/2)))
    (continuous_integrable μ _ (hb.mul hc)) hp
  rw [integral_const_mul] at hi
  have hs := integral_product_sq μ b c hb hc
  have hb2 (x : X) : (b x)^2 = Real.exp (-B x) := by
    dsimp only [b]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hc2 (x : X) : (c x)^2 = Real.exp (-C x) := by
    dsimp only [c]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hb2, hc2, ← he] at hs
  have hpos : 0 ≤ ∫ x, Real.exp (-B x) ∂μ := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hm : (∫ x, b x*c x ∂μ) ≤ ∫ x, Real.exp (-B x) ∂μ := by nlinarith only [hs, hpos]
  exact hi.trans hm

end
end UnifiedTheory.Clay.YangMills.CompactExponentialMidpoint

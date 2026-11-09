/- Weighted Schwartz tails for bounded kernels supported outside a growing ball.
The constants are actual finite weighted integrals, bounded by Schwartz seminorms.
No continuum correlation estimate is supplied as a premise. -/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SchwartzWeightedTail
noncomputable section
open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure E) [μ.HasTemperateGrowth]

/-- A finite, test-dependent weighted absolute integral. -/
def weightedMoment (m : ℕ) (f : SchwartzMap E ℂ) : ℝ :=
  ∫ x, ‖x‖ ^ m * ‖f x‖ ∂μ

theorem weighted_integrable (m : ℕ) (f : SchwartzMap E ℂ) :
    Integrable (fun x => ‖x‖ ^ m * ‖f x‖) μ := f.integrable_pow_mul μ m

omit [BorelSpace E] [SecondCountableTopology E] [μ.HasTemperateGrowth] in
theorem weightedMoment_nonneg (m : ℕ) (f : SchwartzMap E ℂ) :
    0 ≤ weightedMoment μ m f := integral_nonneg (fun _ => by positivity)

omit [BorelSpace E] [SecondCountableTopology E] in
/-- The tail constant itself has a fixed finite Schwartz seminorm bound. -/
theorem weightedMoment_le_seminorms (m : ℕ) (f : SchwartzMap E ℂ) :
    weightedMoment μ m f ≤ 2 ^ μ.integrablePower *
      (∫ x, (1 + ‖x‖) ^ (-(μ.integrablePower : ℝ)) ∂μ) *
        (SchwartzMap.seminorm ℝ 0 0 f +
          SchwartzMap.seminorm ℝ (m + μ.integrablePower) 0 f) := by
  simpa only [weightedMoment, norm_iteratedFDeriv_zero] using
    SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ μ f m 0

/-- A bounded measurable kernel times any Schwartz test is genuinely integrable. -/
theorem bounded_mul_integrable (w : E → ℂ) (hw : AEStronglyMeasurable w μ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖w x‖ ≤ C) (f : SchwartzMap E ℂ) :
    Integrable (fun x => w x * f x) μ := by
  apply (f.integrable.norm.const_mul C).mono (hw.mul f.continuous.aestronglyMeasurable)
  filter_upwards with x
  change ‖w x * f x‖ ≤ ‖C * ‖f x‖‖
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (norm_nonneg _)), norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)

/-- Polynomial decay bounds every bounded kernel that vanishes on a radius-R ball. -/
theorem tail_pairing_bound (w : E → ℂ) (C R : ℝ) (m : ℕ)
    (hC : 0 ≤ C) (hR : 0 < R) (hbound : ∀ x, ‖w x‖ ≤ C)
    (hzero : ∀ x, ‖x‖ ≤ R → w x = 0) (f : SchwartzMap E ℂ) :
    ‖∫ x, w x * f x ∂μ‖ ≤ (C / R ^ m) * weightedMoment μ m f := by
  have hp (x : E) : ‖w x * f x‖ ≤ (C / R ^ m) * (‖x‖ ^ m * ‖f x‖) := by
    by_cases hx : ‖x‖ ≤ R
    · rw [hzero x hx, zero_mul, norm_zero]
      positivity
    · have hrx : R ≤ ‖x‖ := (lt_of_not_ge hx).le
      have hm : R ^ m ≤ ‖x‖ ^ m := pow_le_pow_left₀ hR.le hrx m
      calc
        ‖w x * f x‖ ≤ C * ‖f x‖ := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)
        _ ≤ (C / R ^ m) * (‖x‖ ^ m * ‖f x‖) := by
          have h := mul_le_mul_of_nonneg_left hm (mul_nonneg hC (norm_nonneg (f x)))
          calc
            _ ≤ (C * ‖f x‖ * ‖x‖ ^ m) / R ^ m :=
              (le_div_iff₀ (pow_pos hR m)).mpr h
            _ = _ := by ring
  have h := norm_integral_le_of_norm_le
    ((weighted_integrable μ m f).const_mul (C / R ^ m)) (Eventually.of_forall hp)
  simpa only [integral_const_mul, weightedMoment] using h

end
end UnifiedTheory.Clay.YangMills.SchwartzWeightedTail

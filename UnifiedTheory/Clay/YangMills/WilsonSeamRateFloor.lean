/- The improved averaged certificate still retains an exponential linear-period
cost. This bounds the certified margin from above, not the actual spectral gap.
Further averaging of this particular capped profile cannot remove that cost. -/
import UnifiedTheory.Clay.YangMills.WilsonAveragedSeamContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSeamRateFloor
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonSeamRateProfile
open WilsonTemporalInfluence WilsonPhysicalVariance CompactDensityEntropy

theorem likelihood_coefficient_le (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (a-1)^2/a ≤ (b-1)^2/b := by
  rcases hab.eq_or_lt with h | h
  · rw [h]
  · exact (likelihood_coefficient_lt a b ha h).le

variable (n : ℕ)

def baseScale (β : ℝ) : ℝ := Real.exp (β * Real.pi^2 * n)

theorem baseScale_pos (β : ℝ) : 0 < baseScale n β := Real.exp_pos _

theorem baseScale_ge_one (β : ℝ) (hβ : 0 ≤ β) : 1 ≤ baseScale n β :=
  Real.one_le_exp_iff.mpr (by positivity)

def baseCoefficient (β : ℝ) : ℝ := (baseScale n β - 1)^2 / baseScale n β

theorem baseCoefficient_nonneg (β : ℝ) : 0 ≤ baseCoefficient n β :=
  div_nonneg (sq_nonneg _) (baseScale_pos n β).le

def baseRate (β : ℝ) : ℝ := (baseScale n β - 1)^2 / (baseScale n β + 1)^2

theorem baseRate_fraction (β : ℝ) :
    baseRate n β = baseCoefficient n β / (4 + baseCoefficient n β) := by
  have hp := baseScale_pos n β
  have hc : 0 < 4 + baseCoefficient n β := by
    have hh := baseCoefficient_nonneg n β
    linarith
  apply (eq_div_iff hc.ne').mpr
  unfold baseRate baseCoefficient
  field_simp [hp.ne', (by linarith : baseScale n β + 1 ≠ 0)]
  ring

theorem baseRate_margin (β : ℝ) :
    1 - baseRate n β = 4 * baseScale n β / (baseScale n β + 1)^2 := by
  have hp := baseScale_pos n β
  unfold baseRate
  field_simp [(by linarith : baseScale n β + 1 ≠ 0)]
  ring

theorem baseRate_margin_upper (β : ℝ) : 1 - baseRate n β ≤ 4 / baseScale n β := by
  rw [baseRate_margin]
  have hp := baseScale_pos n β
  apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < baseScale n β + 1)) hp).mpr
  nlinarith

variable [NeZero n]

/-- Noncommutation can only increase the new likelihood coefficient. -/
theorem baseCoefficient_le_new (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    baseCoefficient n β ≤ WilsonPhysicalSeamResponse.coefficient n i β u := by
  apply likelihood_coefficient_le _ _ (baseScale_ge_one n β hβ)
  apply Real.exp_le_exp.mpr
  have hh := mul_nonneg hβ (WilsonSeamGaugePenalty.penalty_nonneg n i u)
  nlinarith only [hh]

omit [NeZero n] in
theorem baseCoefficient_le_raw (hn : 4 ≤ n) (β : ℝ) (hβ : 0 ≤ β) :
    baseCoefficient n β ≤ WilsonCenterLikelihood.coefficient n β := by
  apply likelihood_coefficient_le _ _ (baseScale_ge_one n β hβ)
  apply Real.exp_le_exp.mpr
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi : Real.pi^2 ≤ 4 * (n : ℝ) := by
    nlinarith only [Real.pi_lt_four, Real.pi_pos, hn4]
  have hh := mul_le_mul_of_nonneg_right hpi (mul_nonneg hβ (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  nlinarith only [hh]

theorem baseCoefficient_le_weight (hn : 4 ≤ n) (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β)
    (u : Slice n) : baseCoefficient n β ≤ WilsonPhysicalSeamResponse.weight n i β u :=
  le_min (baseCoefficient_le_raw n hn β hβ) (baseCoefficient_le_new n i β hβ u)

theorem profile_lower (hn : 4 ≤ n) (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    baseRate n β ≤ profile n i β u := by
  rw [baseRate_fraction]
  exact fraction_le _ _ (baseCoefficient_nonneg n β)
    (WilsonPhysicalSeamResponse.weight_nonneg n i β u)
    (baseCoefficient_le_weight n hn i β hβ u)

/-- The original Markov averaging preserves the constant lower floor of the profile. -/
theorem averaged_lower (hn : 4 ≤ n) (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    baseRate n β ≤ WilsonAveragedSeamContraction.averaged n i β hβ u := by
  letI := rowLaw_probability n β hβ u
  have hh := integral_mono (integrable_const (baseRate n β))
    (continuous_integrable (rowLaw n β hβ u) _ (profile n i β).continuous)
    (profile_lower n hn i β hβ)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh

theorem rate_lower (hn : 4 ≤ n) (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) :
    baseRate n β ≤ WilsonAveragedSeamContraction.rate n i β hβ :=
  averaged_lower n hn i β hβ _

/-- This is an upper bound on this certificate's margin, not on the actual physical gap. -/
theorem certified_margin_upper (hn : 4 ≤ n) (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) :
    1 - WilsonAveragedSeamContraction.rate n i β hβ ≤
      4 * Real.exp (-(β * Real.pi^2 * n)) := by
  have hh : 1 - WilsonAveragedSeamContraction.rate n i β hβ ≤ 1 - baseRate n β := by
    linarith only [rate_lower n hn i β hβ]
  have hu := hh.trans (baseRate_margin_upper n β)
  simpa only [baseScale, Real.exp_neg, div_eq_mul_inv] using hu

end
end UnifiedTheory.Clay.YangMills.WilsonSeamRateFloor

/- Source-weighted seam response for the original physical transfer.
The new coefficient is clipped by the earlier global bound. Its integral
retains the actual conditional variance of the source; a small unweighted
mean penalty is not substituted for the needed weighted estimate. -/
import UnifiedTheory.Clay.YangMills.WilsonSeamGaugePenalty
import UnifiedTheory.Clay.YangMills.WilsonCenterContraction
import UnifiedTheory.Clay.YangMills.WilsonPhysicalScore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonPhysicalSeamResponse
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonCenterTwist
open WilsonGroundLocalComparison WilsonTemporalInfluence WilsonPhysicalScore
open WilsonPhysicalVariance WilsonGroundHeatBath CompactDensityEntropy
open WilsonSeamGaugePenalty

variable (n : ℕ) [NeZero n]

def ratio (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) : ℝ :=
  transition n β hβ (twist n i u) v / transition n β hβ u v

theorem ratio_continuous (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    Continuous (ratio n i β hβ u) :=
  (transition_continuous n β hβ _).div (transition_continuous n β hβ u)
    (fun v => (transition_pos n β hβ u v).ne')

theorem ratio_mean (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    (∫ v, ratio n i β hβ u v ∂rowLaw n β hβ u) = 1 := by
  letI := rowLaw_probability n β hβ u
  have he (v : Slice n) : ratio n i β hβ u v = score n β hβ u (twist n i u) v + 1 := by
    unfold ratio score
    ring
  simp_rw [he]
  rw [integral_add (continuous_integrable (rowLaw n β hβ u) _
    (score_continuous n β hβ u _)) (integrable_const 1), score_mean_zero]
  simp

theorem ratio_pairing (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v) :
    (∫ v, ratio n i β hβ u v * f v ∂rowLaw n β hβ u) = step n β hβ f (twist n i u) := by
  letI := rowLaw_probability n β hβ u
  have he (v : Slice n) : ratio n i β hβ u v * f v =
      score n β hβ u (twist n i u) v * f v + f v := by
    unfold ratio score
    ring
  simp_rw [he]
  rw [integral_add (continuous_integrable (rowLaw n β hβ u)
    (fun v => score n β hβ u (twist n i u) v * f v)
    ((score_continuous n β hβ u (twist n i u)).mul f.continuous))
    (continuous_integrable (rowLaw n β hβ u) _ f.continuous),
    score_pairing n β hβ u (twist n i u) f hinv]
  change step n β hβ f (twist n i u) - step n β hβ f u + step n β hβ f u = _
  ring

def scale (i : Fin 3) (β : ℝ) (u : Slice n) : ℝ :=
  Real.exp (β * (Real.pi^2 * n + penalty n i u))

theorem scale_pos (i : Fin 3) (β : ℝ) (u : Slice n) : 0 < scale n i β u := Real.exp_pos _

theorem scale_continuous (i : Fin 3) (β : ℝ) : Continuous (scale n i β) :=
  (continuous_const.mul (continuous_const.add (penalty_continuous n i))).rexp

def coefficient (i : Fin 3) (β : ℝ) (u : Slice n) : ℝ :=
  (scale n i β u - 1)^2 / scale n i β u

theorem coefficient_nonneg (i : Fin 3) (β : ℝ) (u : Slice n) : 0 ≤ coefficient n i β u :=
  div_nonneg (sq_nonneg _) (scale_pos n i β u).le

theorem coefficient_continuous (i : Fin 3) (β : ℝ) : Continuous (coefficient n i β) :=
  (((scale_continuous n i β).sub continuous_const).pow 2).div
    (scale_continuous n i β) (fun u => (scale_pos n i β u).ne')

theorem ratio_bounds (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    ratio n i β hβ u v ∈ Set.Icc (scale n i β u)⁻¹ (scale n i β u) := by
  simpa only [Real.exp_neg, scale, ratio] using
    WilsonSeamGaugePenalty.physical_likelihood_bounds n i β hβ u v

theorem ratio_variance (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    ProbabilityTheory.variance (ratio n i β hβ u) (rowLaw n β hβ u) ≤ coefficient n i β u := by
  letI := rowLaw_probability n β hβ u
  have hh := ProbabilityTheory.variance_le_sub_mul_sub (μ := rowLaw n β hβ u)
    (Filter.Eventually.of_forall (ratio_bounds n i β hβ u))
    (ratio_continuous n i β hβ u).measurable.aemeasurable
  rw [ratio_mean] at hh
  apply hh.trans_eq
  unfold coefficient
  field_simp [(scale_pos n i β u).ne']

theorem response_conditional (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v) :
    (step n β hβ f (twist n i u) - step n β hβ f u)^2 ≤
      coefficient n i β u * rowVariance n β hβ f u := by
  letI := rowLaw_probability n β hβ u
  have hh := CompactNormalizedLikelihood.response_sq_le_likelihood_variance
    (rowLaw n β hβ u) (ratio n i β hβ u) f
    (ratio_continuous n i β hβ u) f.continuous (ratio_mean n i β hβ u)
  rw [ratio_pairing n i β hβ u f hinv] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (ratio_variance n i β hβ u)
    (rowVariance_nonneg n β hβ f u))

/-- Clipping keeps the bound at least as strong as the earlier global seam estimate. -/
def weight (i : Fin 3) (β : ℝ) (u : Slice n) : ℝ :=
  min (WilsonCenterLikelihood.coefficient n β) (coefficient n i β u)

theorem weight_nonneg (i : Fin 3) (β : ℝ) (u : Slice n) : 0 ≤ weight n i β u :=
  le_min (WilsonCenterLikelihood.coefficient_nonneg n β) (coefficient_nonneg n i β u)

theorem weight_continuous (i : Fin 3) (β : ℝ) : Continuous (weight n i β) :=
  continuous_const.min (coefficient_continuous n i β)

theorem weight_gauge (i : Fin 3) (β : ℝ) (u : Slice n) (h : SliceGauge n Q) :
    weight n i β (gaugeSlice h u) = weight n i β u := by
  simp only [weight, coefficient, scale, penalty_gauge]

theorem weight_twist (i : Fin 3) (β : ℝ) (u : Slice n) :
    weight n i β (twist n i u) = weight n i β u := by
  simp only [weight, coefficient, scale, penalty_twist]

theorem clipped_response (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v) :
    (step n β hβ f (twist n i u) - step n β hβ f u)^2 ≤
      weight n i β u * rowVariance n β hβ f u := by
  unfold weight
  rw [min_mul_of_nonneg _ _ (rowVariance_nonneg n β hβ f u)]
  exact le_min (WilsonCenterLikelihood.response_conditional n i β hβ u f)
    (response_conditional n i β hβ u f hinv)

def weightedLoss (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : ℝ :=
  ∫ u, weight n i β u * rowVariance n β hβ f u ∂groundLaw n β hβ

theorem weightedLoss_nonneg (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    0 ≤ weightedLoss n i β hβ f :=
  integral_nonneg (fun u => mul_nonneg (weight_nonneg n i β u) (rowVariance_nonneg n β hβ f u))

theorem response_le_weightedLoss (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v) :
    WilsonCenterCoercivity.energy n i β hβ (step n β hβ f) ≤ weightedLoss n i β hβ f := by
  letI := groundLaw_probability n β hβ
  have hf := (step n β hβ f).continuous
  exact integral_mono
    (continuous_integrable (groundLaw n β hβ) _
      (((hf.comp (twist_continuous n i)).sub hf).pow 2))
    (continuous_integrable (groundLaw n β hβ) _
      ((weight_continuous n i β).mul (rowVariance_continuous n β hβ f)))
    (fun u => clipped_response n i β hβ u f hinv)

theorem weightedLoss_le_global (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    weightedLoss n i β hβ f ≤ WilsonCenterLikelihood.coefficient n β * loss n β hβ f := by
  letI := groundLaw_probability n β hβ
  have hh := integral_mono
    (continuous_integrable (groundLaw n β hβ) _
      ((weight_continuous n i β).mul (rowVariance_continuous n β hβ f)))
    ((continuous_integrable (groundLaw n β hβ) _
      (rowVariance_continuous n β hβ f)).const_mul (WilsonCenterLikelihood.coefficient n β))
    (fun u => mul_le_mul_of_nonneg_right (min_le_left _ _) (rowVariance_nonneg n β hβ f u))
  rw [integral_const_mul, mean_rowVariance_eq_loss] at hh
  exact hh

/-- The exact odd-sector lower bound applies to the same physical response energy. -/
theorem odd_output_bound (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v)
    (hf : ∀ u, f (twist n i u) = -f u) :
    4 * variance n β hβ (step n β hβ f) ≤ weightedLoss n i β hβ f := by
  have hu := response_le_weightedLoss n i β hβ f hinv
  have hl := WilsonCenterCoercivity.odd_coercivity n i β hβ (step n β hβ f)
    (WilsonCenterContraction.step_odd n i β hβ f hf)
  linarith only [hu, hl]

/-- A source-weighted estimate is sufficient; an unweighted mean coefficient is not substituted. -/
theorem odd_contraction_of_weighted_bound (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v)
    (hf : ∀ u, f (twist n i u) = -f u) (C : ℝ) (hC : 0 ≤ C)
    (hw : weightedLoss n i β hβ f ≤ C * loss n β hβ f) :
    variance n β hβ (step n β hβ f) ≤ C / (4 + C) * variance n β hβ f := by
  have hh := (odd_output_bound n i β hβ f hinv hf).trans hw
  unfold loss at hh
  have hp : 0 < 4 + C := by linarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hp).mpr
  nlinarith only [hh]

end
end UnifiedTheory.Clay.YangMills.WilsonPhysicalSeamResponse

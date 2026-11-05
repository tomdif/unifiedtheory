/- The center seam has exactly equal row normalizers. This yields a
fixed likelihood interval, an actual variance-loss response bound, and
explicit extremizers for the pointwise cap. The cost still grows with area. -/
import UnifiedTheory.Clay.YangMills.WilsonCenterSeamGeometry
import UnifiedTheory.Clay.YangMills.CompactNormalizedLikelihood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCenterLikelihood
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonCenterTwist
open WilsonCenterSeamGeometry WilsonTemporalInfluence WilsonVarianceResponse
open WilsonPhysicalVariance WilsonGroundHeatBath CompactDensityEntropy

variable (n : ℕ)

def scale (β : ℝ) : ℝ := Real.exp (4 * β * (n : ℝ)^2)

theorem scale_pos (β : ℝ) : 0 < scale n β := Real.exp_pos _

theorem scale_ge_one (β : ℝ) (hβ : 0 ≤ β) : 1 ≤ scale n β :=
  Real.one_le_exp_iff.mpr (by positivity)

def coefficient (β : ℝ) : ℝ := (scale n β - 1)^2 / scale n β

theorem coefficient_nonneg (β : ℝ) : 0 ≤ coefficient n β :=
  div_nonneg (sq_nonneg _) (scale_pos n β).le

variable [NeZero n]

/-- The partition ratio is exactly one, not separately bounded by an exponential. -/
theorem partition_twist (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    rowPartition n β hβ (twist n i u) = rowPartition n β hβ u := by
  have hh := rowPartition_ground n β hβ (twist n i u)
  have hs : spatialWeight WilsonSingleLinkStaples.character β 2 (twist n i u) =
      spatialWeight WilsonSingleLinkStaples.character β 2 u := by
    simp only [spatialWeight, potential_twist]
  rw [hs, ground_twist] at hh
  exact mul_left_cancel₀ (Real.exp_pos _).ne' (hh.trans (rowPartition_ground n β hβ u).symm)

theorem likelihood_tilt (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    likelihood n β hβ u (twist n i u) v =
      tilt n β (links n i) (twist n i u) u v := by
  unfold likelihood
  simp only [rawTransition_quotient, partition_twist]
  rw [rowWeight_tilt n β hβ (links n i) (twist n i u) u v
    (twist_away n i u)]
  field_simp [(rowPartition_pos n β hβ u).ne', (rowWeight_pos n β hβ u v).ne']

/-- Both ends of the interval are fixed by the same exact symmetry. -/
theorem likelihood_bounds (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    likelihood n β hβ u (twist n i u) v ∈ Set.Icc (scale n β)⁻¹ (scale n β) := by
  rw [likelihood_tilt]
  have hh := tilt_bounds n β hβ (links n i) (twist n i u) u v
  simpa only [links_card, Nat.cast_pow, Real.exp_neg, scale] using hh

theorem likelihood_variance (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    ProbabilityTheory.variance (likelihood n β hβ u (twist n i u)) (rowLaw n β hβ u) ≤
      coefficient n β := by
  letI := rowLaw_probability n β hβ u
  have hh := ProbabilityTheory.variance_le_sub_mul_sub (μ := rowLaw n β hβ u)
    (Filter.Eventually.of_forall (likelihood_bounds n i β hβ u))
    (likelihood_continuous n β hβ u (twist n i u)).measurable.aemeasurable
  rw [likelihood_mean] at hh
  apply hh.trans_eq
  unfold coefficient
  field_simp [(scale_pos n β).ne']

theorem response_conditional (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β)
    (u : Slice n) (f : C(Slice n, ℝ)) :
    (step n β hβ f (twist n i u) - step n β hβ f u)^2 ≤
      coefficient n β * rowVariance n β hβ f u := by
  letI := rowLaw_probability n β hβ u
  have hh := CompactNormalizedLikelihood.response_sq_le_likelihood_variance
    (rowLaw n β hβ u) (likelihood n β hβ u (twist n i u)) f
    (likelihood_continuous n β hβ u _) f.continuous (likelihood_mean n β hβ u _)
  rw [likelihood_reweight] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (likelihood_variance n i β hβ u)
    (rowVariance_nonneg n β hβ f u))

/-- This is the same whole-seam response as in the proved odd-sector lower bound. -/
theorem response_le_loss (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    WilsonCenterCoercivity.energy n i β hβ (step n β hβ f) ≤
      coefficient n β * loss n β hβ f := by
  letI := groundLaw_probability n β hβ
  have hf := (step n β hβ f).continuous
  have hh := integral_mono
    (continuous_integrable (groundLaw n β hβ) _
      (((hf.comp (twist_continuous n i)).sub hf).pow 2))
    ((continuous_integrable (groundLaw n β hβ) _
      (rowVariance_continuous n β hβ f)).const_mul (coefficient n β))
    (fun u => response_conditional n i β hβ u f)
  rw [integral_const_mul, mean_rowVariance_eq_loss] at hh
  exact hh

/-- The pointwise lower endpoint is achieved at the identity configurations. -/
theorem likelihood_identity (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) :
    likelihood n β hβ 1 (twist n i 1) 1 = (scale n β)⁻¹ := by
  rw [likelihood_tilt, tilt_identity, Real.exp_neg]
  rfl

/-- The upper endpoint is achieved at a genuinely distinct flat seam configuration. -/
theorem likelihood_opposite (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) :
    likelihood n β hβ 1 (twist n i 1) (twist n i 1) = scale n β := by
  rw [likelihood_tilt, tilt_opposite]
  rfl

/-- Uniform pointwise likelihood control cannot remove this exponential seam-area cost. -/
theorem pointwise_cap_floor (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (C : ℝ)
    (hC : ∀ u v, likelihood n β hβ u (twist n i u) v ≤ C) : scale n β ≤ C := by
  have hh := hC 1 (twist n i 1)
  rwa [likelihood_opposite] at hh

end
end UnifiedTheory.Clay.YangMills.WilsonCenterLikelihood

/- Variance-weighted bounds for actual bounded centered observables.
These estimates retain the true variance factor. Their range constants must
still be rescaled for a physical source; no uniform continuum bound follows. -/
import UnifiedTheory.Clay.YangMills.GibbsConditionalCumulants
import UnifiedTheory.Clay.YangMills.GibbsSuccessiveCovariance
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.VarianceWeightedNoise
noncomputable section
open MeasureTheory GibbsCrossCovariance GibbsConditionalCumulants

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- Every higher absolute moment is paid for by the actual second moment. -/
theorem absolute_moment_bound (F : X → ℝ) (hF : Continuous F) (L : ℝ)
    (hbound : ∀ x, |F x| ≤ L) (k : ℕ) :
    (∫ x, |F x| ^ (k + 2) ∂μ) ≤ L ^ k * (∫ x, (F x) ^ 2 ∂μ) := by
  have hi : Integrable (fun x => |F x| ^ (k + 2)) μ :=
    (hF.abs.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun x => (F x) ^ 2) μ :=
    (hF.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_mono hi (hi2.const_mul (L ^ k)) (fun x => by
    rw [pow_add, sq_abs]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hbound x) k)
      (sq_nonneg _))
  simpa only [integral_const_mul] using h

/-- The corresponding signed Taylor coefficient numerator has the same bound. -/
theorem moment_bound (F : X → ℝ) (hF : Continuous F) (L : ℝ)
    (hbound : ∀ x, |F x| ≤ L) (k : ℕ) :
    |∫ x, (F x) ^ (k + 2) ∂μ| ≤ L ^ k * (∫ x, (F x) ^ 2 ∂μ) := by
  calc
    _ ≤ ∫ x, |(F x) ^ (k + 2)| ∂μ := abs_integral_le_integral_abs
    _ = ∫ x, |F x| ^ (k + 2) ∂μ := by simp_rw [abs_pow]
    _ ≤ _ := absolute_moment_bound μ F hF L hbound k

/-- Conditional skewness can be small only when its variance or range is small. -/
theorem third_cumulant_bound (F : X → ℝ) (hF : Continuous F) (L : ℝ)
    (hbound : ∀ x, |F x| ≤ L) (hmean : (∫ x, F x ∂μ) = 0) :
    |cumulantThree μ F| ≤ L * (∫ x, (F x) ^ 2 ∂μ) := by
  simpa only [cumulantThree, centeredMoment, hmean, sub_zero, pow_one] using
    moment_bound μ F hF L hbound 1

/-- The square of the second moment does not exceed the fourth moment. -/
theorem second_square_le_fourth (F : X → ℝ) (hF : Continuous F) :
    (∫ x, (F x) ^ 2 ∂μ) ^ 2 ≤ ∫ x, (F x) ^ 4 ∂μ := by
  have h := GibbsSuccessiveCovariance.covariance_self_nonneg μ (fun x => (F x) ^ 2)
    (hF.pow 2)
  unfold covariance at h
  have he (x : X) : (F x) ^ 2 * (F x) ^ 2 = (F x) ^ 4 := by ring
  simp_rw [he] at h
  nlinarith

/-- For a range-L source, Popoviciu's variance bound sharpens the fourth-cumulant estimate. -/
theorem fourth_cumulant_bound (F : X → ℝ) (hF : Continuous F) (L : ℝ)
    (hbound : ∀ x, |F x| ≤ L) (hmean : (∫ x, F x ∂μ) = 0)
    (hvar : (∫ x, (F x) ^ 2 ∂μ) ≤ L ^ 2 / 4) :
    |cumulantFour μ F| ≤ L ^ 2 * (∫ x, (F x) ^ 2 ∂μ) := by
  have hv : 0 ≤ ∫ x, (F x) ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have h4 := (abs_le.mp (moment_bound μ F hF L hbound 2)).2
  have hlow := second_square_le_fourth μ F hF
  unfold cumulantFour centeredMoment
  rw [hmean]
  simp only [sub_zero]
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hvar hv]
  · nlinarith [sq_nonneg (∫ x, (F x) ^ 2 ∂μ)]

/-- Exact centering makes the real moment-generating function at least one. -/
theorem mgf_ge_one (F : X → ℝ) (hF : Continuous F)
    (hmean : (∫ x, F x ∂μ) = 0) (t : ℝ) :
    1 ≤ ∫ x, Real.exp (t * F x) ∂μ := by
  have hi : Integrable (fun x => t * F x) μ :=
    (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul t
  have he : Integrable (fun x => Real.exp (t * F x)) μ :=
    (Real.continuous_exp.comp (continuous_const.mul hF)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := integral_mono (hi.add (integrable_const 1)) he
    (fun x => Real.add_one_le_exp (t * F x))
  simp only [Pi.add_apply] at h
  rw [integral_add hi (integrable_const 1), integral_const_mul, hmean] at h
  simpa using h

/-- A local generating-function estimate with the true second moment as prefactor. -/
theorem mgf_sub_one_bound (F : X → ℝ) (hF : Continuous F) (L : ℝ)
    (hbound : ∀ x, |F x| ≤ L) (hmean : (∫ x, F x ∂μ) = 0) (t : ℝ)
    (ht : |t| * L ≤ 1) :
    |(∫ x, Real.exp (t * F x) ∂μ) - 1| ≤ t ^ 2 * (∫ x, (F x) ^ 2 ∂μ) := by
  have hi : Integrable (fun x => t * F x) μ :=
    (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul t
  have he : Integrable (fun x => Real.exp (t * F x)) μ :=
    (Real.continuous_exp.comp (continuous_const.mul hF)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun x => (F x) ^ 2) μ :=
    (hF.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hrem : Integrable (fun x => Real.exp (t * F x) - 1 - t * F x) μ :=
    (he.sub (integrable_const 1)).sub hi
  have hpoint (x : X) : |Real.exp (t * F x) - 1 - t * F x| ≤ t ^ 2 * (F x) ^ 2 := by
    have hx : |t * F x| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg t)).trans ht
    simpa only [mul_pow] using Real.abs_exp_sub_one_sub_id_le hx
  have h := integral_mono hrem.abs (hi2.const_mul (t ^ 2)) hpoint
  rw [integral_const_mul] at h
  have he1 : Integrable (fun x => Real.exp (t * F x) - 1) μ :=
    he.sub (integrable_const 1)
  have hid : (∫ x, Real.exp (t * F x) - 1 - t * F x ∂μ) =
      (∫ x, Real.exp (t * F x) ∂μ) - 1 := by
    rw [integral_sub he1 hi,
      integral_sub he (integrable_const 1), integral_const_mul, hmean]
    simp
  rw [← hid]
  exact abs_integral_le_integral_abs.trans h

/-- A genuine logarithmic source bound, without assuming any source-derivative estimate. -/
theorem log_mgf_bound (F : X → ℝ) (hF : Continuous F) (L : ℝ)
    (hbound : ∀ x, |F x| ≤ L) (hmean : (∫ x, F x ∂μ) = 0) (t : ℝ)
    (ht : |t| * L ≤ 1) :
    0 ≤ Real.log (∫ x, Real.exp (t * F x) ∂μ) ∧
      Real.log (∫ x, Real.exp (t * F x) ∂μ) ≤ t ^ 2 * (∫ x, (F x) ^ 2 ∂μ) := by
  have h1 := mgf_ge_one μ F hF hmean t
  have h2 := (abs_le.mp (mgf_sub_one_bound μ F hF L hbound hmean t ht)).2
  exact ⟨Real.log_nonneg h1,
    (Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one h1)).trans h2⟩

/-- Mixed retained/noise covariance is controlled by the actual noise variance budget. -/
theorem covariance_weighted_bound (F G V : X → ℝ)
    (hF : Continuous F) (hG : Continuous G) (hV : Continuous V)
    (D C : ℝ) (hD : 0 ≤ D)
    (hFc : ∀ x, |F x - ∫ y, F y ∂μ| ≤ D)
    (hGc : ∀ x, |G x| ≤ C * V x) :
    |covariance μ F G| ≤ D * C * (∫ x, V x ∂μ) := by
  rw [← integral_centered_mul μ F G hF hG]
  have hi : Integrable (fun x => (F x - ∫ y, F y ∂μ) * G x) μ :=
    ((hF.sub continuous_const).mul hG).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiV : Integrable V μ :=
    hV.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp (x : X) : |(F x - ∫ y, F y ∂μ) * G x| ≤ (D * C) * V x := by
    rw [abs_mul]
    calc
      _ ≤ D * |G x| := mul_le_mul_of_nonneg_right (hFc x) (abs_nonneg _)
      _ ≤ D * (C * V x) := mul_le_mul_of_nonneg_left (hGc x) hD
      _ = _ := by ring
  have h := integral_mono hi.abs (hiV.const_mul (D * C)) hp
  rw [integral_const_mul] at h
  exact abs_integral_le_integral_abs.trans h

end
end UnifiedTheory.Clay.YangMills.VarianceWeightedNoise

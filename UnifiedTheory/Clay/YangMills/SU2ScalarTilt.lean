/- Exact one-dimensional tilted semicircle integrals and their Gamma
representation. The affine substitution and endpoint extension are proved;
no transform identity is supplied as a hypothesis. This module does not
identify the scalar semicircle density with the SU(2) Haar pushforward.
The Gamma ratio is identified only for positive κ; the actual excess mean
is zero at κ = 0 and requires that zero extension at the endpoint.
That geometric identification and the interacting continuum limit remain
separate obligations. -/
import UnifiedTheory.Clay.YangMills.SU2QuotientRemainder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SU2ScalarTilt
noncomputable section
open MeasureTheory Set

def weight (κ t : ℝ) : ℝ := Real.exp (κ * t) * Real.sqrt (1-t^2)
/-- Actual tilted semicircle integral on the original scalar interval. -/
def semicircleIntegral (κ : ℝ) (F : ℝ → ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1, weight κ t * F t
def partition (κ : ℝ) : ℝ := semicircleIntegral κ (fun _ => 1)
def excessIntegral (κ : ℝ) : ℝ := semicircleIntegral κ (fun t => κ * (1-t))
/-- The normalized expectation of `κ(1-t)` under the scalar density. -/
def excessMean (κ : ℝ) : ℝ := excessIntegral κ / partition κ
def changeFactor (κ : ℝ) : ℝ := Real.exp κ * Real.sqrt (2 / κ) / κ

@[simp] theorem excessMean_zero : excessMean 0 = 0 := by
  simp [excessMean, excessIntegral, semicircleIntegral]

theorem weight_continuous (κ : ℝ) : Continuous (weight κ) := by
  unfold weight
  fun_prop

/-- The original scalar partition is strictly positive for every real tilt. -/
theorem partition_pos (κ : ℝ) : 0 < partition κ := by
  unfold partition semicircleIntegral
  simp only [mul_one]
  apply intervalIntegral.integral_pos (by norm_num : (-1 : ℝ)<1)
    (weight_continuous κ).continuousOn
  · intro t ht
    unfold weight
    positivity
  · refine ⟨0, by norm_num, ?_⟩
    norm_num [weight]

theorem semicircleIntegral_eq_setIntegral (κ : ℝ) (F : ℝ → ℝ) :
    semicircleIntegral κ F = ∫ t in Icc (-1 : ℝ) 1, weight κ t * F t := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  rfl

theorem cutoffSqrt_zero {κ u : ℝ} (hκ : 0 < κ) (hu : 2 * κ ≤ u) :
    SqrtSourceRemainder.cutoffSqrt κ u = 0 := by
  unfold SqrtSourceRemainder.cutoffSqrt
  have h : 1 ≤ u / (2 * κ) := (le_div_iff₀ (by positivity)).2 (by simpa using hu)
  rw [max_eq_right (by linarith), Real.sqrt_zero]

/-- The cutoff vanishes outside the transformed interval, giving exact
extension to the positive half-line without a tail approximation. -/
theorem gammaIntegral_interval {κ : ℝ} (hκ : 0 < κ) (F : ℝ → ℝ) :
    SqrtSourceRemainder.gammaIntegral (3 / 2)
        (fun u => SqrtSourceRemainder.cutoffSqrt κ u * F u) =
      ∫ u in (0 : ℝ)..2 * κ, SqrtSourceRemainder.gammaWeight (3 / 2) u *
        (SqrtSourceRemainder.cutoffSqrt κ u * F u) := by
  unfold SqrtSourceRemainder.gammaIntegral
  rw [intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * κ)]
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
  intro u hu
  have hub : 2 * κ < u := by
    have hu0 : 0 < u := hu.1
    have hun : ¬ (0 < u ∧ u ≤ 2 * κ) := hu.2
    exact lt_of_not_ge (fun h => hun ⟨hu0, h⟩)
  change SqrtSourceRemainder.gammaWeight (3 / 2) u *
    (SqrtSourceRemainder.cutoffSqrt κ u * F u) = 0
  rw [cutoffSqrt_zero hκ hub.le, zero_mul, mul_zero]

/-- Affine change of variables including the positive Jacobian. -/
theorem affine_integral {κ : ℝ} (hκ : 0 < κ) (F : ℝ → ℝ) :
    (∫ t in (-1 : ℝ)..1, F t) =
      (1 / κ) * (∫ u in (0 : ℝ)..2 * κ, F (1-u / κ)) := by
  have h := intervalIntegral.integral_comp_sub_div (a := (0 : ℝ)) (b := 2 * κ)
    F hκ.ne' 1
  have hleft : 1-2 * κ / κ = (-1 : ℝ) := by field_simp; ring
  simp only [hleft, zero_div, sub_zero, smul_eq_mul] at h
  rw [h]
  field_simp

theorem sqrt_change {κ u : ℝ} (hκ : 0 < κ) (hu : u ∈ Icc 0 (2 * κ)) :
    Real.sqrt (1-(1-u / κ)^2) =
      Real.sqrt (2 / κ) * Real.sqrt u * SqrtSourceRemainder.cutoffSqrt κ u := by
  have hz : 0 ≤ 1-u / (2 * κ) := by
    have h : u / (2 * κ) ≤ 1 := (div_le_one (by positivity)).2 hu.2
    linarith
  have he : 1-(1-u / κ)^2 = (2 / κ) * u * (1-u / (2 * κ)) := by field_simp; ring
  rw [he, Real.sqrt_mul (mul_nonneg (by positivity) hu.1),
    Real.sqrt_mul (by positivity : 0 ≤ 2 / κ)]
  unfold SqrtSourceRemainder.cutoffSqrt
  rw [max_eq_left hz]

theorem weight_change {κ u : ℝ} (hκ : 0 < κ) (hu : u ∈ Icc 0 (2 * κ)) :
    weight κ (1-u / κ) = Real.exp κ * Real.sqrt (2 / κ) *
      (SqrtSourceRemainder.gammaWeight (3 / 2) u * SqrtSourceRemainder.cutoffSqrt κ u) := by
  unfold weight
  rw [sqrt_change hκ hu]
  have he : κ * (1-u / κ) = κ-u := by field_simp
  rw [he, Real.exp_sub]
  unfold SqrtSourceRemainder.gammaWeight
  rw [show (3 / 2 : ℝ)-1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, Real.exp_neg]
  ring

/-- Exact transport of any excess-coordinate insertion, with the same
constant in numerator and denominator. -/
theorem excess_transform {κ : ℝ} (hκ : 0 < κ) (F : ℝ → ℝ) :
    semicircleIntegral κ (fun t => F (κ * (1-t))) =
      changeFactor κ * SqrtSourceRemainder.gammaIntegral (3 / 2)
        (fun u => SqrtSourceRemainder.cutoffSqrt κ u * F u) := by
  unfold semicircleIntegral
  rw [affine_integral hκ, gammaIntegral_interval hκ]
  have hi : (∫ u in (0 : ℝ)..2 * κ, weight κ (1-u / κ) * F (κ * (1-(1-u / κ)))) =
      (Real.exp κ * Real.sqrt (2 / κ)) *
        (∫ u in (0 : ℝ)..2 * κ, SqrtSourceRemainder.gammaWeight (3 / 2) u *
          (SqrtSourceRemainder.cutoffSqrt κ u * F u)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc 0 (2 * κ) := by
      simpa only [uIcc_of_le (by positivity : 0 ≤ 2 * κ)] using hu
    dsimp only
    rw [weight_change hκ hu']
    have he : κ * (1-(1-u / κ)) = u := by field_simp; ring
    rw [he]
    ring
  rw [hi]
  unfold changeFactor
  ring

theorem partition_transform {κ : ℝ} (hκ : 0 < κ) :
    partition κ = changeFactor κ *
      SqrtSourceRemainder.gammaIntegral (3 / 2) (SqrtSourceRemainder.cutoffSqrt κ) := by
  simpa only [partition, mul_one] using excess_transform hκ (fun _ => 1)

theorem excessIntegral_transform {κ : ℝ} (hκ : 0 < κ) :
    excessIntegral κ = changeFactor κ *
      SqrtSourceRemainder.gammaIntegral (3 / 2)
        (fun u => u * SqrtSourceRemainder.cutoffSqrt κ u) := by
  simpa only [excessIntegral, mul_comm] using excess_transform hκ (fun u => u)

theorem changeFactor_pos {κ : ℝ} (hκ : 0 < κ) : 0 < changeFactor κ := by
  unfold changeFactor
  positivity

/-- The common Jacobian-density factor and Gamma normalization cancel
exactly. This is an identity of actual scalar integrals. -/
theorem excessMean_eq_sourceRatio {κ : ℝ} (hκ : 0 < κ) :
    excessMean κ = SU2QuotientRemainder.sourceRatio κ := by
  unfold excessMean SU2QuotientRemainder.sourceRatio
    SU2QuotientRemainder.numerator SU2QuotientRemainder.denominator
    SqrtSourceRemainder.gammaAverage
  rw [excessIntegral_transform hκ, partition_transform hκ,
    mul_div_mul_left _ _ (changeFactor_pos hκ).ne',
    div_div_div_cancel_right₀ (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ)<3 / 2)).ne']

/-- The proved Gamma quotient estimate now applies to the actual scalar tilt. -/
theorem excessMean_remainder {κ : ℝ} (hκ : 3 / 2 ≤ κ) (N : ℕ) (hN : 1 ≤ N) :
    |excessMean κ-SU2QuotientRemainder.sourceTruncation N κ| ≤
      6 * ((N : ℝ) + 9 / 2) * ((N + 1).factorial : ℝ) / (2 * κ)^N := by
  rw [excessMean_eq_sourceRatio (by linarith)]
  exact SU2QuotientRemainder.quotient_remainder hκ N hN

/-- Uniform optimal truncation for the actual scalar excess mean. -/
theorem excessMean_optimal_remainder (κ₀ κ : ℝ) (hκ₀ : 3 / 2 ≤ κ₀) (hκ : κ₀ ≤ κ) :
    |excessMean κ-SU2QuotientRemainder.sourceTruncation ⌊2 * κ₀⌋₊ κ| ≤
      6 * Real.exp 2 * (2 * κ₀) * (2 * κ₀ + 1) * (2 * κ₀ + 9 / 2) * Real.exp (-2 * κ₀) := by
  rw [excessMean_eq_sourceRatio (by linarith)]
  exact SU2QuotientRemainder.optimal_quotient_remainder κ₀ κ hκ₀ hκ

end
end UnifiedTheory.Clay.YangMills.SU2ScalarTilt

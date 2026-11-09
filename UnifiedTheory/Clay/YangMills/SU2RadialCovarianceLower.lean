/- An actual SU(2) tilted-Haar covariance lower bound.
Inversion symmetry retains the radial projection of every probe. The certified
first and second excess moments then give a positive inverse-square bound for
large tilt. This is a one-link estimate, not a continuum covariance claim. -/
import UnifiedTheory.Clay.YangMills.SU2WilsonLocalSecondMoment
import UnifiedTheory.Clay.YangMills.SU2WeightedRadial

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2RadialCovarianceLower
noncomputable section
open MeasureTheory RegulatedGauge SU2QuaternionEquivalence SU2HaarTilt SU2HaarCovariance
open SU2InducedAction SU2WilsonLocalEquipartition SU2WilsonLocalSecondMoment
open scoped Quaternion RealInnerProductSpace

local instance haarIsHaar : haar.IsHaarMeasure := by
  unfold haar compactHaar
  infer_instance

local instance haarInv : haar.IsInvInvariant := by
  letI : IsProbabilityMeasure haar.inv :=
    Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  constructor
  exact ((Measure.haarMeasure_eq_iff (⊤ : TopologicalSpace.PositiveCompacts UnitQuaternion)
    haar.inv).2 (by simp)).symm

/-- Inversion symmetry retains the radial part of every centered probe variance. -/
theorem axis_square_lower (κ : ℝ) (B : ℍ) (c : ℝ) :
    B.re ^ 2 * (∫ q : UnitQuaternion,
      axisWeight κ q * ((q : ℍ).re - c) ^ 2 ∂haar) ≤
      ∫ q : UnitQuaternion, axisWeight κ q * (⟪(q : ℍ), B⟫ - B.re * c) ^ 2 ∂haar := by
  let F : UnitQuaternion → ℝ :=
    fun q => axisWeight κ q * (⟪(q : ℍ), B⟫ - B.re * c) ^ 2
  have hi : Integrable F haar :=
    ((axisWeight_continuous κ).mul
      (((continuous_subtype_val.inner continuous_const).sub continuous_const).pow 2)
        ).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hineq : (∫ q : UnitQuaternion,
      (2 * B.re ^ 2) * (axisWeight κ q * ((q : ℍ).re - c) ^ 2) ∂haar) ≤
      ∫ q : UnitQuaternion, F q + F q⁻¹ ∂haar := by
    apply integral_mono
    · exact (continuous_const.mul ((axisWeight_continuous κ).mul
        (((Quaternion.continuous_re.comp continuous_subtype_val).sub
          continuous_const).pow 2))).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
    · exact hi.add hi.comp_inv
    · intro q
      have hw : axisWeight κ q⁻¹ = axisWeight κ q := by
        change Real.exp (κ * (star (q : ℍ)).re) = _
        simp only [Quaternion.re_star]
        rfl
      have hs := inner_star_sum (q : ℍ) B
      have hc : 2 * B.re ^ 2 * ((q : ℍ).re - c) ^ 2 ≤
          (⟪(q : ℍ), B⟫ - B.re * c) ^ 2 +
          (⟪star (q : ℍ), B⟫ - B.re * c) ^ 2 := by
        have hs' : ⟪star (q : ℍ), B⟫ = 2 * (q : ℍ).re * B.re - ⟪(q : ℍ), B⟫ := by
          linarith
        rw [hs']
        nlinarith [sq_nonneg (⟪(q : ℍ), B⟫ - B.re * (q : ℍ).re)]
      have hp := mul_le_mul_of_nonneg_left hc (Real.exp_pos (κ * (q : ℍ).re)).le
      dsimp only [F]
      rw [hw]
      change _ ≤ axisWeight κ q * (⟪(q : ℍ), B⟫ - B.re * c) ^ 2 +
        axisWeight κ q * (⟪star (q : ℍ), B⟫ - B.re * c) ^ 2
      dsimp only [axisWeight] at *
      nlinarith
  rw [integral_const_mul, integral_add hi hi.comp_inv,
    integral_inv_eq_self (μ := haar) F] at hineq
  dsimp only [F] at hineq
  linarith

/-- Exact variance of the scalar excess expressed as a centered axial Haar integral. -/
theorem axis_variance_integral (κ : ℝ) :
    axisExcessSquare κ - axisExcess κ ^ 2 =
      κ ^ 2 / axisPartition κ * (∫ q : UnitQuaternion,
        axisWeight κ q * ((q : ℍ).re - axisMean κ) ^ 2 ∂haar) := by
  have hi : Integrable (axisWeight κ) haar :=
    (axisWeight_continuous κ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable (fun q : UnitQuaternion => axisWeight κ q * (q : ℍ).re) haar :=
    ((axisWeight_continuous κ).mul
      (Quaternion.continuous_re.comp continuous_subtype_val)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun q : UnitQuaternion => axisWeight κ q * (q : ℍ).re ^ 2) haar :=
    ((axisWeight_continuous κ).mul
      ((Quaternion.continuous_re.comp continuous_subtype_val).pow 2)
        ).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have he (c : ℝ) : (∫ q : UnitQuaternion,
      axisWeight κ q * ((q : ℍ).re - c) ^ 2 ∂haar) =
      (∫ q : UnitQuaternion, axisWeight κ q * (q : ℍ).re ^ 2 ∂haar) -
        (2 * c) * axisNumerator κ + c ^ 2 * axisPartition κ := by
    have hf : (fun q : UnitQuaternion => axisWeight κ q * ((q : ℍ).re - c) ^ 2) =
        (fun q : UnitQuaternion => (axisWeight κ q * (q : ℍ).re ^ 2 -
          (2 * c) * (axisWeight κ q * (q : ℍ).re)) + c ^ 2 * axisWeight κ q) := by
      funext q
      ring
    have hiSub : Integrable (fun q : UnitQuaternion =>
        axisWeight κ q * (q : ℍ).re ^ 2 -
          (2 * c) * (axisWeight κ q * (q : ℍ).re)) haar := hi2.sub (hi1.const_mul _)
    rw [hf, integral_add hiSub (hi.const_mul _),
      integral_sub hi2 (hi1.const_mul _), integral_const_mul, integral_const_mul]
    rfl
  have hs : axisExcessSquare κ = κ ^ 2 / axisPartition κ *
      ((∫ q : UnitQuaternion, axisWeight κ q * (q : ℍ).re ^ 2 ∂haar) -
        2 * axisNumerator κ + axisPartition κ) := by
    unfold axisExcessSquare
    have hf : (fun q : UnitQuaternion => axisWeight κ q * (κ * (1 - (q : ℍ).re)) ^ 2) =
        (fun q : UnitQuaternion => κ ^ 2 * (axisWeight κ q * ((q : ℍ).re - 1) ^ 2)) := by
      funext q
      ring
    rw [hf, integral_const_mul, he]
    ring
  rw [hs, axisExcess_identity, he]
  unfold axisMean
  field_simp [(axisPartition_pos κ).ne']
  ring

/-- The actual scalar conditional variance has an explicit positive lower bound. -/
theorem axis_variance_lower {κ : ℝ} (hκ : 50 ≤ κ) :
    (3 / 4 : ℝ) ≤ axisExcessSquare κ - axisExcess κ ^ 2 := by
  have hk : 0 < κ := by linarith
  have hm := axisExcess_bounds κ hk.le
  have hs := (abs_le.mp (axisExcessSquare_error (by linarith : 3 / 2 ≤ κ))).1
  have he : 75 / (2 * κ) ≤ (3 / 4 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * κ)).mpr
    linarith
  nlinarith [mul_nonneg hm.1 (sub_nonneg.mpr hm.2)]

/-- The covariance is exactly the centered, rotated axial Haar integral. -/
theorem covariance_rotated (β : ℝ) (A B : ℍ) (hA : A ≠ 0) :
    covariance β A B B =
      (∫ q : UnitQuaternion, axisWeight (2 * β * ‖A‖) q *
        (⟪(q : ℍ), star (orientation A hA : ℍ) * B⟫ -
          (star (orientation A hA : ℍ) * B).re * axisMean (2 * β * ‖A‖)) ^ 2 ∂haar) /
        axisPartition (2 * β * ‖A‖) := by
  rw [SU2WeightedRadial.covariance_centered, tiltLaw_integral]
  rw [tiltPartition_eq_axis β A hA]
  congr 1
  calc
    _ = ∫ q : UnitQuaternion, tiltWeight β A (orientation A hA * q) *
        (⟪((orientation A hA * q : UnitQuaternion) : ℍ), B⟫ - tiltMean β A B) ^ 2 ∂haar :=
      (integral_mul_left_eq_self (fun q : UnitQuaternion =>
        tiltWeight β A q * (⟪(q : ℍ), B⟫ - tiltMean β A B) ^ 2) (orientation A hA)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with q
      change tiltWeight β A (orientation A hA * q) *
        (⟪(orientation A hA : ℍ) * (q : ℍ), B⟫ - tiltMean β A B) ^ 2 = _
      rw [inner_left_rotation, rotated_real, orientation_inner, tiltMean_rotational]
      have hw : tiltWeight β A (orientation A hA * q) = axisWeight (2 * β * ‖A‖) q := by
        unfold tiltWeight axisWeight
        rw [oriented_inner]
        congr 1
        ring
      rw [hw]
      ring

/-- Exact radial-projection variance domination under the actual normalized Haar tilt. -/
theorem covariance_radial_domination (β : ℝ) (A B : ℍ) (hA : A ≠ 0) :
    (⟪A, B⟫ / ‖A‖) ^ 2 *
        (axisExcessSquare (2 * β * ‖A‖) - axisExcess (2 * β * ‖A‖) ^ 2) ≤
      (2 * β * ‖A‖) ^ 2 * covariance β A B B := by
  have h := axis_square_lower (2 * β * ‖A‖)
    (star (orientation A hA : ℍ) * B) (axisMean (2 * β * ‖A‖))
  rw [rotated_real, orientation_inner] at h
  have hs := mul_le_mul_of_nonneg_left h
    (div_nonneg (sq_nonneg (2 * β * ‖A‖)) (axisPartition_pos (2 * β * ‖A‖)).le)
  rw [axis_variance_integral, covariance_rotated β A B hA, rotated_real, orientation_inner]
  convert hs using 1 <;> ring

/-- A positive polynomial covariance floor in every nonzero radial probe direction. -/
theorem covariance_radial_lower (β : ℝ) (A B : ℍ) (hκ : 50 ≤ 2 * β * ‖A‖) :
    (3 / 4 : ℝ) * (⟪A, B⟫ / ‖A‖) ^ 2 ≤
      (2 * β * ‖A‖) ^ 2 * covariance β A B B := by
  have hA : A ≠ 0 := by
    intro h
    rw [h, norm_zero, mul_zero] at hκ
    norm_num at hκ
  have hs := mul_le_mul_of_nonneg_left (axis_variance_lower hκ)
    (sq_nonneg (⟪A, B⟫ / ‖A‖))
  calc
    _ ≤ (⟪A, B⟫ / ‖A‖) ^ 2 *
        (axisExcessSquare (2 * β * ‖A‖) - axisExcess (2 * β * ‖A‖) ^ 2) := by
      simpa only [mul_comm] using hs
    _ ≤ _ := covariance_radial_domination β A B hA

end
end UnifiedTheory.Clay.YangMills.SU2RadialCovarianceLower

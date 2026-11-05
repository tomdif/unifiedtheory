/- All natural moments of the actual one-link excess have the Gamma(3/2) limit.
These are local conditional moments; no continuum source estimate is asserted. -/
import UnifiedTheory.Clay.YangMills.SU2WilsonLocalSecondMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SU2ExcessAllMoments
noncomputable section
open MeasureTheory SU2QuaternionEquivalence SU2HaarTilt SU2HaarCovariance
open SU2WilsonLocalEquipartition SqrtSourceRemainder
open scoped Quaternion RealInnerProductSpace

def gammaMoment (m : ℕ) : ℝ := ∏ j ∈ Finset.range m, (3 / 2 + (j : ℝ))
def errorConstant (m : ℕ) : ℝ := 2 * (gammaMoment (m + 1) + (3 / 2) * gammaMoment m)
def momentBound (m : ℕ) : ℝ := 3 ^ m + gammaMoment m + errorConstant m

def axisMoment (m : ℕ) (κ : ℝ) : ℝ :=
  (∫ q : UnitQuaternion, axisWeight κ q * (κ * (1 - (q : ℍ).re)) ^ m ∂haar) /
    axisPartition κ

@[simp] theorem gammaMoment_zero : gammaMoment 0 = 1 := by simp [gammaMoment]

theorem gammaMoment_succ (m : ℕ) :
    gammaMoment (m+1) = gammaMoment m * (3/2 + (m : ℝ)) := by
  simp only [gammaMoment, Finset.prod_range_succ]

@[simp] theorem gammaMoment_one : gammaMoment 1 = 3/2 := by
  norm_num [gammaMoment_succ]

@[simp] theorem gammaMoment_two : gammaMoment 2 = 15/4 := by
  norm_num [gammaMoment_succ]

@[simp] theorem gammaMoment_three : gammaMoment 3 = 105/8 := by
  norm_num [gammaMoment_succ]

@[simp] theorem gammaMoment_four : gammaMoment 4 = 945/16 := by
  norm_num [gammaMoment_succ]

theorem gammaMoment_pos (m : ℕ) : 0 < gammaMoment m := by
  apply Finset.prod_pos
  intro j _
  positivity

theorem errorConstant_pos (m : ℕ) : 0 < errorConstant m := by
  unfold errorConstant
  have h := gammaMoment_pos m
  have h' := gammaMoment_pos (m + 1)
  positivity

theorem momentBound_pos (m : ℕ) : 0 < momentBound m := by
  unfold momentBound
  have h := gammaMoment_pos m
  have h' := errorConstant_pos m
  positivity

@[simp] theorem axisMoment_zero_tilt (m : ℕ) : axisMoment m 0 = (0 : ℝ)^m := by
  simp [axisMoment, axisWeight]

theorem axisMoment_eq_gamma (m : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    axisMoment m κ = gammaAverage (3 / 2) (fun u => u^m * cutoffSqrt κ u) /
      gammaAverage (3 / 2) (cutoffSqrt κ) := by
  unfold axisMoment
  rw [SU2HaarScalarBridge.weighted_coordinate_formula
    SU2SemicircleSlice.firstCoordinateFormula κ (fun t => (κ * (1 - t)) ^ m) (by fun_prop),
    SU2HaarScalarBridge.axisPartition_eq_scalar SU2SemicircleSlice.firstCoordinateFormula,
    div_div_div_cancel_right₀ (SU2ScalarTilt.partition_pos 0).ne',
    SU2ScalarTilt.excess_transform hκ (fun u => u ^ m), SU2ScalarTilt.partition_transform hκ,
    mul_div_mul_left _ _ (SU2ScalarTilt.changeFactor_pos hκ).ne']
  have he : (fun u : ℝ => cutoffSqrt κ u * u ^ m) =
      (fun u : ℝ => u ^ m * cutoffSqrt κ u) := by funext u; ring
  rw [he]
  unfold gammaAverage
  rw [div_div_div_cancel_right₀ (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)).ne']

/-- Explicit uniform-in-order formula; the constants are proved finite products. -/
theorem axisMoment_error (m : ℕ) {κ : ℝ} (hκ : 3 / 2 ≤ κ) :
    |axisMoment m κ - gammaMoment m| ≤ errorConstant m / κ := by
  have hk : 0 < κ := by linarith
  let D := gammaAverage (3 / 2) (cutoffSqrt κ)
  let N := gammaAverage (3 / 2) (fun u => u ^ m * cutoffSqrt κ u)
  have hd : 1 / 2 ≤ D := su2_denominator_ge_half hκ
  have hD : 0 < D := by linarith
  have hn : |N - gammaMoment m| ≤ gammaMoment (m+1) / κ := by
    have h := gamma_average_moment_expansion_product
      (by norm_num : (0 : ℝ) < 3 / 2) hk m 1
    simp only [Finset.sum_range_one, coefficient_zero, one_mul, Nat.add_zero, pow_zero,
      div_one, pow_one] at h
    convert h using 1
    dsimp only [N, gammaMoment]
    ring
  have hd' : |D - 1| ≤ 3 / (2 * κ) := by
    have h := su2_denominator_expansion hk 1
    norm_num [Finset.prod_range_succ, coefficient_zero] at h
    exact h
  have hM := (gammaMoment_pos m).le
  have he : |N - gammaMoment m * D| ≤
      (gammaMoment (m+1) + (3/2)*gammaMoment m) / κ := by
    calc
      _ = |(N - gammaMoment m) - gammaMoment m * (D - 1)| := by congr 1; ring
      _ ≤ |N - gammaMoment m| + |gammaMoment m * (D - 1)| := abs_sub _ _
      _ ≤ gammaMoment (m+1) / κ + gammaMoment m * (3 / (2*κ)) := by
        rw [abs_mul, abs_of_nonneg hM]
        exact add_le_add hn (mul_le_mul_of_nonneg_left hd' hM)
      _ = _ := by ring
  rw [axisMoment_eq_gamma m hk]
  change |N / D - gammaMoment m| ≤ _
  have hh : N / D - gammaMoment m = (N - gammaMoment m * D) / D := by field_simp
  rw [hh, abs_div, abs_of_pos hD]
  apply (div_le_iff₀ hD).mpr
  have h := mul_le_mul_of_nonneg_left hd
    (div_nonneg (errorConstant_pos m).le hk.le)
  calc
    _ ≤ (gammaMoment (m+1) + (3/2)*gammaMoment m) / κ := he
    _ = errorConstant m / κ * (1/2) := by unfold errorConstant; ring
    _ ≤ _ := h

theorem coordinate_abs_le_one (q : UnitQuaternion) : |(q : ℍ).re| ≤ 1 := by
  have h := abs_real_inner_le_norm (q : ℍ) (1 : ℍ)
  simpa only [Quaternion.inner_def, star_one, mul_one, norm_one,
    CStarRing.norm_coe_unitary, one_mul] using h

/-- A global elementary bound, also covering small or cancelling staples. -/
theorem axisMoment_power_bound (m : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    0 ≤ axisMoment m κ ∧ axisMoment m κ ≤ (2 * κ)^m := by
  have hpoint (q : UnitQuaternion) : 0 ≤ κ * (1 - (q : ℍ).re) ∧
      κ * (1 - (q : ℍ).re) ≤ 2 * κ := by
    have h := abs_le.mp (coordinate_abs_le_one q)
    constructor <;> nlinarith
  have hi : Integrable (fun q : UnitQuaternion =>
      axisWeight κ q * (κ * (1 - (q : ℍ).re))^m) haar :=
    ((axisWeight_continuous κ).mul
      ((continuous_const.mul (continuous_const.sub
        (Quaternion.continuous_re.comp continuous_subtype_val))).pow m)
          ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hw : Integrable (axisWeight κ) haar :=
    (axisWeight_continuous κ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold axisMoment
  constructor
  · apply div_nonneg _ (axisPartition_pos κ).le
    exact integral_nonneg (fun q => mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (hpoint q).1 m))
  · apply (div_le_iff₀ (axisPartition_pos κ)).mpr
    have h := integral_mono hi (hw.const_mul ((2*κ)^m)) (fun q => by
      have hp := pow_le_pow_left₀ (hpoint q).1 (hpoint q).2 m
      have hh := mul_le_mul_of_nonneg_left hp (Real.exp_pos (κ * (q : ℍ).re)).le
      simpa only [mul_comm] using hh)
    rw [integral_const_mul] at h
    exact h

/-- One fixed constant bounds each moment over all nonnegative tilt parameters. -/
theorem axisMoment_bounds (m : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    0 ≤ axisMoment m κ ∧ axisMoment m κ ≤ momentBound m := by
  refine ⟨(axisMoment_power_bound m κ hκ).1, ?_⟩
  by_cases hk : κ ≤ 3 / 2
  · have h := (axisMoment_power_bound m κ hκ).2
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2*κ) (by linarith : 2*κ ≤ 3) m
    have hM := (gammaMoment_pos m).le
    have hE := (errorConstant_pos m).le
    unfold momentBound
    linarith
  · have he := (abs_le.mp (axisMoment_error m (le_of_lt (lt_of_not_ge hk)))).2
    have hκ' : 1 ≤ κ := by linarith
    have he' : errorConstant m / κ ≤ errorConstant m :=
      div_le_self (errorConstant_pos m).le hκ'
    unfold momentBound
    have h3 : (0 : ℝ) ≤ 3^m := by positivity
    linarith

/-- Exact rotation identifies every actual tilted quaternion moment with the scalar model. -/
theorem excess_pow_mean (m : ℕ) (β : ℝ) (A : ℍ) :
    (∫ q : UnitQuaternion, (excess β A q)^m ∂tiltLaw β A) =
      axisMoment m (2 * β * ‖A‖) := by
  by_cases hA : A = 0
  · subst A
    letI := tiltLaw_probability β (0 : ℍ)
    simp [excess]
  · rw [tiltLaw_integral, tiltPartition_eq_axis β A hA]
    unfold axisMoment
    congr 1
    calc
      _ = ∫ q : UnitQuaternion, tiltWeight β A (orientation A hA * q) *
          (excess β A (orientation A hA * q))^m ∂haar :=
        (integral_mul_left_eq_self (fun q : UnitQuaternion =>
          tiltWeight β A q * (excess β A q)^m) (orientation A hA)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with q
        have hw : tiltWeight β A (orientation A hA * q) = axisWeight (2*β*‖A‖) q := by
          unfold tiltWeight axisWeight
          rw [oriented_inner]
          congr 1
          ring
        have hx : excess β A (orientation A hA * q) =
            (2*β*‖A‖) * (1-(q : ℍ).re) := by
          unfold excess
          rw [oriented_inner]
          ring
        rw [hw, hx]

end
end UnifiedTheory.Clay.YangMills.SU2ExcessAllMoments

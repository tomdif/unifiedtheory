/-
Actual SU(2) Haar concentration and scale-sensitive induced curvature.
Antitone cutoff reweighting lowers the exact Gamma moments; the proved Haar
semicircle dictionary transports these bounds to the original quaternion law.
No concentration or covariance estimate is supplied as a premise.

The directional estimates apply to the actual one-link Wilson fiber. They
control a single induced interaction; they do not assert contraction of later
interactions or a physical continuum limit.
-/
import UnifiedTheory.Clay.YangMills.SU2InducedAction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2HaarCovariance
noncomputable section
open MeasureTheory Set SqrtSourceRemainder SU2QuaternionEquivalence SU2HaarTilt
open scoped Quaternion RealInnerProductSpace

theorem cutoff_antitone {κ : ℝ} (hκ : 0 < κ) : Antitone (cutoffSqrt κ) := by
  intro u v huv
  unfold cutoffSqrt
  apply Real.sqrt_le_sqrt
  apply max_le_max_right
  have h := div_le_div_of_nonneg_right huv (show 0 ≤ 2 * κ by positivity)
  linarith

theorem cutoff_moment_integrable {α κ : ℝ} (hα : 0 < α) (hκ : 0 < κ) (q : ℕ) :
    IntegrableOn (fun u => gammaWeight α u * (u ^ q * cutoffSqrt κ u)) (Ioi 0) := by
  have h := gamma_cutoff_integrable (show 0 < α + (q : ℝ) by positivity) hκ
  apply h.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  rw [← mul_assoc, gammaWeight_mul_pow α hu q]

/-- Antitone reweighting lowers an exact Gamma moment. -/
theorem cutoff_moment_comparison {α κ c : ℝ} (hα : 0 < α) (hκ : 0 < κ)
    (hc : 0 ≤ c) (q : ℕ) (hm : Real.Gamma (α + q) = c ^ q * Real.Gamma α) :
    gammaIntegral α (fun u => u ^ q * cutoffSqrt κ u) ≤
      c ^ q * gammaIntegral α (cutoffSqrt κ) := by
  have hcut := gamma_cutoff_integrable hα hκ
  have hraw := gamma_moment_integrable hα q
  have hw := gammaWeight_integrable hα
  have hnum := cutoff_moment_integrable hα hκ q
  have hint := (hcut.const_mul (c ^ q)).add
    ((hraw.sub (hw.const_mul (c ^ q))).const_mul (cutoffSqrt κ c))
  have hpoint (u : ℝ) (hu : u ∈ Ioi 0) :
      gammaWeight α u * (u ^ q * cutoffSqrt κ u) ≤
        c ^ q * (gammaWeight α u * cutoffSqrt κ u) +
          cutoffSqrt κ c * (gammaWeight α u * u ^ q - c ^ q * gammaWeight α u) := by
    have hsign : (u ^ q - c ^ q) * (cutoffSqrt κ u - cutoffSqrt κ c) ≤ 0 := by
      rcases le_total u c with huc | hcu
      · exact mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (pow_le_pow_left₀ hu.le huc q))
          (sub_nonneg.mpr (cutoff_antitone hκ huc))
      · exact mul_nonpos_of_nonneg_of_nonpos
          (sub_nonneg.mpr (pow_le_pow_left₀ hc hcu q))
          (sub_nonpos.mpr (cutoff_antitone hκ hcu))
    have h := mul_nonpos_of_nonneg_of_nonpos (gammaWeight_nonneg α hu.le) hsign
    nlinarith
  have h := integral_mono_ae hnum hint (by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact hpoint u hu)
  simp only [Pi.add_apply, Pi.sub_apply] at h
  have hrest : IntegrableOn (fun u => cutoffSqrt κ c *
      (gammaWeight α u * u ^ q - c ^ q * gammaWeight α u)) (Ioi 0) := by
    simpa only [Pi.sub_apply] using
      ((hraw.sub (hw.const_mul (c ^ q))).const_mul (cutoffSqrt κ c))
  rw [integral_add (hcut.const_mul _) hrest, integral_const_mul, integral_const_mul,
    integral_sub hraw (hw.const_mul _), integral_const_mul,
    integral_gamma_moment hα q, integral_gammaWeight hα, hm] at h
  simpa only [sub_self, mul_zero, add_zero, gammaIntegral] using h

theorem gamma_first_cutoff_le {κ : ℝ} (hκ : 0 < κ) :
    gammaIntegral (3 / 2) (fun u => u * cutoffSqrt κ u) ≤
      (3 / 2 : ℝ) * gammaIntegral (3 / 2) (cutoffSqrt κ) := by
  have hm : Real.Gamma ((3 / 2 : ℝ) + (1 : ℕ)) =
      (3 / 2 : ℝ) ^ (1 : ℕ) * Real.Gamma (3 / 2) := by
    simpa only [Nat.cast_one, pow_one] using Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0)
  simpa only [pow_one] using cutoff_moment_comparison
    (by norm_num : (0 : ℝ) < 3 / 2) hκ (by norm_num : (0 : ℝ) ≤ 3 / 2) 1 hm

theorem gamma_second_cutoff_le {κ : ℝ} (hκ : 0 < κ) :
    gammaIntegral (3 / 2) (fun u => u ^ 2 * cutoffSqrt κ u) ≤
      (15 / 4 : ℝ) * gammaIntegral (3 / 2) (cutoffSqrt κ) := by
  have hc : (Real.sqrt (15 / 4 : ℝ)) ^ 2 = 15 / 4 := Real.sq_sqrt (by norm_num)
  have hm : Real.Gamma ((3 / 2 : ℝ) + (2 : ℕ)) =
      (Real.sqrt (15 / 4 : ℝ)) ^ 2 * Real.Gamma (3 / 2) := by
    rw [hc]
    have h1 := Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0)
    have h2 := Real.Gamma_add_one (by norm_num : (5 / 2 : ℝ) ≠ 0)
    norm_num at h1 h2 ⊢
    rw [h2, h1]
    ring
  have h := cutoff_moment_comparison (by norm_num : (0 : ℝ) < 3 / 2) hκ
    (Real.sqrt_nonneg (15 / 4 : ℝ)) 2 hm
  simpa only [hc] using h

theorem gamma_cutoff_pos {κ : ℝ} (hκ : 0 < κ) :
    0 < gammaIntegral (3 / 2) (cutoffSqrt κ) := by
  have h := SU2ScalarTilt.partition_pos κ
  rw [SU2ScalarTilt.partition_transform hκ] at h
  exact (mul_pos_iff_of_pos_left (SU2ScalarTilt.changeFactor_pos hκ)).mp h

theorem axisExcess_le {κ : ℝ} (hκ : 0 < κ) : axisExcess κ ≤ 3 / 2 := by
  rw [SU2HaarScalarBridge.axisExcess_eq_scalar SU2SemicircleSlice.firstCoordinateFormula]
  unfold SU2ScalarTilt.excessMean
  rw [SU2ScalarTilt.excessIntegral_transform hκ, SU2ScalarTilt.partition_transform hκ,
    mul_div_mul_left _ _ (SU2ScalarTilt.changeFactor_pos hκ).ne']
  exact (div_le_iff₀ (gamma_cutoff_pos hκ)).mpr (gamma_first_cutoff_le hκ)

theorem axis_concentration {κ : ℝ} (hκ : 0 < κ) :
    1 - axisMean κ ≤ 3 / (2 * κ) := by
  have h := axisExcess_le hκ
  rw [axisExcess_identity] at h
  apply (le_div_iff₀ (show 0 < 2 * κ by positivity)).mpr
  nlinarith


/-- Variance is no larger than the square deviation from any fixed center. -/
theorem covariance_le_square_deviation (β : ℝ) (A B : ℍ) (c : ℝ) :
    SU2InducedAction.covariance β A B B ≤
      ∫ q : UnitQuaternion, (⟪(q : ℍ), B⟫ - c) ^ 2 ∂tiltLaw β A := by
  letI := tiltLaw_probability β A
  have hi : Integrable (fun q : UnitQuaternion => ⟪(q : ℍ), B⟫) (tiltLaw β A) :=
    (continuous_subtype_val.inner continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun q : UnitQuaternion => ⟪(q : ℍ), B⟫ ^ 2) (tiltLaw β A) :=
    ((continuous_subtype_val.inner continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (∫ q : UnitQuaternion, (⟪(q : ℍ), B⟫ - c) ^ 2 ∂tiltLaw β A) =
      (∫ q : UnitQuaternion, ⟪(q : ℍ), B⟫ ^ 2 ∂tiltLaw β A) -
        2 * c * tiltMean β A B + c ^ 2 := by
    have hf : (fun q : UnitQuaternion => (⟪(q : ℍ), B⟫ - c) ^ 2) =
        (fun q : UnitQuaternion => (⟪(q : ℍ), B⟫ ^ 2 -
          (2 * c) * ⟪(q : ℍ), B⟫) + c ^ 2) := by funext q; ring
    have hisub : Integrable (fun q : UnitQuaternion =>
        ⟪(q : ℍ), B⟫ ^ 2 - (2 * c) * ⟪(q : ℍ), B⟫) (tiltLaw β A) :=
      hi2.sub (hi.const_mul _)
    rw [hf, integral_add hisub (integrable_const _),
      integral_sub hi2 (hi.const_mul _), integral_const_mul, tiltLaw_inner_mean]
    simp
  rw [he]
  unfold SU2InducedAction.covariance
  simp only [← pow_two]
  nlinarith [sq_nonneg (tiltMean β A B - c)]

theorem covariance_le_distance (β : ℝ) (A B a : ℍ) :
    SU2InducedAction.covariance β A B B ≤
      ‖B‖ ^ 2 * ∫ q : UnitQuaternion, ‖(q : ℍ) - a‖ ^ 2 ∂tiltLaw β A := by
  letI := tiltLaw_probability β A
  apply (covariance_le_square_deviation β A B ⟪a, B⟫).trans
  rw [← integral_const_mul]
  apply integral_mono
  · exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.of_compactSpace _)
  · exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.of_compactSpace _)
  · intro q
    dsimp only
    rw [← inner_sub_left]
    have h := abs_real_inner_le_norm ((q : ℍ) - a) B
    have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 h
    rw [sq_abs] at hs
    nlinarith

theorem mean_orientation (β : ℝ) (A : ℍ) (hA : A ≠ 0) :
    tiltMean β A (orientation A hA : ℍ) = axisMean (2 * β * ‖A‖) := by
  have hr : ‖A‖ ≠ 0 := norm_ne_zero_iff.mpr hA
  have hi : ⟪A, (orientation A hA : ℍ)⟫ = ‖A‖ := by
    rw [real_inner_comm, orientation_inner, real_inner_self_eq_norm_sq]
    field_simp
  rw [tiltMean_rotational, hi]
  field_simp

theorem distance_orientation_integral (β : ℝ) (A : ℍ) (hA : A ≠ 0) :
    (∫ q : UnitQuaternion, ‖(q : ℍ) - (orientation A hA : ℍ)‖ ^ 2 ∂tiltLaw β A) =
      2 * (1 - axisMean (2 * β * ‖A‖)) := by
  letI := tiltLaw_probability β A
  have hi : Integrable (fun q : UnitQuaternion =>
      ⟪(q : ℍ), (orientation A hA : ℍ)⟫) (tiltLaw β A) :=
    (continuous_subtype_val.inner continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (q : UnitQuaternion) : ‖(q : ℍ) - (orientation A hA : ℍ)‖ ^ 2 =
      2 - 2 * ⟪(q : ℍ), (orientation A hA : ℍ)⟫ := by
    rw [norm_sub_sq_real, CStarRing.norm_of_mem_unitary q.property,
      CStarRing.norm_of_mem_unitary (orientation A hA).property]
    ring
  simp_rw [he]
  rw [integral_sub (integrable_const _) (hi.const_mul _), integral_const_mul,
    tiltLaw_inner_mean, mean_orientation]
  simp
  ring

/-- Actual tilted Haar covariance decays with the tilt magnitude. -/
theorem covariance_le_inverse_tilt (β : ℝ) (A B : ℍ) (hβ : 0 < β) (hA : A ≠ 0) :
    SU2InducedAction.covariance β A B B ≤ 3 * ‖B‖ ^ 2 / (2 * β * ‖A‖) := by
  have hr : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have h := covariance_le_distance β A B (orientation A hA : ℍ)
  rw [distance_orientation_integral] at h
  calc
    _ ≤ ‖B‖ ^ 2 * (2 * (1 - axisMean (2 * β * ‖A‖))) := h
    _ ≤ ‖B‖ ^ 2 * (2 * (3 / (2 * (2 * β * ‖A‖)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (axis_concentration (by positivity)) (by norm_num))
        (sq_nonneg _)
    _ = _ := by field_simp


/-- The actual normalized square of the excess coordinate under Haar tilt. -/
def axisExcessSquare (κ : ℝ) : ℝ :=
  (∫ q : UnitQuaternion, axisWeight κ q * (κ * (1 - (q : ℍ).re)) ^ 2 ∂haar) /
    axisPartition κ

theorem axisExcessSquare_le {κ : ℝ} (hκ : 0 < κ) : axisExcessSquare κ ≤ 15 / 4 := by
  unfold axisExcessSquare
  rw [SU2HaarScalarBridge.weighted_coordinate_formula
    SU2SemicircleSlice.firstCoordinateFormula κ (fun t => (κ * (1 - t)) ^ 2) (by fun_prop),
    SU2HaarScalarBridge.axisPartition_eq_scalar SU2SemicircleSlice.firstCoordinateFormula,
    div_div_div_cancel_right₀ (SU2ScalarTilt.partition_pos 0).ne',
    SU2ScalarTilt.excess_transform hκ (fun u => u ^ 2), SU2ScalarTilt.partition_transform hκ,
    mul_div_mul_left _ _ (SU2ScalarTilt.changeFactor_pos hκ).ne']
  have he : (fun u : ℝ => cutoffSqrt κ u * u ^ 2) =
      (fun u : ℝ => u ^ 2 * cutoffSqrt κ u) := by funext u; ring
  rw [he]
  exact (div_le_iff₀ (gamma_cutoff_pos hκ)).mpr (gamma_second_cutoff_le hκ)

theorem tiltLaw_integral (β : ℝ) (A : ℍ) (F : UnitQuaternion → ℝ) :
    (∫ q, F q ∂tiltLaw β A) =
      (∫ q, tiltWeight β A q * F q ∂haar) / tiltPartition β A :=
  LocalGibbsComparison.weighted_integral haar _ (tiltWeight_continuous β A).measurable
    (fun _ => (Real.exp_pos _).le) (tiltPartition_pos β A) _

/-- Exact radial square deviation, expressed using the actual Haar excess moment. -/
theorem radial_square_deviation (β : ℝ) (A : ℍ) (hβ : 0 < β) (hA : A ≠ 0) :
    (∫ q : UnitQuaternion, (⟪(q : ℍ), A⟫ - ‖A‖) ^ 2 ∂tiltLaw β A) =
      ‖A‖ ^ 2 / (2 * β * ‖A‖) ^ 2 * axisExcessSquare (2 * β * ‖A‖) := by
  have hr : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hk : 2 * β * ‖A‖ ≠ 0 := ne_of_gt (by positivity)
  rw [tiltLaw_integral, tiltPartition_radial]
  have he : (∫ q : UnitQuaternion, tiltWeight β A q * (⟪(q : ℍ), A⟫ - ‖A‖) ^ 2 ∂haar) =
      (‖A‖ ^ 2 / (2 * β * ‖A‖) ^ 2) *
        (∫ q : UnitQuaternion, axisWeight (2 * β * ‖A‖) q *
          ((2 * β * ‖A‖) * (1 - (q : ℍ).re)) ^ 2 ∂haar) := by
    calc
      _ = ∫ q : UnitQuaternion, tiltWeight β A (orientation A hA * q) *
          (⟪((orientation A hA * q : UnitQuaternion) : ℍ), A⟫ - ‖A‖) ^ 2 ∂haar :=
        (integral_mul_left_eq_self
          (fun q : UnitQuaternion => tiltWeight β A q * (⟪(q : ℍ), A⟫ - ‖A‖) ^ 2)
          (orientation A hA)).symm
      _ = _ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with q
        unfold tiltWeight axisWeight
        rw [oriented_inner]
        have hex : 2 * β * (‖A‖ * (q : ℍ).re) = (2 * β * ‖A‖) * (q : ℍ).re := by ring
        rw [hex]
        field_simp
        ring
  rw [he]
  unfold axisExcessSquare
  ring

/-- The actual radial variance has the stronger inverse-square coupling bound. -/
theorem covariance_radial_le (β : ℝ) (A : ℍ) (hβ : 0 < β) (hA : A ≠ 0) :
    SU2InducedAction.covariance β A A A ≤ 15 / (16 * β ^ 2) := by
  have hr : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have h := covariance_le_square_deviation β A A ‖A‖
  rw [radial_square_deviation β A hβ hA] at h
  calc
    _ ≤ ‖A‖ ^ 2 / (2 * β * ‖A‖) ^ 2 * axisExcessSquare (2 * β * ‖A‖) := h
    _ ≤ ‖A‖ ^ 2 / (2 * β * ‖A‖) ^ 2 * (15 / 4) :=
      mul_le_mul_of_nonneg_left (axisExcessSquare_le (by positivity)) (by positivity)
    _ = _ := by field_simp; ring


theorem covariance_radial_le_all (β : ℝ) (A : ℍ) (hβ : 0 < β) :
    SU2InducedAction.covariance β A A A ≤ 15 / (16 * β ^ 2) := by
  by_cases hA : A = 0
  · subst A
    simp only [SU2InducedAction.covariance, inner_zero_right, mul_zero, integral_zero,
      tiltMean_zero, sub_zero]
    positivity
  · exact covariance_radial_le β A hβ hA

/-- A positive staple radius improves the induced vector Hessian from β² to β/r. -/
theorem potential_good_curvature (β : ℝ) (A B : ℍ) (t : ℝ)
    (hβ : 0 < β) (hA : A + t • B ≠ 0) :
    |deriv (fun s : ℝ => deriv (fun u : ℝ => SU2InducedAction.potential β (A + u • B)) s) t| ≤
      6 * β * ‖B‖ ^ 2 / ‖A + t • B‖ := by
  rw [(SU2InducedAction.potential_direction_second β A B t).deriv,
    abs_neg, abs_of_nonneg (mul_nonneg (by positivity)
      (SU2InducedAction.covariance_self_nonneg β (A + t • B) B))]
  calc
    _ ≤ (4 * β ^ 2) * (3 * ‖B‖ ^ 2 / (2 * β * ‖A + t • B‖)) :=
      mul_le_mul_of_nonneg_left (covariance_le_inverse_tilt β (A + t • B) B hβ hA)
        (by positivity)
    _ = _ := by field_simp; ring

/-- The radial direction has a coupling-independent induced Hessian bound. -/
theorem potential_radial_curvature (β : ℝ) (A : ℍ) (hβ : 0 < β) :
    |deriv (fun s : ℝ => deriv (fun u : ℝ => SU2InducedAction.potential β (A + u • A)) s) 0| ≤
      15 / 4 := by
  rw [(SU2InducedAction.potential_direction_second β A A 0).deriv]
  simp only [zero_smul, add_zero]
  rw [abs_neg, abs_of_nonneg (mul_nonneg (by positivity)
    (SU2InducedAction.covariance_self_nonneg β A A))]
  calc
    _ ≤ (4 * β ^ 2) * (15 / (16 * β ^ 2)) :=
      mul_le_mul_of_nonneg_left (covariance_radial_le_all β A hβ) (by positivity)
    _ = _ := by field_simp; ring

open RegulatedGauge PeriodicLattice4 WilsonUniformVariance WilsonSingleLinkStaples

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- Good-region source curvature for the actual original Wilson fiber action. -/
theorem wilson_sourced_good_curvature (x : Vertex n) (μ : Fin 4) (β t r₀ : ℝ)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) (hr₀ : 0 < r₀)
    (hgood : r₀ ≤ ‖β • exteriorStaple n x μ r - t • exteriorWeightedStaple n x μ r f‖) :
    |deriv (fun s : ℝ => deriv (fun u : ℝ => GibbsMarginalTower.effectiveAction haar
      (fun z => SU2WilsonConditionalSource.splitAction n x μ β z -
        u * SU2WilsonConditionalSource.splitSource n x μ f z) r) s) t| ≤
      6 * ‖exteriorWeightedStaple n x μ r f‖ ^ 2 / r₀ := by
  let V := β • exteriorStaple n x μ r - t • exteriorWeightedStaple n x μ r f
  let B := exteriorWeightedStaple n x μ r f
  have hV : V ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hr₀.trans_le hgood))
  rw [SU2InducedAction.wilson_sourced_curvature]
  change |-4 * SU2InducedAction.covariance 1 V B B| ≤ 6 * ‖B‖ ^ 2 / r₀
  rw [abs_mul, abs_of_nonneg (SU2InducedAction.covariance_self_nonneg 1 V B)]
  norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  have hcov := covariance_le_inverse_tilt 1 V B (by norm_num) hV
  calc
    _ ≤ 4 * (3 * ‖B‖ ^ 2 / (2 * 1 * ‖V‖)) :=
      mul_le_mul_of_nonneg_left hcov (by norm_num)
    _ = 6 * ‖B‖ ^ 2 / ‖V‖ := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hr₀ hgood

omit [NeZero n] [Fact (1 < n)] in
/-- Uniform scalar-action weights are radial, with actual conditional variance O(β⁻²). -/
theorem wilson_radial_covariance_le (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r : Exterior n Q x μ) (hβ : 0 < β) :
    SU2InducedAction.covariance β (exteriorStaple n x μ r)
      (exteriorStaple n x μ r) (exteriorStaple n x μ r) ≤ 15 / (16 * β ^ 2) :=
  covariance_radial_le_all β (exteriorStaple n x μ r) hβ

end
end UnifiedTheory.Clay.YangMills.SU2HaarCovariance

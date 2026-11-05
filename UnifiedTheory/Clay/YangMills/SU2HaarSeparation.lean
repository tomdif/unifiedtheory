/- Continuous tests separating two actual concentrated SU(2) Haar tilts.
The squared-distance ratio yields an inverse-beta error, directly from the
proved exact orientation second moment. No Gaussian approximation is used. -/
import UnifiedTheory.Clay.YangMills.SU2HaarCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SU2HaarSeparation
noncomputable section
open MeasureTheory SU2QuaternionEquivalence SU2HaarTilt SU2HaarCovariance
open scoped Quaternion RealInnerProductSpace

theorem separation_sq_le (a b q : UnitQuaternion) :
    ‖(a : ℍ) - (b : ℍ)‖ ^ 2 ≤
      2 * (‖(q : ℍ) - (a : ℍ)‖ ^ 2 + ‖(q : ℍ) - (b : ℍ)‖ ^ 2) := by
  have ht : ‖(a : ℍ) - (b : ℍ)‖ ≤
      ‖(q : ℍ) - (a : ℍ)‖ + ‖(q : ℍ) - (b : ℍ)‖ := by
    calc
      _ = ‖((q : ℍ) - (b : ℍ)) - ((q : ℍ) - (a : ℍ))‖ := by congr 1; abel
      _ ≤ _ := by simpa only [add_comm] using
        (norm_sub_le ((q : ℍ) - (b : ℍ)) ((q : ℍ) - (a : ℍ)))
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 ht
  nlinarith [sq_nonneg (‖(q : ℍ) - (a : ℍ)‖ - ‖(q : ℍ) - (b : ℍ)‖)]

theorem separation_sq_pos (a b : UnitQuaternion) (hab : a ≠ b) :
    0 < ‖(a : ℍ) - (b : ℍ)‖ ^ 2 := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  exact sub_ne_zero.mpr (fun h => hab (Subtype.ext h))

theorem denominator_pos (a b : UnitQuaternion) (hab : a ≠ b) (q : UnitQuaternion) :
    0 < ‖(q : ℍ) - (a : ℍ)‖ ^ 2 + ‖(q : ℍ) - (b : ℍ)‖ ^ 2 := by
  have h := separation_sq_pos a b hab
  have hle := separation_sq_le a b q
  linarith

/-- A continuous [0,1]-valued test equal to one at a and zero at b. -/
def separator (a b : UnitQuaternion) (hab : a ≠ b) : C(UnitQuaternion, ℝ) :=
  ⟨fun q => ‖(q : ℍ) - (b : ℍ)‖ ^ 2 /
    (‖(q : ℍ) - (a : ℍ)‖ ^ 2 + ‖(q : ℍ) - (b : ℍ)‖ ^ 2),
    Continuous.div (by fun_prop) (by fun_prop) (fun q => (denominator_pos a b hab q).ne')⟩

theorem separator_nonneg (a b : UnitQuaternion) (hab : a ≠ b) (q : UnitQuaternion) :
    0 ≤ separator a b hab q :=
  div_nonneg (sq_nonneg _) (denominator_pos a b hab q).le

theorem separator_le_one (a b : UnitQuaternion) (hab : a ≠ b) (q : UnitQuaternion) :
    separator a b hab q ≤ 1 := by
  dsimp only [separator, ContinuousMap.coe_mk]
  apply (div_le_one (denominator_pos a b hab q)).mpr
  nlinarith [sq_nonneg ‖(q : ℍ) - (a : ℍ)‖]

theorem separator_oscillation (a b : UnitQuaternion) (hab : a ≠ b)
    (q r : UnitQuaternion) : |separator a b hab q - separator a b hab r| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [separator_nonneg a b hab q, separator_nonneg a b hab r,
    separator_le_one a b hab q, separator_le_one a b hab r]

theorem separator_distance_bound (a b : UnitQuaternion) (hab : a ≠ b)
    (q : UnitQuaternion) :
    separator a b hab q ≤ (2 / ‖(a : ℍ) - (b : ℍ)‖ ^ 2) *
      ‖(q : ℍ) - (b : ℍ)‖ ^ 2 := by
  have hs := separation_sq_pos a b hab
  have hd := denominator_pos a b hab q
  have hle := separation_sq_le a b q
  dsimp only [separator, ContinuousMap.coe_mk]
  apply (div_le_iff₀ hd).mpr
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (le_div_iff₀ hs).mpr
  nlinarith [mul_nonneg (sq_nonneg ‖(q : ℍ) - (b : ℍ)‖) (sub_nonneg.mpr hle)]

theorem separator_complement_bound (a b : UnitQuaternion) (hab : a ≠ b)
    (q : UnitQuaternion) :
    1 - separator a b hab q ≤ (2 / ‖(a : ℍ) - (b : ℍ)‖ ^ 2) *
      ‖(q : ℍ) - (a : ℍ)‖ ^ 2 := by
  have he : 1 - separator a b hab q = separator b a hab.symm q := by
    dsimp only [separator, ContinuousMap.coe_mk]
    have hd := (denominator_pos a b hab q).ne'
    rw [add_comm (‖(q : ℍ) - (b : ℍ)‖ ^ 2)]
    apply (eq_div_iff hd).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hd]
    ring
  rw [he]
  simpa only [norm_sub_rev] using separator_distance_bound b a hab.symm q

/-- Two mean squared distance bounds produce a lower bound on actual expectation separation. -/
theorem integral_separation (a b : UnitQuaternion) (hab : a ≠ b)
    (μ ν : Measure UnitQuaternion) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ε δ : ℝ)
    (hμ : (∫ q, ‖(q : ℍ) - (a : ℍ)‖ ^ 2 ∂μ) ≤ ε)
    (hν : (∫ q, ‖(q : ℍ) - (b : ℍ)‖ ^ 2 ∂ν) ≤ δ) :
    1 - (2 / ‖(a : ℍ) - (b : ℍ)‖ ^ 2) * (ε + δ) ≤
      (∫ q, separator a b hab q ∂μ) - (∫ q, separator a b hab q ∂ν) := by
  have hpos : 0 ≤ 2 / ‖(a : ℍ) - (b : ℍ)‖ ^ 2 := by positivity
  have hf : Integrable (separator a b hab) μ :=
    (separator a b hab).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hl := integral_mono ((integrable_const 1).sub hf)
    (Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.of_compactSpace _)) (separator_complement_bound a b hab)
  dsimp only [Pi.sub_apply] at hl
  rw [integral_sub (integrable_const 1) hf, integral_const_mul] at hl
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hl
  have hu : (∫ q, separator a b hab q ∂ν) ≤
      ∫ q, (2 / ‖(a : ℍ) - (b : ℍ)‖ ^ 2) * ‖(q : ℍ) - (b : ℍ)‖ ^ 2 ∂ν := integral_mono
    ((separator a b hab).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.of_compactSpace _)) (separator_distance_bound a b hab)
  rw [integral_const_mul] at hu
  have hle := mul_le_mul_of_nonneg_left hμ hpos
  have hue := mul_le_mul_of_nonneg_left hν hpos
  linarith

theorem orientation_distance_bound (β : ℝ) (hβ : 0 < β) (A : ℍ) (hA : A ≠ 0) :
    (∫ q : UnitQuaternion, ‖(q : ℍ) - (orientation A hA : ℍ)‖ ^ 2 ∂tiltLaw β A) ≤
      3 / (2 * β * ‖A‖) := by
  rw [distance_orientation_integral]
  have hr : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have h := axis_concentration (κ := 2 * β * ‖A‖) (by positivity)
  calc
    _ ≤ 2 * (3 / (2 * (2 * β * ‖A‖))) := by linarith
    _ = _ := by ring

/-- Distinct orientation fibers become distinguishable with inverse-beta error. -/
theorem tilt_separation (β : ℝ) (hβ : 0 < β) (A B : ℍ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hab : orientation A hA ≠ orientation B hB) :
    1 - (3 / ‖A‖ + 3 / ‖B‖) /
      (β * ‖(orientation A hA : ℍ) - (orientation B hB : ℍ)‖ ^ 2) ≤
      (∫ q, separator _ _ hab q ∂tiltLaw β A) -
        (∫ q, separator _ _ hab q ∂tiltLaw β B) := by
  letI := tiltLaw_probability β A
  letI := tiltLaw_probability β B
  have h := integral_separation _ _ hab (tiltLaw β A) (tiltLaw β B) _ _
    (orientation_distance_bound β hβ A hA) (orientation_distance_bound β hβ B hB)
  convert h using 1
  ring

end
end UnifiedTheory.Clay.YangMills.SU2HaarSeparation

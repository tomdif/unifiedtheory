/- Actual unit-quaternion Haar response to an arbitrary linear tilt.
Haar inversion removes the transverse response and left translation orients
the source. Positivity, normalized Gibbs expectations, and the zero-source
case are proved. The one-axis excess remains its actual Haar integral;
no semicircle-density identity, Gamma approximation, or continuum limit is
assumed in this module. -/
import UnifiedTheory.Clay.YangMills.SU2QuaternionEquivalence
import UnifiedTheory.Clay.YangMills.CompactGibbsContinuity
import Mathlib.MeasureTheory.Group.Integral
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SU2HaarTilt
noncomputable section
open MeasureTheory RegulatedGauge SU2QuaternionEquivalence
open scoped Quaternion RealInnerProductSpace

local instance haar_isHaar : (compactHaar UnitQuaternion).IsHaarMeasure := by
  unfold compactHaar
  infer_instance

abbrev haar : Measure UnitQuaternion := compactHaar UnitQuaternion

/-- Compact Haar inversion invariance follows from right invariance and
normalized Haar uniqueness, including this noncommutative group. -/
local instance haar_inv : haar.IsInvInvariant := by
  letI : IsProbabilityMeasure haar.inv :=
    Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  constructor
  exact ((Measure.haarMeasure_eq_iff (⊤ : TopologicalSpace.PositiveCompacts UnitQuaternion)
    haar.inv).2 (by simp)).symm

def axisWeight (κ : ℝ) (q : UnitQuaternion) : ℝ := Real.exp (κ * (q : ℍ).re)
def axisPartition (κ : ℝ) : ℝ := ∫ q, axisWeight κ q ∂haar
def axisNumerator (κ : ℝ) : ℝ := ∫ q, axisWeight κ q * (q : ℍ).re ∂haar
def axisMean (κ : ℝ) : ℝ := axisNumerator κ / axisPartition κ
/-- Actual one-axis Haar expectation of `κ(1-re q)`. -/
def axisExcess (κ : ℝ) : ℝ :=
  (∫ q, axisWeight κ q * (κ * (1-(q : ℍ).re)) ∂haar) / axisPartition κ

/-- The Wilson convention uses exponent `2β inner(q,A)`. -/
def tiltWeight (β : ℝ) (A : ℍ) (q : UnitQuaternion) : ℝ :=
  Real.exp (2 * β * ⟪(q : ℍ), A⟫)
def tiltPartition (β : ℝ) (A : ℍ) : ℝ := ∫ q, tiltWeight β A q ∂haar
def tiltNumerator (β : ℝ) (A B : ℍ) : ℝ :=
  ∫ q, tiltWeight β A q * ⟪(q : ℍ), B⟫ ∂haar
def tiltMean (β : ℝ) (A B : ℍ) : ℝ := tiltNumerator β A B / tiltPartition β A

theorem axisWeight_continuous (κ : ℝ) : Continuous (axisWeight κ) :=
  Real.continuous_exp.comp
    (continuous_const.mul (Quaternion.continuous_re.comp continuous_subtype_val))

theorem tiltWeight_continuous (β : ℝ) (A : ℍ) : Continuous (tiltWeight β A) :=
  Real.continuous_exp.comp
    (continuous_const.mul (continuous_subtype_val.inner continuous_const))

theorem axisPartition_pos (κ : ℝ) : 0 < axisPartition κ :=
  integral_exp_pos ((axisWeight_continuous κ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))

theorem tiltPartition_pos (β : ℝ) (A : ℍ) : 0 < tiltPartition β A :=
  integral_exp_pos ((tiltWeight_continuous β A).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))

theorem real_mul_comm (a b : ℍ) : (a * b).re = (b * a).re := by
  simp only [Quaternion.re_mul]
  ring

theorem inner_left_rotation (a q B : ℍ) : ⟪a * q, B⟫ = ⟪q, star a * B⟫ := by
  simp only [Quaternion.inner_def, star_mul, star_star]
  rw [mul_assoc, real_mul_comm a (q * star B), mul_assoc]

theorem inner_star_sum (q B : ℍ) : ⟪q, B⟫ + ⟪star q, B⟫ = 2 * q.re * B.re := by
  simp only [Quaternion.inner_def, Quaternion.re_mul, Quaternion.re_star,
    Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  ring

/-- Haar inversion fixes the axis weight and cancels all transverse
components, without a coordinate-density assumption. -/
theorem axis_inner_integral (κ : ℝ) (B : ℍ) :
    (∫ q : UnitQuaternion, axisWeight κ q * ⟪(q : ℍ), B⟫ ∂haar) =
      B.re * axisNumerator κ := by
  let F : UnitQuaternion → ℝ := fun q => axisWeight κ q * ⟪(q : ℍ), B⟫
  have hi : Integrable F haar :=
    ((axisWeight_continuous κ).mul
      (continuous_subtype_val.inner continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hinv := integral_inv_eq_self (μ := haar) F
  have hsum : (∫ q : UnitQuaternion, F q + F q⁻¹ ∂haar) =
      2 * (B.re * axisNumerator κ) := by
    have he : (fun q : UnitQuaternion => F q + F q⁻¹) =
        (fun q : UnitQuaternion => (2 * B.re) * (axisWeight κ q * (q : ℍ).re)) := by
      funext q
      change axisWeight κ q * ⟪(q : ℍ), B⟫ +
        axisWeight κ q⁻¹ * ⟪((q⁻¹ : UnitQuaternion) : ℍ), B⟫ = _
      have hr : axisWeight κ q⁻¹ = axisWeight κ q := by
        change Real.exp (κ * (star (q : ℍ)).re) = _
        simp only [Quaternion.re_star]
        rfl
      rw [hr, ← mul_add]
      change axisWeight κ q * (⟪(q : ℍ), B⟫ + ⟪star (q : ℍ), B⟫) = _
      rw [inner_star_sum]
      ring
    rw [he, integral_const_mul]
    unfold axisNumerator
    ring
  rw [integral_add hi hi.comp_inv, hinv] at hsum
  dsimp [F] at hsum
  linarith

/-- Explicit unit quaternion orienting a nonzero source. -/
def orientation (A : ℍ) (hA : A ≠ 0) : UnitQuaternion :=
  ⟨‖A‖⁻¹ • A, by
    have hn : ‖‖A‖⁻¹ • A‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg A)]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hA)
    have hs : Quaternion.normSq (‖A‖⁻¹ • A) = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, hn]
      norm_num
    constructor
    · rw [Quaternion.star_mul_self, hs]; rfl
    · rw [Quaternion.self_mul_star, hs]; rfl⟩

theorem orientation_decomposition (A : ℍ) (hA : A ≠ 0) :
    A = ‖A‖ • (orientation A hA : ℍ) := by
  change A = ‖A‖ • (‖A‖⁻¹ • A)
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hA), one_smul]

theorem orientation_inner (A B : ℍ) (hA : A ≠ 0) :
    ⟪(orientation A hA : ℍ), B⟫ = ⟪A, B⟫ / ‖A‖ := by
  change ⟪‖A‖⁻¹ • A, B⟫ = _
  rw [real_inner_smul_left]
  ring

theorem oriented_inner (A : ℍ) (hA : A ≠ 0) (q : UnitQuaternion) :
    ⟪((orientation A hA * q : UnitQuaternion) : ℍ), A⟫ = ‖A‖ * (q : ℍ).re := by
  change ⟪(orientation A hA : ℍ) * (q : ℍ), A⟫ = _
  rw [inner_left_rotation]
  have hprod : star (orientation A hA : ℍ) * A = ‖A‖ • (1 : ℍ) := by
    calc
      _ = star (orientation A hA : ℍ) * (‖A‖ • (orientation A hA : ℍ)) :=
        congrArg (fun z : ℍ => star (orientation A hA : ℍ) * z) (orientation_decomposition A hA)
      _ = _ := by rw [mul_smul_comm, Unitary.coe_star_mul_self]
  rw [hprod]
  simp only [real_inner_smul_right, Quaternion.inner_def, star_one, mul_one]

theorem rotated_real (a : UnitQuaternion) (B : ℍ) :
    (star (a : ℍ) * B).re = ⟪(a : ℍ), B⟫ := by
  rw [real_mul_comm, ← Quaternion.inner_def, real_inner_comm]

theorem tiltPartition_eq_axis (β : ℝ) (A : ℍ) (hA : A ≠ 0) :
    tiltPartition β A = axisPartition (2 * β * ‖A‖) := by
  calc
    _ = ∫ q : UnitQuaternion, tiltWeight β A (orientation A hA * q) ∂haar :=
      (integral_mul_left_eq_self (tiltWeight β A) (orientation A hA)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with q
      unfold tiltWeight axisWeight
      rw [oriented_inner]
      congr 1
      ring

theorem tiltNumerator_eq_axis (β : ℝ) (A B : ℍ) (hA : A ≠ 0) :
    tiltNumerator β A B = (⟪A, B⟫ / ‖A‖) * axisNumerator (2 * β * ‖A‖) := by
  calc
    _ = ∫ q : UnitQuaternion, tiltWeight β A (orientation A hA * q) *
        ⟪((orientation A hA * q : UnitQuaternion) : ℍ), B⟫ ∂haar :=
      (integral_mul_left_eq_self
        (fun q : UnitQuaternion => tiltWeight β A q * ⟪(q : ℍ), B⟫) (orientation A hA)).symm
    _ = ∫ q : UnitQuaternion, axisWeight (2 * β * ‖A‖) q *
        ⟪(q : ℍ), star (orientation A hA : ℍ) * B⟫ ∂haar := by
      apply integral_congr_ae
      filter_upwards with q
      change tiltWeight β A (orientation A hA * q) *
        ⟪(orientation A hA : ℍ) * (q : ℍ), B⟫ = _
      rw [inner_left_rotation]
      congr 1
      unfold tiltWeight axisWeight
      rw [oriented_inner]
      congr 1
      ring
    _ = _ := by rw [axis_inner_integral, rotated_real, orientation_inner]

/-- The zero-source response vanishes by antipodal left invariance. -/
theorem unweighted_inner_zero (B : ℍ) :
    (∫ q : UnitQuaternion, ⟪(q : ℍ), B⟫ ∂haar) = 0 := by
  apply integral_eq_zero_of_mul_left_eq_neg (g := (-1 : UnitQuaternion))
  intro q
  simp only [neg_one_mul, Unitary.coe_neg, inner_neg_left]

theorem tiltNumerator_zero (β : ℝ) (B : ℍ) : tiltNumerator β 0 B = 0 := by
  simpa only [tiltNumerator, tiltWeight, inner_zero_right, mul_zero, Real.exp_zero, one_mul]
    using unweighted_inner_zero B

theorem tiltMean_zero (β : ℝ) (B : ℍ) : tiltMean β 0 B = 0 := by
  simp only [tiltMean, tiltNumerator_zero, zero_div]

/-- The actual normalized Haar response is parallel to the source. At
`A=0` both sides are zero, as proved separately by antipodal symmetry. -/
theorem tiltMean_rotational (β : ℝ) (A B : ℍ) :
    tiltMean β A B = axisMean (2 * β * ‖A‖) * ⟪A, B⟫ / ‖A‖ := by
  by_cases hA : A = 0
  · subst A
    simp [tiltMean_zero]
  · rw [tiltMean, tiltNumerator_eq_axis β A B hA, tiltPartition_eq_axis β A hA]
    unfold axisMean
    ring

theorem axisExcess_identity (κ : ℝ) : axisExcess κ = κ * (1-axisMean κ) := by
  have hi : Integrable (axisWeight κ) haar :=
    (axisWeight_continuous κ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hir : Integrable (fun q : UnitQuaternion => axisWeight κ q * (q : ℍ).re) haar :=
    ((axisWeight_continuous κ).mul
      (Quaternion.continuous_re.comp continuous_subtype_val)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have he : (fun q : UnitQuaternion => axisWeight κ q * (κ * (1-(q : ℍ).re))) =
      (fun q : UnitQuaternion => κ * axisWeight κ q-κ * (axisWeight κ q * (q : ℍ).re)) := by
    funext q
    ring
  unfold axisExcess
  rw [he, integral_sub (hi.const_mul κ) (hir.const_mul κ), integral_const_mul,
    integral_const_mul]
  change (κ * axisPartition κ-κ * axisNumerator κ) / axisPartition κ = _
  unfold axisMean
  field_simp [(axisPartition_pos κ).ne']

@[simp] theorem axisExcess_zero : axisExcess 0 = 0 := by
  rw [axisExcess_identity, zero_mul]

theorem axisMean_eq_excess (κ : ℝ) (hκ : κ ≠ 0) :
    axisMean κ = 1-axisExcess κ / κ := by
  rw [axisExcess_identity]
  field_simp
  ring

/-- Exact excess form, with `κ=2β‖A‖` and no asymptotic coefficient. -/
theorem tiltMean_excess (β : ℝ) (hβ : β ≠ 0) (A B : ℍ) (hA : A ≠ 0) :
    tiltMean β A B =
      (1-axisExcess (2 * β * ‖A‖) / (2 * β * ‖A‖)) * ⟪A, B⟫ / ‖A‖ := by
  rw [tiltMean_rotational, axisMean_eq_excess _
    (mul_ne_zero (mul_ne_zero (by norm_num) hβ) (norm_ne_zero_iff.mpr hA))]

/-- The actual probability with density proportional to the Haar tilt. -/
def tiltLaw (β : ℝ) (A : ℍ) : Measure UnitQuaternion :=
  LocalGibbsComparison.weightedLaw haar (tiltWeight β A)

theorem tiltLaw_probability (β : ℝ) (A : ℍ) : IsProbabilityMeasure (tiltLaw β A) :=
  LocalGibbsComparison.weightedLaw_probability haar _ (tiltWeight_continuous β A).measurable
    ((tiltWeight_continuous β A).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (fun _ => (Real.exp_pos _).le)
    (tiltPartition_pos β A)

theorem tiltLaw_inner_mean (β : ℝ) (A B : ℍ) :
    (∫ q : UnitQuaternion, ⟪(q : ℍ), B⟫ ∂tiltLaw β A) = tiltMean β A B :=
  LocalGibbsComparison.weighted_integral haar _ (tiltWeight_continuous β A).measurable
    (fun _ => (Real.exp_pos _).le) (tiltPartition_pos β A) _

/-- The rotational formula as an expectation under the constructed Gibbs law. -/
theorem tiltLaw_rotational (β : ℝ) (A B : ℍ) :
    (∫ q : UnitQuaternion, ⟪(q : ℍ), B⟫ ∂tiltLaw β A) =
      axisMean (2 * β * ‖A‖) * ⟪A, B⟫ / ‖A‖ := by
  rw [tiltLaw_inner_mean, tiltMean_rotational]

@[simp] theorem axisPartition_zero : axisPartition 0 = 1 := by
  simp [axisPartition, axisWeight]

@[simp] theorem axisNumerator_zero : axisNumerator 0 = 0 := by
  simpa [axisNumerator, axisWeight, Quaternion.inner_def] using unweighted_inner_zero (1 : ℍ)

@[simp] theorem axisMean_zero : axisMean 0 = 0 := by
  simp [axisMean]

theorem tiltPartition_radial (β : ℝ) (A : ℍ) :
    tiltPartition β A = axisPartition (2 * β * ‖A‖) := by
  by_cases hA : A = 0
  · subst A
    simp [tiltPartition, tiltWeight]
  · exact tiltPartition_eq_axis β A hA

theorem haar_inv_preserving : MeasurePreserving (Inv.inv : UnitQuaternion → UnitQuaternion)
    haar haar := Measure.measurePreserving_inv haar

end
end UnifiedTheory.Clay.YangMills.SU2HaarTilt

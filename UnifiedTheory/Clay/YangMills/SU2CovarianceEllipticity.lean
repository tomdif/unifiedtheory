/- Full-direction ellipticity of the actual normalized SU(2) Haar tilt.
The radial and tangent channels are separated by exact covariance identities.
This is a local conditional estimate, not a nonzero retained continuum signal. -/
import UnifiedTheory.Clay.YangMills.SU2RadialCovarianceLower
import UnifiedTheory.Clay.YangMills.SU2ConditionalInfluence

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SU2CovarianceEllipticity
noncomputable section
open MeasureTheory SU2QuaternionEquivalence SU2HaarTilt SU2InducedAction
open SU2HaarCovariance SU2WeightedRadial SU2RadialCovarianceLower SU2ConditionalInfluence
open scoped Quaternion RealInnerProductSpace

theorem mean_add (β : ℝ) (A B C : ℍ) :
    tiltMean β A (B + C) = tiltMean β A B + tiltMean β A C := by
  simp only [tiltMean_rotational, inner_add_right]
  ring

theorem covariance_symm (β : ℝ) (A B C : ℍ) : covariance β A B C = covariance β A C B := by
  unfold covariance
  simp only [mul_comm]

theorem covariance_add_left (β : ℝ) (A B C D : ℍ) :
    covariance β A (B + C) D = covariance β A B D + covariance β A C D := by
  letI := tiltLaw_probability β A
  have hi (E : ℍ) : Integrable (fun q : UnitQuaternion => ⟪(q : ℍ), E⟫ * ⟪(q : ℍ), D⟫)
      (tiltLaw β A) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)
  simp only [covariance, inner_add_right, add_mul, mean_add]
  rw [integral_add (hi B) (hi C)]
  ring

theorem covariance_add_right (β : ℝ) (A B C D : ℍ) :
    covariance β A B (C + D) = covariance β A B C + covariance β A B D := by
  rw [covariance_symm β A B (C + D), covariance_add_left,
    covariance_symm β A C B, covariance_symm β A D B]

theorem covariance_smul_left (β : ℝ) (A B C : ℍ) (c : ℝ) :
    covariance β A (c • B) C = c * covariance β A B C := by
  unfold covariance
  simp only [real_inner_smul_right, mean_smul, mul_assoc]
  rw [integral_const_mul]
  ring

theorem covariance_add_self (β : ℝ) (A B C : ℍ) :
    covariance β A (B + C) (B + C) =
      covariance β A B B + 2 * covariance β A B C + covariance β A C C := by
  rw [covariance_add_left, covariance_add_right, covariance_add_right,
    covariance_symm β A C B]
  ring

/-- Exact tangent covariance, derived from two derivatives of the same actual mean. -/
theorem perpendicular_covariance (β : ℝ) (A B : ℍ)
    (hA : A ≠ 0) (hperp : ⟪A, B⟫ = 0) :
    (2 * β * ‖A‖) * covariance β A B B =
      axisMean (2 * β * ‖A‖) * ‖B‖ ^ 2 := by
  have hp : HasDerivAt (fun t : ℝ => A + t • B) B 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const B).const_add A
  have h1 := mean_direction_hasDerivAt β A B B 0
  have h2 := mean_path_perpendicular β (fun t => A + t • B) B B 0 hp
    (by simpa using hA) (by simpa using hperp)
  have he := h1.unique h2
  simp only [zero_smul, add_zero, real_inner_self_eq_norm_sq] at he
  have hr := norm_ne_zero_iff.mpr hA
  have hh := (eq_div_iff hr).mp he
  nlinarith

/-- Radial and tangent fluctuations are exactly uncorrelated under the tilted law. -/
theorem radial_perpendicular_zero (β : ℝ) (A B : ℍ)
    (hβ : β ≠ 0) (hA : A ≠ 0) (hperp : ⟪A, B⟫ = 0) :
    covariance β A A B = 0 := by
  have hp : HasDerivAt (fun t : ℝ => A + t • A) A 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const A).const_add A
  have h1 := mean_direction_hasDerivAt β A A B 0
  have h2 := mean_path_perpendicular β (fun t => A + t • A) B A 0 hp
    (by simpa using hA) (by simpa using hperp)
  have he := h1.unique h2
  simp only [zero_smul, add_zero, hperp, mul_zero, zero_div] at he
  rw [covariance_symm β A B A] at he
  exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) hβ)

/-- The tangent channel also dominates an inverse-square floor at large tilt. -/
theorem perpendicular_lower (β : ℝ) (A B : ℍ)
    (hκ : 50 ≤ 2 * β * ‖A‖) (hperp : ⟪A, B⟫ = 0) :
    (3 / 4 : ℝ) * ‖B‖ ^ 2 ≤ (2 * β * ‖A‖) ^ 2 * covariance β A B B := by
  have hA : A ≠ 0 := by intro h; simp only [h, norm_zero, mul_zero] at hκ; linarith
  have hk : 0 < 2 * β * ‖A‖ := by linarith
  have hc := axis_concentration hk
  have hm : 3 / 4 ≤ (2 * β * ‖A‖) * axisMean (2 * β * ‖A‖) := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (2 * β * ‖A‖))).mp hc
    nlinarith
  have ht := perpendicular_covariance β A B hA hperp
  calc
    _ ≤ ((2 * β * ‖A‖) * axisMean (2 * β * ‖A‖)) * ‖B‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hm (sq_nonneg _)
    _ = (2 * β * ‖A‖) * ((2 * β * ‖A‖) * covariance β A B B) := by rw [ht]; ring
    _ = _ := by ring

/-- Actual covariance ellipticity in every quaternion probe direction. -/
theorem covariance_lower (β : ℝ) (A B : ℍ) (hκ : 50 ≤ 2 * β * ‖A‖) :
    (3 / 4 : ℝ) * ‖B‖ ^ 2 ≤ (2 * β * ‖A‖) ^ 2 * covariance β A B B := by
  have hA : A ≠ 0 := by intro h; simp only [h, norm_zero, mul_zero] at hκ; linarith
  have hβ : β ≠ 0 := by intro h; simp only [h, mul_zero, zero_mul] at hκ; linarith
  have hr : ‖A‖ ≠ 0 := norm_ne_zero_iff.mpr hA
  let c : ℝ := ⟪A, B⟫ / ‖A‖ ^ 2
  let P : ℍ := c • A
  let D : ℍ := B - P
  have hperp : ⟪A, D⟫ = 0 := by
    dsimp only [D, P, c]
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    ring
  have hPD : ⟪P, D⟫ = 0 := by
    dsimp only [P]
    rw [real_inner_smul_left, hperp, mul_zero]
  have hsum : P + D = B := by dsimp only [D]; abel
  have hnorm := norm_add_sq_real P D
  rw [hsum, hPD, mul_zero, add_zero] at hnorm
  have hpnorm : ‖P‖ ^ 2 = c ^ 2 * ‖A‖ ^ 2 := by
    simp only [P, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hrad := covariance_radial_lower β A A hκ
  have hradproj : (⟪A, A⟫ / ‖A‖) ^ 2 = ‖A‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
    field_simp
  rw [hradproj] at hrad
  have hrad' := mul_le_mul_of_nonneg_left hrad (sq_nonneg c)
  have htan := perpendicular_lower β A D hκ hperp
  have hcross : covariance β A P D = 0 := by
    change covariance β A (c • A) D = 0
    rw [covariance_smul_left, radial_perpendicular_zero β A D hβ hA hperp, mul_zero]
  have hcov := covariance_add_self β A P D
  rw [hsum, hcross, mul_zero, add_zero] at hcov
  dsimp only [P] at hcov
  rw [covariance_smul] at hcov
  rw [hnorm, hpnorm, hcov]
  nlinarith

/-- A positive numerical constant for a bound valid through zero tilt. -/
def floorConstant : ℝ := Real.exp (-100) / 4

theorem floorConstant_pos : 0 < floorConstant := by unfold floorConstant; positivity

theorem floorConstant_le : floorConstant ≤ 3 / 4 := by
  have h := Real.exp_le_one_iff.mpr (by norm_num : (-100 : ℝ) ≤ 0)
  unfold floorConstant
  linarith

/-- Direct Haar comparison supplies the bounded-tilt region, including A=0. -/
theorem covariance_exponential_lower (β : ℝ) (A B : ℍ) (hβ : 0 ≤ β) :
    Real.exp (-(2 * (2 * β * ‖A‖))) * (‖B‖ ^ 2 / 4) ≤ covariance β A B B := by
  let κ : ℝ := 2 * β * ‖A‖
  let m : ℝ := tiltMean β A B
  let f : UnitQuaternion → ℝ := fun q => (⟪(q : ℍ), B⟫ - m) ^ 2
  have hf : Continuous f := by dsimp only [f]; fun_prop
  have hfi : Integrable f haar :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hw : Integrable (tiltWeight β A) haar :=
    (tiltWeight_continuous β A).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hwf : Integrable (fun q => tiltWeight β A q * f q) haar :=
    ((tiltWeight_continuous β A).mul hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb (q : UnitQuaternion) : Real.exp (-κ) ≤ tiltWeight β A q ∧
      tiltWeight β A q ≤ Real.exp κ := by
    have hi := abs_real_inner_le_norm (q : ℍ) A
    rw [CStarRing.norm_coe_unitary q, one_mul] at hi
    have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * β by positivity)
    have ha := abs_le.mp hi
    constructor <;> apply Real.exp_le_exp.mpr
    · dsimp only [κ]
      nlinarith
    · dsimp only [κ]
      nlinarith
  have hz : tiltPartition β A ≤ Real.exp κ := by
    have h := integral_mono hw (integrable_const (Real.exp κ)) (fun q => (hb q).2)
    simpa only [tiltPartition, integral_const, Measure.real, measure_univ,
      ENNReal.toReal_one, one_smul] using h
  have hn : Real.exp (-κ) * (∫ q, f q ∂haar) ≤
      ∫ q, tiltWeight β A q * f q ∂haar := by
    rw [← integral_const_mul]
    exact integral_mono (hfi.const_mul _) hwf
      (fun q => mul_le_mul_of_nonneg_right (hb q).1 (sq_nonneg _))
  have hv := covariance_le_square_deviation 0 0 B m
  rw [covariance_zero, tiltLaw_zero] at hv
  change ‖B‖ ^ 2 / 4 ≤ ∫ q, f q ∂haar at hv
  rw [covariance_centered, tiltLaw_integral]
  apply (le_div_iff₀ (tiltPartition_pos β A)).mpr
  change (Real.exp (-(2 * κ)) * (‖B‖ ^ 2 / 4)) * tiltPartition β A ≤ _
  calc
    _ ≤ (Real.exp (-(2 * κ)) * (‖B‖ ^ 2 / 4)) * Real.exp κ :=
      mul_le_mul_of_nonneg_left hz (by positivity)
    _ = Real.exp (-κ) * (‖B‖ ^ 2 / 4) := by
      have he : Real.exp (-(2 * κ)) * Real.exp κ = Real.exp (-κ) := by
        rw [← Real.exp_add]
        congr 1
        ring
      nlinarith [he]
    _ ≤ Real.exp (-κ) * (∫ q, f q ∂haar) :=
      mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
    _ ≤ _ := hn

/-- All-direction polynomial ellipticity under every nonnegative actual Haar tilt. -/
theorem covariance_global_lower (β : ℝ) (A B : ℍ) (hβ : 0 ≤ β) :
    floorConstant * ‖B‖ ^ 2 ≤ (1 + 2 * β * ‖A‖) ^ 2 * covariance β A B B := by
  have hk : 0 ≤ 2 * β * ‖A‖ := by positivity
  have hv := covariance_self_nonneg β A B
  by_cases hlarge : 50 ≤ 2 * β * ‖A‖
  · calc
      _ ≤ (3 / 4 : ℝ) * ‖B‖ ^ 2 :=
        mul_le_mul_of_nonneg_right floorConstant_le (sq_nonneg _)
      _ ≤ (2 * β * ‖A‖) ^ 2 * covariance β A B B := covariance_lower β A B hlarge
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith) hv
  · have hsmall : 2 * β * ‖A‖ ≤ 50 := le_of_lt (lt_of_not_ge hlarge)
    have he : Real.exp (-100) ≤ Real.exp (-(2 * (2 * β * ‖A‖))) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      _ = Real.exp (-100) * (‖B‖ ^ 2 / 4) := by unfold floorConstant; ring
      _ ≤ Real.exp (-(2 * (2 * β * ‖A‖))) * (‖B‖ ^ 2 / 4) :=
        mul_le_mul_of_nonneg_right he (by positivity)
      _ ≤ covariance β A B B := covariance_exponential_lower β A B hβ
      _ ≤ _ := by nlinarith [mul_nonneg hv (sq_nonneg (2 * β * ‖A‖))]

/-- The actual Wilson staple norm bound makes the estimate independent of the exterior. -/
theorem covariance_six_lower (β : ℝ) (A B : ℍ) (hβ : 0 ≤ β) (hA : ‖A‖ ≤ 6) :
    floorConstant * ‖B‖ ^ 2 ≤ (1 + 12 * β) ^ 2 * covariance β A B B := by
  have hκ : 2 * β * ‖A‖ ≤ 12 * β := by nlinarith
  exact (covariance_global_lower β A B hβ).trans
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by linarith) 2) (covariance_self_nonneg β A B))

open RegulatedGauge PeriodicLattice4 WilsonUniformVariance WilsonSingleLinkStaples
variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- The global lower bound is bound to the literal interacting Wilson conditional source.
The weighted staple can vanish, so this is not a lower bound on a physical smeared field. -/
theorem wilson_conditional_source_lower (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (hβ : 0 ≤ β) (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) :
    Real.exp (-100) * ‖exteriorWeightedStaple n x μ r f‖ ^ 2 ≤
      (1 + 12 * β) ^ 2 *
        (∫ q : Q, (SU2WilsonConditionalSource.splitSource n x μ f (r, q) -
          SU2WilsonConditionalSource.conditionalSource n x μ β f r) ^ 2
          ∂SU2WilsonConditionalSource.conditionalLaw n x μ β r) := by
  rw [conditional_source_variance]
  have h := mul_le_mul_of_nonneg_left
    (covariance_six_lower β (exteriorStaple n x μ r) (exteriorWeightedStaple n x μ r f)
      hβ (exteriorStaple_norm_le_six n x μ r)) (by norm_num : (0 : ℝ) ≤ 4)
  unfold floorConstant at h
  convert h using 1 <;> ring

end
end UnifiedTheory.Clay.YangMills.SU2CovarianceEllipticity

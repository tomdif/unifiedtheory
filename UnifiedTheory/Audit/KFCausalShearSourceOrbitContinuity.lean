/- Joint L2 continuity of polynomial-weighted shear paths and their first
outputs along a continuous source orbit of fixed source norm. A single
Gaussian majorant controls both parameters, including their endpoints. -/
import UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalShearSourceOrbitContinuity
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (sourceSize sourceConstant)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds
open UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation
open UnifiedTheory.Audit.KFCausalGaussianSecondShearBounds (firstEnvelope scaleBound first_path_bound)
open UnifiedTheory.Audit.KFCausalGaussianSecondShearDifferential (first)
open UnifiedTheory.Audit.KFCausalGaussianShearSlopeBounds (slopeConstant)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve
open UnifiedTheory.Audit.KFCausalShearRadius (radius radius_positive)
open UnifiedTheory.Audit.KFCausalIntervalL2Derivative (clip)

theorem source_coordinate_bound (b : Fin 5 → ℂ) (i : Fin 5) :
    ‖b i‖ ≤ 1+sourceSize b := by
  have hs : ‖b i‖^2 ≤ sourceSize b :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖b j‖) (Finset.mem_univ i)
  nlinarith [sq_nonneg (‖b i‖-1)]

def slopeCap (M α β : ℝ) (b : Fin 5 → ℂ) : ℝ :=
  slopeConstant M α β (fun _ => (1+sourceSize b:ℝ))

theorem slope_le_cap (M α β : ℝ) (hM : 0 ≤ M) (b c : Fin 5 → ℂ)
    (he : sourceSize b = sourceSize c) : slopeConstant M α β b ≤ slopeCap M α β c := by
  have hs : 0 ≤ sourceSize c := Finset.sum_nonneg (fun i _ => sq_nonneg ‖c i‖)
  unfold slopeCap slopeConstant
  apply Finset.sum_le_sum
  intro i _
  have hi := source_coordinate_bound b i
  rw [he] at hi
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ 1+sourceSize c)]
  have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2*M by positivity)
  linarith only [hm]

theorem envelope_source_eq (A : ℝ → ℂ) (α β : ℝ) (b c : Fin 5 → ℂ)
    (he : sourceSize b = sourceSize c) : envelope A α β b = envelope A α β c := by
  unfold KFCausalImaginaryShearPathBounds.envelope KFCausalImaginaryShearPathBounds.constant
    KFCausalClockFloorCoherentBounds.sourceConstant
  rw [he]

theorem first_envelope_bound (A : ℝ → ℂ) (α β : ℝ) (b c : Fin 5 → ℂ)
    (he : sourceSize b = sourceSize c) (x : Configuration) :
    ‖firstEnvelope A α β b x‖ ≤
      ‖(slopeCap scaleBound α β c+1:ℝ)*((radius x.2:ℂ)*envelope A α β c x)‖ := by
  have hb := KFCausalGaussianShearSlopeBounds.slopeConstant_nonnegative
    scaleBound α β (Real.exp_pos _).le b
  have hc := KFCausalGaussianShearSlopeBounds.slopeConstant_nonnegative
    scaleBound α β (Real.exp_pos _).le (fun _ => (1+sourceSize c:ℝ))
  change 0 ≤ slopeCap scaleBound α β c at hc
  rw [firstEnvelope,envelope_source_eq A α β b c he]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ slopeConstant scaleBound α β b+1),
    abs_of_nonneg (by linarith : 0 ≤ slopeCap scaleBound α β c+1)]
  exact mul_le_mul_of_nonneg_right
    (by linarith only [slope_le_cap scaleBound α β (Real.exp_pos _).le b c he])
    (mul_nonneg (abs_nonneg _) (norm_nonneg _))

variable (P : Weight) (A D : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hAm : MemLp A 2 volume)
  (hD : ContDiff ℝ 1 D) (hDb : ∀ s, ‖D s‖ ≤ Real.pi/3)
  (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (b : ℝ → Fin 5 → ℂ) (hb : Continuous b) (c : Fin 5 → ℂ)
  (he : ∀ θ, sourceSize (b θ) = sourceSize c)

include hb he in
theorem input_joint_continuous : Continuous (fun p : ℝ × ℝ =>
    input P A D hA hAm hD hDb α β hα hβ hw (b p.2) p.1) := by
  apply KFCausalDominatedL2Continuity.continuous_toLp
    (fun p : ℝ × ℝ => fun x => P.value x*path A D α β (b p.2) (clip p.1) x)
    (fun p => input_memLp P A D hA hAm hD hDb α β hα hβ hw (b p.2) (clip p.1) (clip p.1).property)
    (fun x => P.value x*envelope A α β c x) (envelope0_memLp P A hAm α β hα hβ c)
  · intro p
    filter_upwards [] with x
    have hp := path_bound A D hDb α β hα hβ hw (b p.2) (clip p.1) (clip p.1).property x
    rw [envelope_source_eq A α β (b p.2) c (he p.2)] at hp
    simpa only [norm_mul] using mul_le_mul_of_nonneg_left hp (norm_nonneg (P.value x))
  · filter_upwards [] with x
    have ht : Continuous (fun p : ℝ × ℝ => (clip p.1:ℝ)) :=
      continuous_subtype_val.comp ((continuous_projIcc (h := zero_le_one)).comp continuous_fst)
    have hp (j : Fin 5) : Continuous (fun p : ℝ × ℝ =>
        KFCausalRelativeGaussianDifferential.position (timeScale D (clip p.1) x.1) x.2 j) := by
      unfold KFCausalRelativeGaussianDifferential.position timeScale
      split_ifs <;> fun_prop
    unfold path KFCausalRelativeGaussianDifferential.profile
      KFCausalRelativeGaussianDifferential.exponent timeAmplitude
    fun_prop

include hb he in
theorem first_joint_continuous : Continuous (fun p : ℝ × ℝ =>
    firstState P A D hA hAm hD hDb α β hα hβ hw (b p.2) p.1) := by
  let B : Configuration → ℂ := fun x =>
    (slopeCap scaleBound α β c+1:ℝ)*(P.value x*(radius x.2:ℂ)*envelope A α β c x)
  have hB : MemLp B 2 volume := by
    simpa only [B,pow_one] using
      (KFCausalFieldInterpolationBounds.weighted_envelope_memLp P.value P.smooth.continuous
        P.bound P.nonnegative P.estimate A hAm α β hα hβ c 1).const_mul
        ((slopeCap scaleBound α β c+1:ℝ):ℂ)
  apply KFCausalDominatedL2Continuity.continuous_toLp
    (fun p : ℝ × ℝ => fun x => P.value x*
      first (timeAmplitude A D (clip p.1)) (timeScale D (clip p.1)) α β (b p.2) x)
    (fun p => first_memLp P A D hA hAm hD hDb α β hα hβ hw (b p.2) (clip p.1) (clip p.1).property) B hB
  · intro p
    filter_upwards [] with x
    have hp := (first_path_bound A D hDb α β hα hβ hw (b p.2) (clip p.1) (clip p.1).property x).trans
      (first_envelope_bound A α β (b p.2) c (he p.2) x)
    simpa only [B,norm_mul,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_left hp (norm_nonneg (P.value x))
  · filter_upwards [] with x
    have ht : Continuous (fun p : ℝ × ℝ => (clip p.1:ℝ)) :=
      continuous_subtype_val.comp ((continuous_projIcc (h := zero_le_one)).comp continuous_fst)
    have hp (j : Fin 5) : Continuous (fun p : ℝ × ℝ =>
        KFCausalRelativeGaussianDifferential.position (timeScale D (clip p.1) x.1) x.2 j) := by
      unfold KFCausalRelativeGaussianDifferential.position timeScale
      split_ifs <;> fun_prop
    have hd (j : Fin 5) : Continuous (fun p : ℝ × ℝ =>
        KFCausalRelativeGaussianDifferential.direction (timeScale D (clip p.1) x.1) x.2 j) := by
      unfold KFCausalRelativeGaussianDifferential.direction timeScale
      split_ifs <;> fun_prop
    unfold first KFCausalRelativeGaussianDifferential.slope
      KFCausalRelativeGaussianDifferential.profile KFCausalRelativeGaussianDifferential.exponent
      timeAmplitude
    fun_prop

#print axioms source_coordinate_bound
#print axioms slope_le_cap
#print axioms envelope_source_eq
#print axioms first_envelope_bound
#print axioms input_joint_continuous
#print axioms first_joint_continuous
end
end UnifiedTheory.Audit.KFCausalShearSourceOrbitContinuity

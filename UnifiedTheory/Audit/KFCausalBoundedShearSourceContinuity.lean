/- Bounded continuous source orbits have continuous actual shear-path
inputs and outputs. Source norms need not be constant along the orbit. -/
import UnifiedTheory.Audit.KFCausalShearSourceOrbitContinuity
import UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalBoundedShearSourceContinuity
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
  (sourceSize sourceConstant positionConstant positionConstant_positive)
open UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation
open UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalGaussianSecondShearBounds
open UnifiedTheory.Audit.KFCausalGaussianSecondShearDifferential (first)
open UnifiedTheory.Audit.KFCausalGaussianShearSlopeBounds (slopeConstant slopeConstant_nonnegative)
open UnifiedTheory.Audit.KFCausalShearSourceOrbitContinuity (source_coordinate_bound slopeCap)
open UnifiedTheory.Audit.KFCausalShearRadius (radius)
open UnifiedTheory.Audit.KFCausalGaussianFourthMoments (radius_memLp)
open UnifiedTheory.Audit.KFCausalStrongImaginaryShearCurve (inputCurve firstCurve)
open UnifiedTheory.Audit.KFCausalIntervalL2Derivative (curve curve_value)

theorem source_cap (B : ℝ) : ∃ c : Fin 5 → ℂ, B ≤ sourceSize c := by
  refine ⟨fun _ => ((1+|B|:ℝ):ℂ),?_⟩
  have hb : 0 ≤ 1+|B| := by positivity
  simp only [sourceSize,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hb]
  nlinarith [le_abs_self B,sq_nonneg |B|,abs_nonneg B]

theorem slope_cap_bound (M α β : ℝ) (hM : 0 ≤ M) (b c : Fin 5 → ℂ)
    (he : sourceSize b ≤ sourceSize c) : slopeConstant M α β b ≤ slopeCap M α β c := by
  have hs : 0 ≤ sourceSize c := Finset.sum_nonneg (fun i _ => sq_nonneg ‖c i‖)
  unfold slopeCap slopeConstant
  apply Finset.sum_le_sum
  intro i _
  have hi : ‖b i‖ ≤ 1+sourceSize c := (source_coordinate_bound b i).trans (by linarith)
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ 1+sourceSize c)]
  nlinarith [mul_le_mul_of_nonneg_left hi (show 0 ≤ 2*M by positivity)]

theorem envelope_bound (A : ℝ → ℂ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (b c : Fin 5 → ℂ) (he : sourceSize b ≤ sourceSize c) (x : Configuration) :
    ‖envelope A α β b x‖ ≤ ‖envelope A α β c x‖ := by
  have hc : constant α β b ≤ constant α β c := by
    unfold constant
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    unfold sourceConstant
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right he (positionConstant_positive α β hα hβ).le) (by norm_num)
  have hb0 : 0 ≤ constant α β b := by unfold constant; positivity
  have hc0 : 0 ≤ constant α β c := by unfold constant; positivity
  simpa only [envelope,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb0,
    abs_of_nonneg hc0] using mul_le_mul_of_nonneg_right hc
      (norm_nonneg (A x.1*KFCausalClockFloorShearBounds.physicalGaussian (width α β) (width α β) x.2))

theorem first_envelope_bound (A : ℝ → ℂ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (b c : Fin 5 → ℂ) (he : sourceSize b ≤ sourceSize c) (x : Configuration) :
    ‖firstEnvelope A α β b x‖ ≤
      ‖((slopeCap scaleBound α β c+1:ℝ):ℂ)*((radius x.2:ℂ)*envelope A α β c x)‖ := by
  have hb := slopeConstant_nonnegative scaleBound α β (Real.exp_pos _).le b
  have hc := slopeConstant_nonnegative scaleBound α β (Real.exp_pos _).le
    (fun _ => ((1+sourceSize c:ℝ):ℂ))
  change 0 ≤ slopeCap scaleBound α β c at hc
  simp only [firstEnvelope,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ slopeConstant scaleBound α β b+1),
    abs_of_nonneg (by linarith : 0 ≤ slopeCap scaleBound α β c+1)]
  apply mul_le_mul
  · linarith [slope_cap_bound scaleBound α β (Real.exp_pos _).le b c he]
  · exact mul_le_mul_of_nonneg_left (envelope_bound A α β hα hβ b c he x) (abs_nonneg _)
  · positivity
  · positivity

variable (A D : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hAm : MemLp A 2 volume)
  (hD : ContDiff ℝ 1 D) (hDb : ∀ s, ‖D s‖ ≤ Real.pi/3)
  (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (b : ℝ → Fin 5 → ℂ) (hb : Continuous b) (B : ℝ) (hB : ∀ θ, sourceSize (b θ) ≤ B)

include hb hB in
theorem input_continuous (t : Interval) :
    Continuous (fun θ => inputCurve A D hA hAm hD hDb α β hα hβ hw (b θ) t) := by
  obtain ⟨c,hc⟩ := source_cap B
  have he (θ : ℝ) := (hB θ).trans hc
  simp only [inputCurve,curve_value _ _ t t.property]
  apply KFCausalDominatedL2Continuity.continuous_toLp
    (fun θ => path A D α β (b θ) t)
    (fun θ => path_memLp A D hA hAm hD hDb α β hα hβ hw (b θ) t t.property)
    (envelope A α β c) (envelope_memLp A hAm α β hα hβ c)
  · intro θ
    exact Filter.Eventually.of_forall (fun x =>
      (path_bound A D hDb α β hα hβ hw (b θ) t t.property x).trans
        (envelope_bound A α β hα hβ (b θ) c (he θ) x))
  · filter_upwards [] with x
    unfold path KFCausalRelativeGaussianDifferential.profile KFCausalRelativeGaussianDifferential.exponent
    fun_prop

include hb hB in
theorem first_continuous (t : Interval) :
    Continuous (fun θ => firstCurve A D hA hAm hD hDb α β hα hβ hw (b θ) t) := by
  obtain ⟨c,hc⟩ := source_cap B
  have he (θ : ℝ) := (hB θ).trans hc
  let F : Configuration → ℂ := fun x =>
    ((slopeCap scaleBound α β c+1:ℝ):ℂ)*((radius x.2:ℂ)*envelope A α β c x)
  have hF : MemLp F 2 volume := (radius_memLp _ (envelope_memLp A hAm α β hα hβ c)
    (envelope_quadratic_memLp A hAm α β hα hβ c)).const_mul _
  simp only [firstCurve,curve_value _ _ t t.property]
  apply KFCausalDominatedL2Continuity.continuous_toLp
    (fun θ => first (timeAmplitude A D t) (timeScale D t) α β (b θ))
    (fun θ => first_path_memLp A D hA hAm hD hDb α β hα hβ hw (b θ) t t.property) F hF
  · intro θ
    exact Filter.Eventually.of_forall (fun x =>
      (first_path_bound A D hDb α β hα hβ hw (b θ) t t.property x).trans
        (first_envelope_bound A α β hα hβ (b θ) c (he θ) x))
  · filter_upwards [] with x
    unfold first KFCausalRelativeGaussianDifferential.slope
      KFCausalRelativeGaussianDifferential.profile KFCausalRelativeGaussianDifferential.exponent
    fun_prop

#print axioms source_cap
#print axioms slope_cap_bound
#print axioms envelope_bound
#print axioms first_envelope_bound
#print axioms input_continuous
#print axioms first_continuous
end
end UnifiedTheory.Audit.KFCausalBoundedShearSourceContinuity

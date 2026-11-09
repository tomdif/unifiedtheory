/- Joint source/path continuity with the actual unbounded polynomial
weights. A common Gaussian envelope derives all required L2 domination. -/
import UnifiedTheory.Audit.KFCausalBoundedShearSourceContinuity
import UnifiedTheory.Audit.KFCausalActualPolynomialShearCurve

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalBoundedPolynomialShearContinuity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (sourceSize)
open UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation
open UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalGaussianSecondShearBounds
open UnifiedTheory.Audit.KFCausalGaussianSecondShearDifferential (first)
open UnifiedTheory.Audit.KFCausalBoundedShearSourceContinuity
  (source_cap envelope_bound first_envelope_bound)
open UnifiedTheory.Audit.KFCausalShearSourceOrbitContinuity (slopeCap)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve
  (Weight input firstState input_memLp first_memLp envelope0_memLp)
open UnifiedTheory.Audit.KFCausalIntervalL2Derivative (curve_value)
open UnifiedTheory.Audit.KFCausalShearRadius (radius)

variable (P : Weight) (A D : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hAm : MemLp A 2 volume)
  (hD : ContDiff ℝ 1 D) (hDb : ∀ s, ‖D s‖ ≤ Real.pi/3)
  (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (b : ℝ → Fin 5 → ℂ) (hb : Continuous b) (B : ℝ) (hB : ∀ θ, sourceSize (b θ) ≤ B)

include hb hB in
theorem input_continuous : Continuous (fun v : ℝ × Interval =>
    input P A D hA hAm hD hDb α β hα hβ hw (b v.1) v.2) := by
  obtain ⟨c,hc⟩ := source_cap B
  have he (θ : ℝ) := (hB θ).trans hc
  simp only [input,curve_value _ _ _ (Subtype.property _)]
  apply KFCausalDominatedL2Continuity.continuous_toLp
    (fun v : ℝ × Interval => fun x => P.value x*path A D α β (b v.1) v.2 x)
    (fun v => input_memLp P A D hA hAm hD hDb α β hα hβ hw (b v.1) v.2 v.2.property)
    (fun x => P.value x*envelope A α β c x) (envelope0_memLp P A hAm α β hα hβ c)
  · intro v
    filter_upwards [] with x
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((path_bound A D hDb α β hα hβ hw (b v.1) v.2 v.2.property x).trans
        (envelope_bound A α β hα hβ (b v.1) c (he v.1) x)) (norm_nonneg _)
  · filter_upwards [] with x
    have hp (i : Fin 5) : Continuous (fun v : ℝ × Interval =>
        KFCausalRelativeGaussianDifferential.position (timeScale D v.2 x.1) x.2 i) := by
      unfold KFCausalRelativeGaussianDifferential.position
      split_ifs <;> unfold timeScale <;> fun_prop
    unfold path timeAmplitude KFCausalRelativeGaussianDifferential.profile
      KFCausalRelativeGaussianDifferential.exponent
    fun_prop

include hb hB in
theorem first_continuous : Continuous (fun v : ℝ × Interval =>
    firstState P A D hA hAm hD hDb α β hα hβ hw (b v.1) v.2) := by
  obtain ⟨c,hc⟩ := source_cap B
  have he (θ : ℝ) := (hB θ).trans hc
  let F : Configuration → ℂ := fun x => P.value x*
    (((slopeCap scaleBound α β c+1:ℝ):ℂ)*((radius x.2:ℂ)*envelope A α β c x))
  have hF : MemLp F 2 volume := by
    have hm := (KFCausalFieldInterpolationBounds.weighted_envelope_memLp P.value P.smooth.continuous
      P.bound P.nonnegative P.estimate A hAm α β hα hβ c 1).const_mul
      ((slopeCap scaleBound α β c+1:ℝ):ℂ)
    convert hm using 1
    funext x
    simp only [F,pow_one]
    ring
  simp only [firstState,curve_value _ _ _ (Subtype.property _)]
  apply KFCausalDominatedL2Continuity.continuous_toLp
    (fun v : ℝ × Interval => fun x => P.value x*
      first (timeAmplitude A D v.2) (timeScale D v.2) α β (b v.1) x)
    (fun v => first_memLp P A D hA hAm hD hDb α β hα hβ hw (b v.1) v.2 v.2.property) F hF
  · intro v
    filter_upwards [] with x
    change ‖P.value x*_‖ ≤ ‖P.value x*_‖
    simp only [norm_mul]
    have he' := (first_path_bound A D hDb α β hα hβ hw (b v.1) v.2 v.2.property x).trans
      (first_envelope_bound A α β hα hβ (b v.1) c (he v.1) x)
    simpa only [norm_mul] using mul_le_mul_of_nonneg_left he' (norm_nonneg (P.value x))
  · filter_upwards [] with x
    have hp (i : Fin 5) : Continuous (fun v : ℝ × Interval =>
        KFCausalRelativeGaussianDifferential.position (timeScale D v.2 x.1) x.2 i) := by
      unfold KFCausalRelativeGaussianDifferential.position
      split_ifs <;> unfold timeScale <;> fun_prop
    have hd (i : Fin 5) : Continuous (fun v : ℝ × Interval =>
        KFCausalRelativeGaussianDifferential.direction (timeScale D v.2 x.1) x.2 i) := by
      unfold KFCausalRelativeGaussianDifferential.direction
      split_ifs <;> unfold timeScale <;> fun_prop
    unfold first timeAmplitude KFCausalRelativeGaussianDifferential.slope
      KFCausalRelativeGaussianDifferential.profile KFCausalRelativeGaussianDifferential.exponent
    fun_prop

#print axioms input_continuous
#print axioms first_continuous
end
end UnifiedTheory.Audit.KFCausalBoundedPolynomialShearContinuity

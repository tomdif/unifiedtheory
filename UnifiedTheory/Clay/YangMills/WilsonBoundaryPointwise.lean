/- One actual transfer step upgrades the proved fixed-cutoff boundary L2
limit to uniform convergence of continuous representatives. No rate uniform
in the spatial volume or coupling is used. -/
import UnifiedTheory.Clay.YangMills.WilsonCylinderVacuum
import UnifiedTheory.Clay.YangMills.WilsonTemporalGauge

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonBoundaryPointwise
noncomputable section
open MeasureTheory Filter WilsonTimeSlab WilsonSlabOperator WilsonPositiveGroundState
open WilsonBoundaryTransfer WilsonCylinderVacuum ContinuousBoundaryMoments
open WilsonGroundLocalComparison TransferEnergySurvival
open scoped Topology

variable (n : ℕ) [NeZero n]

/-- The finite boundary is the actual spatial endpoint weight throughout. -/
def boundaryMessage (β : ℝ) (j : ℕ) : C(Slice n, ℝ) :=
  message n β (spatialBoundary n β) j

theorem boundaryMessage_pos (β : ℝ) (j : ℕ) (u : Slice n) :
    0 < boundaryMessage n β j u := by
  induction j generalizing u with
  | zero => exact spatialBoundary_pos n β u
  | succ j ih =>
    rw [boundaryMessage, message_succ]
    exact PositiveKernelRatio.profile_integral_pos (measure n)
      ⟨fun v => kernelMap n β (u,v)*boundaryMessage n β j v,
        ((kernelMap n β).continuous.comp (continuous_const.prodMk continuous_id)).mul
          (boundaryMessage n β j).continuous⟩
      (fun v => mul_pos (kernel_positive _ WilsonSingleLinkStaples.character_continuous
        β 2 u v) (ih v))

theorem boundaryMessage_gauge (β : ℝ) (j : ℕ) (h : SliceGauge n Q) (u : Slice n) :
    boundaryMessage n β j (gaugeSlice h u) = boundaryMessage n β j u := by
  cases j with
  | zero =>
    exact WilsonSlabGauge.spatialWeight_gauge _
      WilsonSingleLinkStaples.character_classFunction β 2 h u
  | succ j =>
    change (representative n β (embed (measure n) (boundaryMessage n β j))
      (gaugeSlice h u)).re = (representative n β
        (embed (measure n) (boundaryMessage n β j)) u).re
    rw [representative_gauge]

/-- Gauge averaging is removed only against the proved invariant message. -/
theorem boundaryMessage_raw_succ (β : ℝ) (j : ℕ) (u : Slice n) :
    boundaryMessage n β (j+1) u =
      ∫ v, WilsonTemporalGauge.rawKernel WilsonSingleLinkStaples.character β 2 u v*
        boundaryMessage n β j v ∂measure n := by
  rw [boundaryMessage, message_succ]
  exact WilsonTemporalGauge.invariant_integral _ WilsonSingleLinkStaples.character_continuous
    WilsonSingleLinkStaples.character_classFunction β 2 (boundaryMessage n β j)
    (boundaryMessage n β j).continuous (boundaryMessage_gauge n β j) u

theorem scaledMessage_succ (β : ℝ) (j : ℕ) :
    scaledMessage n β (j+1) = ‖transfer n β‖⁻¹ •
      realSmoothing (measure n) (kernelMap n β) (scaledMessage n β j) := by
  ext u
  simp only [scaledMessage, ContinuousMap.smul_apply, smul_eq_mul, message_succ,
    realSmoothing_integral]
  have he (v : Slice n) : kernelMap n β (u,v)*
      ((‖transfer n β‖⁻¹)^j*message n β (spatialBoundary n β) j v) =
      (‖transfer n β‖⁻¹)^j*(kernelMap n β (u,v)*message n β (spatialBoundary n β) j v) := by ring
  simp_rw [he]
  rw [integral_const_mul, pow_succ]
  ring

theorem smoothing_ground (β : ℝ) (hβ : 0 ≤ β) :
    CompactKernelOperator.smoothingOperator (measure n) (kernelMap n β)
      (WilsonVacuumConvergence.vacuum n β hβ) =
        (‖transfer n β‖ : ℂ) • complexify (ground n β hβ) := by
  ext u
  change CompactKernelOperator.smoothing (measure n) (kernelMap n β)
    (ContinuousMap.toLp 2 (measure n) ℂ (complexify (ground n β hβ))) u = _
  rw [CompactKernelOperator.smoothing_continuous_input]
  simp only [complexify, ContinuousMap.coe_mk, ContinuousMap.smul_apply, smul_eq_mul,
    ← Complex.ofReal_mul, integral_complex_ofReal]
  exact congrArg (fun r : ℝ => (r : ℂ)) (ground_equation n β hβ u)

/-- This is convergence in the continuous-function norm, after one smoothing step. -/
theorem scaledMessage_uniform_tendsto (β : ℝ) (hβ : 0 ≤ β) :
    Tendsto (fun j => complexify (scaledMessage n β (j+1))) atTop
      (nhds ((overlap n β hβ : ℂ) • complexify (ground n β hβ))) := by
  have ht := (CompactKernelOperator.smoothingOperator (measure n) (kernelMap n β)).continuous
    |>.tendsto ((overlap n β hβ : ℂ) • WilsonVacuumConvergence.vacuum n β hβ)
    |>.comp (WilsonCylinderVacuum.boundary_power_tendsto n β hβ)
  have hs := ht.const_smul ((‖transfer n β‖⁻¹ : ℝ) : ℂ)
  have he (j : ℕ) : complexify (scaledMessage n β (j+1)) =
      ((‖transfer n β‖⁻¹ : ℝ) : ℂ) •
        CompactKernelOperator.smoothingOperator (measure n) (kernelMap n β)
          (iterate (WilsonSlabContraction.normalized n β) j (boundary n β)) := by
    rw [scaledMessage_succ, complexify_smul, complexify_realSmoothing,
      ← scaledMessage_embedding]
    rfl
  simp only [Function.comp_apply] at hs
  simp_rw [← he] at hs
  rw [map_smul, smoothing_ground, smul_smul, smul_smul] at hs
  have hc : ((‖transfer n β‖⁻¹ : ℝ) : ℂ)*
      (overlap n β hβ : ℂ)*(‖transfer n β‖ : ℂ) = (overlap n β hβ : ℂ) := by
    rw [Complex.ofReal_inv]
    field_simp [(Complex.ofReal_ne_zero.mpr
      (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1.ne')]
  rwa [hc] at hs

theorem scaledMessage_pointwise_tendsto (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    Tendsto (fun j => scaledMessage n β (j+1) u) atTop
      (nhds (overlap n β hβ*ground n β hβ u)) := by
  have h := ((continuous_eval_const u).tendsto _).comp
    (scaledMessage_uniform_tendsto n β hβ)
  have hr := Complex.continuous_re.tendsto _ |>.comp h
  simpa only [Function.comp_apply, complexify, ContinuousMap.coe_mk,
    ContinuousMap.smul_apply, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re] using hr

end
end UnifiedTheory.Clay.YangMills.WilsonBoundaryPointwise

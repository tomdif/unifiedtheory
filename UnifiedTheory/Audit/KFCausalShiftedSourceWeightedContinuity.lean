/- Continuous L2 vectors for polynomially controlled physical multipliers
of a complex-shifted Gaussian. A common physical Gaussian envelope is
derived for bounded source curves; no continuity of an unbounded operator
is inferred from continuity of its input. -/
import UnifiedTheory.Audit.KFCausalShiftedGaussianRadialMoments
import UnifiedTheory.Audit.KFCausalDominatedL2Continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalShiftedSourceWeightedContinuity
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalRadialMultipliers
open KFCausalRelativeGaussianDifferential (profile)
open KFCausalClockFloorRelativeShift (scale relative)
open KFCausalClockFloorCoherentBounds (sourceSize sourceConstant positionConstant)
open KFCausalImaginaryShearPathBounds (envelope constant)

def weighted (ε y α β : ℝ) (A : ℝ → ℂ) (m : Configuration → ℂ)
    (C : ℂ) (b : Fin 5 → ℂ) (x : Configuration) : ℂ :=
  m x*(C*profile A (scale ε y) α β b x)

theorem weighted_memLp (ε y α β : ℝ) (A : ℝ → ℂ) (m : Configuration → ℂ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hA : ContDiff ℝ 1 A) (hAm : MemLp A 2 volume)
    (hm : Controlled m) (C : ℂ) (b : Fin 5 → ℂ) :
    MemLp (weighted ε y α β A m C b) 2 volume := by
  have hf := controlled_memLp m _ hm (fun n =>
    KFCausalShiftedGaussianRadialMoments.profile_radius_memLp ε y A hε hy hA hAm α β hα hβ hw b n)
  convert hf.const_mul C using 1
  funext x
  unfold weighted
  ring

theorem profile_uniform_bound (ε y α β B : ℝ) (A : ℝ → ℂ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (b : Fin 5 → ℂ) (hb : sourceSize b ≤ B) (x : Configuration) :
    ‖profile A (scale ε y) α β b x‖ ≤
      Real.exp (B*positionConstant α β/2)*‖envelope A α β 0 x‖ := by
  have ht := KFCausalImaginaryShearPathBounds.path_bound A (relative ε y)
    (KFCausalShiftedGaussianRadialMoments.relative_strip ε y hε hy) α β hα hβ hw b 1
    (by constructor <;> norm_num) x
  simp only [KFCausalImaginaryShearInterpolation.path_one] at ht
  have hp := KFCausalClockFloorCoherentBounds.positionConstant_positive α β hα hβ
  have hs : sourceConstant α β b ≤ B*positionConstant α β :=
    mul_le_mul_of_nonneg_right hb hp.le
  have hc : constant α β b ≤ Real.exp (B*positionConstant α β/2)*constant α β 0 := by
    have he := Real.exp_le_exp.mpr (show sourceConstant α β b/2 ≤ B*positionConstant α β/2 by linarith)
    simpa only [constant,sourceConstant,sourceSize,Pi.zero_apply,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),
      Finset.sum_const_zero,zero_mul,zero_div,Real.exp_zero,mul_one,one_mul,mul_comm] using
      mul_le_mul_of_nonneg_left he (Real.exp_pos (Real.pi/3)).le
  have he : ‖envelope A α β b x‖ ≤ Real.exp (B*positionConstant α β/2)*‖envelope A α β 0 x‖ := by
    have hc0 : 0 < constant α β 0 := by unfold constant; positivity
    have hcb : 0 < constant α β b := by unfold constant; positivity
    simpa only [envelope,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hc0,abs_of_pos hcb,mul_assoc] using
      mul_le_mul_of_nonneg_right hc (norm_nonneg (A x.1*KFCausalClockFloorShearBounds.physicalGaussian
        (KFCausalImaginaryShearPathBounds.width α β) (KFCausalImaginaryShearPathBounds.width α β) x.2))
  exact ht.trans he

variable (ε y α β : ℝ) (A : ℝ → ℂ) (m : Configuration → ℂ)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (hA : ContDiff ℝ 1 A) (hAm : MemLp A 2 volume) (hm : Controlled m)

def state (C : ℂ) (b : Fin 5 → ℂ) : Hilbert :=
  (weighted_memLp ε y α β A m hε hy hα hβ hw hA hAm hm C b).toLp (weighted ε y α β A m C b)

theorem state_coe (C : ℂ) (b : Fin 5 → ℂ) :
    state ε y α β A m hε hy hα hβ hw hA hAm hm C b =ᵐ[volume] weighted ε y α β A m C b :=
  (weighted_memLp ε y α β A m hε hy hα hβ hw hA hAm hm C b).coeFn_toLp

theorem state_curve_continuous (B : ℝ) (C : ℝ → ℂ) (b : ℝ → Fin 5 → ℂ)
    (hC : Continuous C) (hb : Continuous b) (hCB : ∀ θ, ‖C θ‖ ≤ 1)
    (hbB : ∀ θ, sourceSize (b θ) ≤ B) :
    Continuous (fun θ => state ε y α β A m hε hy hα hβ hw hA hAm hm (C θ) (b θ)) := by
  have hg := controlled_memLp m (envelope A α β 0) hm (fun n =>
    KFCausalGaussianAllRadiusMoments.radius_envelope_memLp A hAm α β hα hβ 0 n)
  apply KFCausalDominatedL2Continuity.continuous_toLp _ _
    (fun x => (Real.exp (B*positionConstant α β/2):ℂ)*(m x*envelope A α β 0 x))
    (hg.const_mul _)
  · intro θ
    filter_upwards [] with x
    have hp := profile_uniform_bound ε y α β B A hε hy hα hβ hw (b θ) (hbB θ) x
    have hc : ‖C θ*profile A (scale ε y) α β (b θ) x‖ ≤
        Real.exp (B*positionConstant α β/2)*‖envelope A α β 0 x‖ := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hCB θ) (norm_nonneg _)).trans (by simpa using hp)
    simpa only [weighted,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),mul_assoc,mul_left_comm] using
      mul_le_mul_of_nonneg_left hc (norm_nonneg (m x))
  · filter_upwards [] with x
    unfold weighted profile KFCausalRelativeGaussianDifferential.exponent
    fun_prop

#print axioms weighted_memLp
#print axioms profile_uniform_bound
#print axioms state_coe
#print axioms state_curve_continuous
end
end UnifiedTheory.Audit.KFCausalShiftedSourceWeightedContinuity

/- The actual bounded multiplication operator for the classical clock
bracket defect epsilon/(exp(s)+epsilon), on the physical configuration L2
space. Its norm measures a state's clock defect; it is not yet a quantum
commutator identity or a semiclassical error estimate. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectLimits
import UnifiedTheory.Audit.KFCausalContractiveMultiplier
import UnifiedTheory.Audit.KFCausalConfigurationTestSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectLimits
open UnifiedTheory.Audit.KFCausalContractiveMultiplier

def weight (ε : ℝ) (x : Configuration) : ℂ := (defect ε x.1 : ℂ)

theorem weight_measurable (ε : ℝ) : Measurable (weight ε) := by
  unfold weight defect clock
  fun_prop

theorem weight_bound (ε : ℝ) (hε : 0 < ε) (x : Configuration) : ‖weight ε x‖ ≤ 1 := by
  rw [weight, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (defect_positive ε x.1 hε)]
  have h := response_add_defect ε x.1 hε.le
  linarith [(response_bounds ε x.1 hε).1]

def defectOperator (ε : ℝ) (hε : 0 < ε) : Hilbert →L[ℂ] Hilbert :=
  multiplyL (weight ε) (weight_measurable ε) (weight_bound ε hε)

theorem defectOperator_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    defectOperator ε hε f =ᵐ[volume] fun x => (defect ε x.1 : ℂ)*f x :=
  multiplyL_coe _ _ _ f

theorem defectOperator_norm_le (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    ‖defectOperator ε hε f‖ ≤ ‖f‖ :=
  multiply_norm_le (weight ε) (weight_measurable ε) (weight_bound ε hε) f

theorem defectOperator_injective (ε : ℝ) (hε : 0 < ε) :
    Function.Injective (defectOperator ε hε) :=
  multiplyL_injective _ _ _ (fun x => Complex.ofReal_ne_zero.mpr (defect_positive ε x.1 hε).ne')

/-- No nonzero L2 state has exactly zero defect at fixed positive floor. -/
theorem defectOperator_ne_zero (ε : ℝ) (hε : 0 < ε) (f : Hilbert) (hf : f ≠ 0) :
    defectOperator ε hε f ≠ 0 := by
  intro h
  exact hf ((defectOperator_injective ε hε) (h.trans (map_zero _).symm))

/-- A state supported above a log-clock threshold has small norm defect. -/
theorem defectOperator_on_supported_state (ε : ℝ) (hε : 0 < ε) (S : ℝ) (f : Hilbert)
    (hf : ∀ᵐ x ∂volume, x.1 < S → f x = 0) :
    ‖defectOperator ε hε f‖ ≤ (ε * Real.exp (-S)) * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [defectOperator_coe ε hε f, hf] with x hx hzero
  rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (defect_positive ε x.1 hε)]
  by_cases hs : x.1 < S
  · simp [hzero hs]
  · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (defect_upper_bound ε x.1 hε.le).trans
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hε.le

#print axioms weight_measurable
#print axioms weight_bound
#print axioms defectOperator_coe
#print axioms defectOperator_norm_le
#print axioms defectOperator_injective
#print axioms defectOperator_ne_zero
#print axioms defectOperator_on_supported_state

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectOperator

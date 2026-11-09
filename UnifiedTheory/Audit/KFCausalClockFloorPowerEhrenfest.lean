/- Exact higher clock-defect moment dynamics on the actual propagated
energy form. The upward rate is O(abs(hbar)) at each fixed moment order. -/
import UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityOutput
import UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest
import UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
import UnifiedTheory.Audit.KFCausalClockFloorReferenceDefect
import UnifiedTheory.Audit.KFCausalFormObservableDerivative
import UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorPowerEhrenfest
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakIntegralEquation (limitSlope)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalClockFloorReferenceDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ) (n : ℕ)
local notation "V₀" => FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0
local notation "J" => embedding ε hε hbar hh hbound mass2 quartic vacuum 0
local notation "E" => timeEnergy ε hε hbar hh hbound mass2 quartic vacuum
local notation "F" => formFlow ε hε hbar hh hbound mass2 quartic vacuum
local notation "U" => evolution ε hε hbar hh hbound mass2 quartic vacuum
local notation "D" => (defectOperator ε hε)^(n+1)
local notation "R" => (ContinuousLinearMap.compLpL 2 KFCausalUnitIntervalOrbit.angleMeasure (outputAction ε hε hbar hbound))^(n+1)
local notation "A" => (formDefect ε hε hbar hh hbound mass2 quartic vacuum 0)^(n+1)

open UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest (evolvingOutput)
open UnifiedTheory.Audit.KFCausalClockFloorPowerForm (formPower_embedding reference_power_pairing)
open UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityPairing (defect_power_inner)
open UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityScalar (errorConstant)
open UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityOutput (outputLp_power_rate_upper)

def powerRate (s t : ℝ) (w : V₀) : ℝ :=
  (-2/hbar)*(inner ℂ (evolvingOutput ε hε hbar hh hbound mass2 quartic vacuum s t w)
    (R (evolvingOutput ε hε hbar hh hbound mass2 quartic vacuum s t w))).im

theorem powerExpectation_derivative (s t : ℝ) (w : V₀) :
    HasDerivAt (fun r => (inner ℂ (U s r (J w)) (D (U s r (J w)))).re)
      (powerRate ε hε hbar hh hbound mass2 quartic vacuum n s t w) t := by
  let V := weakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w
  have hd := KFCausalFormObservableDerivative.expectation_derivative J D
    (massOperator ε hε hbar hh hbound mass2 quartic vacuum) A
    (mass_left_pairing ε hε hbar hh hbound mass2 quartic vacuum)
    (formPower_embedding ε hε hbar hh hbound mass2 quartic vacuum 0 (n+1))
    (defect_power_inner ε hε (n+1))
    V.formState (massSlope ε hε hbar hh hbound mass2 quartic vacuum s w V t)
    t (massLipschitzBound ε hε hbar hh hbound mass2 quartic vacuum s (|t|+1) w)
    (massLipschitzBound_nonneg ε hε hbar hh hbound mass2 quartic vacuum s (|t|+1) w)
    (formFlow_continuous ε hε hbar hh hbound mass2 quartic vacuum s w).continuousAt
    ?_ (mass_pairing_derivative ε hε hbar hh hbound mass2 quartic vacuum s w V t)
  · have hr : 2*(inner ℂ (massSlope ε hε hbar hh hbound mass2 quartic vacuum s w V t)
        (A (V.formState t))).re = powerRate ε hε hbar hh hbound mass2 quartic vacuum n s t w := by
      rw [massSlope_pairing,limitSlope,reference_power_pairing]
      simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,mul_zero,sub_zero,zero_add,zero_sub]
      unfold powerRate evolvingOutput
      dsimp only [V,formFlow]
      ring
    simpa only [KFCausalFormObservableDerivative.expectation,evolution_embedding] using hd.congr_deriv hr
  · have he : ∀ᶠ h in 𝓝 (0:ℝ), |h| < 1 := by
      simpa only [abs_zero] using (continuous_abs.tendsto (0:ℝ)).eventually
        (gt_mem_nhds (by norm_num : |(0:ℝ)| < 1))
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with h hsmall
    have hsum : |t+h| ≤ |t|+|h| := abs_add_le _ _
    simpa only [add_sub_cancel_left] using
      massState_window_lipschitz ε hε hbar hh hbound mass2 quartic vacuum s w V
        (|t|+1) t (t+h) (by positivity) (by linarith) (hsum.trans (by linarith))

theorem powerRate_continuous (s : ℝ) (w : V₀) :
    Continuous (fun t => powerRate ε hε hbar hh hbound mass2 quartic vacuum n s t w) := by
  have hf := formFlow_continuous ε hε hbar hh hbound mass2 quartic vacuum s w
  have hq : Continuous (referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (referenceForm_derivative ε hε hbar hh hbound mass2 quartic vacuum t).continuousAt)
  have hp := hf.inner (𝕜 := ℂ) (hq.clm_apply ((A).continuous.comp hf))
  have hc : Continuous (fun t => (-2/hbar)*(inner ℂ (F s t w)
      (referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum t (A (F s t w)))).im) :=
    continuous_const.mul (Complex.continuous_im.comp hp)
  have he : (fun t => (-2/hbar)*(inner ℂ (F s t w)
      (referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum t (A (F s t w)))).im) =
      (fun t => powerRate ε hε hbar hh hbound mass2 quartic vacuum n s t w) := by
    funext t
    rw [reference_power_pairing]
    rfl
  exact he ▸ hc

theorem powerExpectation_integral (s r t : ℝ) (w : V₀) :
    (∫ z in r..t, powerRate ε hε hbar hh hbound mass2 quartic vacuum n s z w) =
      (inner ℂ (U s t (J w)) (D (U s t (J w)))).re-
      (inner ℂ (U s r (J w)) (D (U s r (J w)))).re :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z _ => powerExpectation_derivative ε hε hbar hh hbound mass2 quartic vacuum n s z w)
    ((powerRate_continuous ε hε hbar hh hbound mass2 quartic vacuum n s w).intervalIntegrable _ _)

theorem powerRate_upper (s t : ℝ) (w : V₀) :
    powerRate ε hε hbar hh hbound mass2 quartic vacuum n s t w ≤
      (errorConstant ε n*|hbar|)*E t (F s t w) := by
  have he := outputLp_power_rate_upper ε hε hbar hh hbound n
    (evolvingOutput ε hε hbar hh hbound mass2 quartic vacuum s t w)
  simpa only [evolvingOutput,timeEnergy_actual] using he

#print axioms powerExpectation_derivative
#print axioms powerRate_continuous
#print axioms powerExpectation_integral
#print axioms powerRate_upper

end
end UnifiedTheory.Audit.KFCausalClockFloorPowerEhrenfest

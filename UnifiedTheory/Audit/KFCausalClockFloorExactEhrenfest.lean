/- Exact clock-defect expectation dynamics for the actual unbounded
propagator on every initial energy-form state. The chain rule uses strong
form continuity and the established weak equation, without assuming
invariance of the Hamiltonian operator domain. -/
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

namespace UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest
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
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "V₀" => FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0
local notation "J" => embedding ε hε hbar hh hbound mass2 quartic vacuum 0
local notation "E" => timeEnergy ε hε hbar hh hbound mass2 quartic vacuum
local notation "F" => formFlow ε hε hbar hh hbound mass2 quartic vacuum
local notation "U" => evolution ε hε hbar hh hbound mass2 quartic vacuum
local notation "D" => defectOperator ε hε
local notation "R" => ContinuousLinearMap.compLp (outputAction ε hε hbar hbound)
local notation "Q" => ContinuousLinearMap.compLp (classicalOutput ε hε)
local notation "A" => formDefect ε hε hbar hh hbound mass2 quartic vacuum 0

def evolvingOutput (s t : ℝ) (w : V₀) :=
  energyOutput ε hε hbar hh hbound mass2 quartic vacuum t
    (formTransfer ε hε hbar hh hbound mass2 quartic vacuum 0 t (F s t w))

def exactRate (s t : ℝ) (w : V₀) : ℝ :=
  (-2/hbar)*(inner ℂ (evolvingOutput ε hε hbar hh hbound mass2 quartic vacuum s t w)
    (R (evolvingOutput ε hε hbar hh hbound mass2 quartic vacuum s t w))).im

def classicalRate (s t : ℝ) (w : V₀) : ℝ :=
  (inner ℂ (evolvingOutput ε hε hbar hh hbound mass2 quartic vacuum s t w)
    (Q (evolvingOutput ε hε hbar hh hbound mass2 quartic vacuum s t w))).re

theorem expectation_derivative (s t : ℝ) (w : V₀) :
    HasDerivAt (fun r => (inner ℂ (U s r (J w)) (D (U s r (J w)))).re)
      (exactRate ε hε hbar hh hbound mass2 quartic vacuum s t w) t := by
  let V := weakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w
  have hd := KFCausalFormObservableDerivative.expectation_derivative J D
    (massOperator ε hε hbar hh hbound mass2 quartic vacuum) A
    (mass_left_pairing ε hε hbar hh hbound mass2 quartic vacuum)
    (formDefect_embedding ε hε hbar hh hbound mass2 quartic vacuum 0)
    (KFCausalClockFloorDefectForm.defect_inner ε hε)
    V.formState (massSlope ε hε hbar hh hbound mass2 quartic vacuum s w V t)
    t (massLipschitzBound ε hε hbar hh hbound mass2 quartic vacuum s (|t|+1) w)
    (massLipschitzBound_nonneg ε hε hbar hh hbound mass2 quartic vacuum s (|t|+1) w)
    (formFlow_continuous ε hε hbar hh hbound mass2 quartic vacuum s w).continuousAt
    ?_ (mass_pairing_derivative ε hε hbar hh hbound mass2 quartic vacuum s w V t)
  · have hr : 2*(inner ℂ (massSlope ε hε hbar hh hbound mass2 quartic vacuum s w V t)
        (A (V.formState t))).re = exactRate ε hε hbar hh hbound mass2 quartic vacuum s t w := by
      rw [massSlope_pairing,limitSlope,reference_defect_pairing]
      simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,mul_zero,sub_zero,zero_add,zero_sub]
      unfold exactRate evolvingOutput
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

theorem rate_error (s t : ℝ) (w : V₀) :
    |exactRate ε hε hbar hh hbound mass2 quartic vacuum s t w-
      classicalRate ε hε hbar hh hbound mass2 quartic vacuum s t w| ≤
      (20*|hbar|/ε^2)*E t (F s t w) := by
  have he := outputLp_velocity_error ε hε hbar hh hbound
    (evolvingOutput ε hε hbar hh hbound mass2 quartic vacuum s t w)
  simpa only [evolvingOutput,timeEnergy_actual] using he

theorem rate_error_initial_energy (s t : ℝ) (w : V₀) :
    |exactRate ε hε hbar hh hbound mass2 quartic vacuum s t w-
      classicalRate ε hε hbar hh hbound mass2 quartic vacuum s t w| ≤
      (20*|hbar|/ε^2)*Real.exp (2*|t-s|)*E s w := by
  apply (rate_error ε hε hbar hh hbound mass2 quartic vacuum s t w).trans
  have he := mul_le_mul_of_nonneg_left
    (formFlow_energy_bound ε hε hbar hh hbound mass2 quartic vacuum s t w)
    (by positivity : 0 ≤ 20*|hbar|/ε^2)
  simpa only [mul_assoc] using he

theorem exactRate_continuous (s : ℝ) (w : V₀) :
    Continuous (fun t => exactRate ε hε hbar hh hbound mass2 quartic vacuum s t w) := by
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
      (fun t => exactRate ε hε hbar hh hbound mass2 quartic vacuum s t w) := by
    funext t
    rw [reference_defect_pairing]
    rfl
  exact he ▸ hc

theorem expectation_integral (s r t : ℝ) (w : V₀) :
    (∫ z in r..t, exactRate ε hε hbar hh hbound mass2 quartic vacuum s z w) =
      (inner ℂ (U s t (J w)) (D (U s t (J w)))).re-
      (inner ℂ (U s r (J w)) (D (U s r (J w)))).re :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z _ => expectation_derivative ε hε hbar hh hbound mass2 quartic vacuum s z w)
    ((exactRate_continuous ε hε hbar hh hbound mass2 quartic vacuum s w).intervalIntegrable _ _)

#print axioms exactRate_continuous
#print axioms expectation_integral
#print axioms expectation_derivative
#print axioms rate_error
#print axioms rate_error_initial_energy

end
end UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest

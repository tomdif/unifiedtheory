/- Exact dynamics of the charge-compatible radial position observable
along the existing unbounded propagator. Both form lifts and the adjoint
identity are derived, so the weak-evolution chain rule has no additional
observable-domain premise. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialReferenceResponse
import UnifiedTheory.Audit.KFCausalNeutralEhrenfest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialEhrenfest
noncomputable section
open Filter
open scoped Topology ComplexConjugate
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakIntegralEquation (limitSlope)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (action)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCompletedForm (formAction formAction_embedding)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialReferenceResponse (rate rate_bound)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialShiftPairing (responseConstant)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialFullResponse (kineticConstant)
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)
open UnifiedTheory.Audit.KFCausalNeutralEhrenfest (coefficient_pairing)

variable (ε : ℝ) (hε : 0 < ε) (h δ v : ℝ) (hδ : 0 < δ)
  (hh : |h| ≤ 2*Real.pi*ε/3) (hne : h ≠ 0) (m g k : ℝ)
local notation "V₀" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "A" => formAction ε hε h δ v hδ hh hne m g k 0
local notation "B" => formAction ε hε h δ (-v) hδ hh hne m g k 0

def characteristic (s t : ℝ) (w : V₀) : ℂ :=
  inner ℂ (U s t (J w)) (action h δ v hδ (U s t (J w)))

def exactRate (s t : ℝ) (w : V₀) : ℂ :=
  rate ε hε h δ v hδ hh hne m g k t (F s t w)

theorem expectation_derivative (s t : ℝ) (w : V₀) :
    HasDerivAt (fun z => characteristic ε hε h δ v hδ hh hne m g k s z w)
      (exactRate ε hε h δ v hδ hh hne m g k s t w) t := by
  let V := weakTrajectory ε hε h hne hh m g k s w
  have hD : ∀ x y, inner ℂ (action h δ v hδ x) y = inner ℂ x (action h δ (-v) hδ y) := by
    intro x y
    simpa only [neg_neg] using (KFCausalNeutralPositionRadialAdjoint.action_dual h δ (-v) hδ x y).symm
  have hd := KFCausalComplexFormObservableDerivative.expectation_derivative J
    (action h δ v hδ) (action h δ (-v) hδ)
    (massOperator ε hε h hne hh m g k) A B
    (mass_left_pairing ε hε h hne hh m g k)
    (formAction_embedding ε hε h δ v hδ hh hne m g k 0)
    (formAction_embedding ε hε h δ (-v) hδ hh hne m g k 0)
    hD V.formState (massSlope ε hε h hne hh m g k s w V t)
    t (massLipschitzBound ε hε h hne hh m g k s (|t|+1) w)
    (massLipschitzBound_nonneg ε hε h hne hh m g k s (|t|+1) w)
    (formFlow_continuous ε hε h hne hh m g k s w).continuousAt
    ?_ (mass_pairing_derivative ε hε h hne hh m g k s w V t)
  · have hr : inner ℂ (massSlope ε hε h hne hh m g k s w V t) (A (V.formState t))+
        conj (inner ℂ (massSlope ε hε h hne hh m g k s w V t) (B (V.formState t))) =
        exactRate ε hε h δ v hδ hh hne m g k s t w := by
      have hs := coefficient_pairing h
        (inner ℂ (V.formState t) (Q t (A (V.formState t))))
        (inner ℂ (V.formState t) (Q t (B (V.formState t))))
      simpa only [massSlope_pairing,limitSlope,exactRate,rate,coefficient,formFlow] using hs
    simpa only [KFCausalComplexFormObservableDerivative.expectation,characteristic,evolution_embedding]
      using hd.congr_deriv hr
  · have he : ∀ᶠ z in 𝓝 (0:ℝ), |z| < 1 := by
      simpa only [abs_zero] using (continuous_abs.tendsto (0:ℝ)).eventually
        (gt_mem_nhds (by norm_num : |(0:ℝ)| < 1))
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with z hz
    have hsum : |t+z| ≤ |t|+|z| := abs_add_le _ _
    simpa only [add_sub_cancel_left] using
      massState_window_lipschitz ε hε h hne hh m g k s w V (|t|+1) t (t+z)
        (by positivity) (by linarith) (hsum.trans (by linarith))

theorem exactRate_continuous (s : ℝ) (w : V₀) :
    Continuous (fun t => exactRate ε hε h δ v hδ hh hne m g k s t w) := by
  have hf := formFlow_continuous ε hε h hne hh m g k s w
  have hq : Continuous (referenceFormOperator ε hε h hne hh m g k) :=
    continuous_iff_continuousAt.mpr (fun t => (referenceForm_derivative ε hε h hne hh m g k t).continuousAt)
  have h1 := hf.inner (𝕜 := ℂ) (hq.clm_apply ((A).continuous.comp hf))
  have h2 := hf.inner (𝕜 := ℂ) (hq.clm_apply ((B).continuous.comp hf))
  have hc := (continuous_const (y := coefficient h)).mul (h1.sub (Complex.continuous_conj.comp h2))
  simpa only [exactRate,rate] using hc

theorem expectation_integral (s a b : ℝ) (w : V₀) :
    (∫ t in a..b, exactRate ε hε h δ v hδ hh hne m g k s t w) =
      characteristic ε hε h δ v hδ hh hne m g k s b w-
        characteristic ε hε h δ v hδ hh hne m g k s a w :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => expectation_derivative ε hε h δ v hδ hh hne m g k s t w)
    ((exactRate_continuous ε hε h δ v hδ hh hne m g k s w).intervalIntegrable _ _)

theorem exactRate_energy_bound (hs : |h| ≤ Real.pi*ε/3) (s t : ℝ) (w : V₀) :
    ‖exactRate ε hε h δ v hδ hh hne m g k s t w‖ ≤
      responseConstant ε δ v*timeEnergy ε hε h hne hh m g k t (F s t w)+
        2*kineticConstant ε δ v*‖J w‖*Real.sqrt (timeEnergy ε hε h hne hh m g k t (F s t w)) := by
  simpa only [formFlow_physical_norm,exactRate] using
    rate_bound ε hε h δ v hδ hh hne m g k hs t (F s t w)

#print axioms expectation_derivative
#print axioms exactRate_continuous
#print axioms expectation_integral
#print axioms exactRate_energy_bound

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialEhrenfest

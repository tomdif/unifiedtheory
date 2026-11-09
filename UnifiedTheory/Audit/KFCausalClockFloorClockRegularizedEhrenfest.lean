/- Exact bounded positive-clock evolution along the actual averaged propagator. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockReferenceRate
import UnifiedTheory.Audit.KFCausalNeutralEhrenfest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockRegularizedEhrenfest
noncomputable section
open Filter
open scoped Topology ComplexConjugate
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakIntegralEquation (limitSlope)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedClockResolvent
open UnifiedTheory.Audit.KFCausalClockFloorClockResolvent
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)
open UnifiedTheory.Audit.KFCausalNeutralEhrenfest (coefficient_pairing)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k b : ℝ) (hb : 0 < b)
local notation "V₀" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "A" => formApprox ε hε h hne hh m g k 0 b hb
local notation "O" => clockApprox ε hε b hb

def characteristic (s t : ℝ) (w : V₀) : ℂ :=
  inner ℂ (U s t (J w)) (O (U s t (J w)))

def exactRate (s t : ℝ) (w : V₀) : ℂ :=
  coefficient h*(inner ℂ (F s t w) (Q t (A (F s t w)))-
    conj (inner ℂ (F s t w) (Q t (A (F s t w)))))

theorem expectation_derivative (s t : ℝ) (w : V₀) :
    HasDerivAt (fun z => characteristic ε hε h hne hh m g k b hb s z w)
      (exactRate ε hε h hne hh m g k b hb s t w) t := by
  let V := weakTrajectory ε hε h hne hh m g k s w
  have hd := KFCausalComplexFormObservableDerivative.expectation_derivative J
    (O) (O)
    (massOperator ε hε h hne hh m g k) (A) (A)
    (mass_left_pairing ε hε h hne hh m g k)
    (approx_embedding ε hε h hne hh m g k 0 b hb)
    (approx_embedding ε hε h hne hh m g k 0 b hb)
    (clockApprox_dual ε hε b hb) V.formState (massSlope ε hε h hne hh m g k s w V t)
    t (massLipschitzBound ε hε h hne hh m g k s (|t|+1) w)
    (massLipschitzBound_nonneg ε hε h hne hh m g k s (|t|+1) w)
    (formFlow_continuous ε hε h hne hh m g k s w).continuousAt
    ?_ (mass_pairing_derivative ε hε h hne hh m g k s w V t)
  · have hr : inner ℂ (massSlope ε hε h hne hh m g k s w V t) (A (V.formState t))+
        conj (inner ℂ (massSlope ε hε h hne hh m g k s w V t) (A (V.formState t))) =
        exactRate ε hε h hne hh m g k b hb s t w := by
      have hs := coefficient_pairing h
        (inner ℂ (V.formState t) (referenceFormOperator ε hε h hne hh m g k t (A (V.formState t))))
        (inner ℂ (V.formState t) (referenceFormOperator ε hε h hne hh m g k t (A (V.formState t))))
      simpa only [massSlope_pairing,limitSlope,exactRate,coefficient,formFlow] using hs
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
    Continuous (fun t => exactRate ε hε h hne hh m g k b hb s t w) := by
  have hf := formFlow_continuous ε hε h hne hh m g k s w
  have hq : Continuous (referenceFormOperator ε hε h hne hh m g k) :=
    continuous_iff_continuousAt.mpr (fun t => (referenceForm_derivative ε hε h hne hh m g k t).continuousAt)
  have h1 := hf.inner (𝕜 := ℂ) (hq.clm_apply ((A).continuous.comp hf))
  have h2 := hf.inner (𝕜 := ℂ) (hq.clm_apply ((A).continuous.comp hf))
  have hc := (continuous_const (y := coefficient h)).mul (h1.sub (Complex.continuous_conj.comp h2))
  simpa only [exactRate] using hc

theorem expectation_integral (s r c : ℝ) (w : V₀) :
    (∫ t in r..c, exactRate ε hε h hne hh m g k b hb s t w) =
      characteristic ε hε h hne hh m g k b hb s c w-characteristic ε hε h hne hh m g k b hb s r w :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => expectation_derivative ε hε h hne hh m g k b hb s t w)
    ((exactRate_continuous ε hε h hne hh m g k b hb s w).intervalIntegrable _ _)

#print axioms expectation_derivative
#print axioms exactRate_continuous
#print axioms expectation_integral

end
end UnifiedTheory.Audit.KFCausalClockFloorClockRegularizedEhrenfest

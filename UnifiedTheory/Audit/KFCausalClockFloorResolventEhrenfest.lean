/- Exact complex evolution identities for resolvent-regularized bounded
observables along the actual averaged propagator. The domain lifts are
constructed for every observable and its adjoint, without a phase-domain
invariance assumption. -/
import UnifiedTheory.Audit.KFCausalClockFloorResolventTests
import UnifiedTheory.Audit.KFCausalNeutralEhrenfest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorResolventEhrenfest
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
open UnifiedTheory.Audit.KFCausalClockFloorResolventTests
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)
open UnifiedTheory.Audit.KFCausalNeutralEhrenfest (coefficient_pairing)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k a τ : ℝ) (D : Hilbert →L[ℂ] Hilbert)
local notation "V₀" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "A" => formLift ε hε h hne hh m g k a τ
local notation "O" => observable ε hε h hne hh m g k a τ

def characteristic (s t : ℝ) (w : V₀) : ℂ :=
  inner ℂ (U s t (J w)) (O D (U s t (J w)))

def exactRate (s t : ℝ) (w : V₀) : ℂ :=
  coefficient h*(inner ℂ (F s t w) (Q t (A D (F s t w)))-
    conj (inner ℂ (F s t w) (Q t (A D.adjoint (F s t w)))))

variable (ha : 0 < a)
include ha in
theorem expectation_derivative (s t : ℝ) (w : V₀) :
    HasDerivAt (fun z => characteristic ε hε h hne hh m g k a τ D s z w)
      (exactRate ε hε h hne hh m g k a τ D s t w) t := by
  let V := weakTrajectory ε hε h hne hh m g k s w
  have hd := KFCausalComplexFormObservableDerivative.expectation_derivative J
    (O D) (O D.adjoint)
    (massOperator ε hε h hne hh m g k) (A D) (A D.adjoint)
    (mass_left_pairing ε hε h hne hh m g k)
    (formLift_embedding ε hε h hne hh m g k a τ D)
    (formLift_embedding ε hε h hne hh m g k a τ D.adjoint)
    (observable_dual ε hε h hne hh m g k a τ ha D) V.formState (massSlope ε hε h hne hh m g k s w V t)
    t (massLipschitzBound ε hε h hne hh m g k s (|t|+1) w)
    (massLipschitzBound_nonneg ε hε h hne hh m g k s (|t|+1) w)
    (formFlow_continuous ε hε h hne hh m g k s w).continuousAt
    ?_ (mass_pairing_derivative ε hε h hne hh m g k s w V t)
  · have hr : inner ℂ (massSlope ε hε h hne hh m g k s w V t) (A D (V.formState t))+
        conj (inner ℂ (massSlope ε hε h hne hh m g k s w V t) (A D.adjoint (V.formState t))) =
        exactRate ε hε h hne hh m g k a τ D s t w := by
      have hs := coefficient_pairing h
        (inner ℂ (V.formState t) (referenceFormOperator ε hε h hne hh m g k t (A D (V.formState t))))
        (inner ℂ (V.formState t) (referenceFormOperator ε hε h hne hh m g k t (A D.adjoint (V.formState t))))
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
    Continuous (fun t => exactRate ε hε h hne hh m g k a τ D s t w) := by
  have hf := formFlow_continuous ε hε h hne hh m g k s w
  have hq : Continuous (referenceFormOperator ε hε h hne hh m g k) :=
    continuous_iff_continuousAt.mpr (fun t => (referenceForm_derivative ε hε h hne hh m g k t).continuousAt)
  have h1 := hf.inner (𝕜 := ℂ) (hq.clm_apply ((A D).continuous.comp hf))
  have h2 := hf.inner (𝕜 := ℂ) (hq.clm_apply ((A D.adjoint).continuous.comp hf))
  have hc := (continuous_const (y := coefficient h)).mul (h1.sub (Complex.continuous_conj.comp h2))
  simpa only [exactRate] using hc

include ha in
theorem expectation_integral (s b c : ℝ) (w : V₀) :
    (∫ t in b..c, exactRate ε hε h hne hh m g k a τ D s t w) =
      characteristic ε hε h hne hh m g k a τ D s c w-characteristic ε hε h hne hh m g k a τ D s b w :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => expectation_derivative ε hε h hne hh m g k a τ D ha s t w)
    ((exactRate_continuous ε hε h hne hh m g k a τ D s w).intervalIntegrable _ _)

#print axioms expectation_derivative
#print axioms exactRate_continuous
#print axioms expectation_integral

end
end UnifiedTheory.Audit.KFCausalClockFloorResolventEhrenfest

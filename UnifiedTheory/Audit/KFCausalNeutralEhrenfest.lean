/- Exact complex Ehrenfest dynamics for the canonical neutral-momentum
test along the actual unbounded propagator. The proof uses the derived
form action, weak equation and strong form continuity. -/
import UnifiedTheory.Audit.KFCausalComplexFormObservableDerivative
import UnifiedTheory.Audit.KFCausalNeutralReferencePairing
import UnifiedTheory.Audit.KFCausalNeutralWeightTime
import UnifiedTheory.Audit.KFCausalNeutralCanonicalForm
import UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalNeutralEhrenfest
noncomputable section
open Filter
open scoped Topology ComplexConjugate
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakIntegralEquation (limitSlope)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalNeutralReferenceForm
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient coefficient_conj action_dual rate)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates (action)
open UnifiedTheory.Audit.KFCausalNeutralTranslationPhysicalCommutator (speedBound)
open UnifiedTheory.Audit.KFCausalNeutralWeightTime (speedBound_time speedBound_nonneg)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)

theorem coefficient_pairing (h : ℝ) (x y : ℂ) :
    coefficient h*x+conj (coefficient h*y) = coefficient h*(x-conj y) := by
  rw [map_mul,coefficient_conj]
  ring

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ) (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
local notation "V₀" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "E" => timeEnergy ε hε h hne hh m g k
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "A" => formAction ε hε h hne hh m g k hm hg hk 0

def characteristic (r s t : ℝ) (w : V₀) : ℂ :=
  inner ℂ (U s t (J w)) (action r (U s t (J w)))

def exactRate (r s t : ℝ) (w : V₀) : ℂ :=
  rate ε hε h hne hh m g k hm hg hk t r (F s t w)

theorem expectation_derivative (r s t : ℝ) (w : V₀) :
    HasDerivAt (fun z => characteristic ε hε h hne hh m g k r s z w)
      (exactRate ε hε h hne hh m g k hm hg hk r s t w) t := by
  let V := weakTrajectory ε hε h hne hh m g k s w
  have hd := KFCausalComplexFormObservableDerivative.expectation_derivative J
    (action r : _ →L[ℂ] _) (action (-r) : _ →L[ℂ] _)
    (massOperator ε hε h hne hh m g k) (A r) (A (-r))
    (mass_left_pairing ε hε h hne hh m g k)
    (formAction_embedding ε hε h hne hh m g k hm hg hk 0 r)
    (formAction_embedding ε hε h hne hh m g k hm hg hk 0 (-r))
    (action_dual r) V.formState (massSlope ε hε h hne hh m g k s w V t)
    t (massLipschitzBound ε hε h hne hh m g k s (|t|+1) w)
    (massLipschitzBound_nonneg ε hε h hne hh m g k s (|t|+1) w)
    (formFlow_continuous ε hε h hne hh m g k s w).continuousAt
    ?_ (mass_pairing_derivative ε hε h hne hh m g k s w V t)
  · have hr : inner ℂ (massSlope ε hε h hne hh m g k s w V t) (A r (V.formState t))+
        conj (inner ℂ (massSlope ε hε h hne hh m g k s w V t) (A (-r) (V.formState t))) =
        exactRate ε hε h hne hh m g k hm hg hk r s t w := by
      have hs := coefficient_pairing h
        (inner ℂ (V.formState t) (referenceFormOperator ε hε h hne hh m g k t (A r (V.formState t))))
        (inner ℂ (V.formState t) (referenceFormOperator ε hε h hne hh m g k t (A (-r) (V.formState t))))
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

theorem exactRate_continuous (r s : ℝ) (w : V₀) :
    Continuous (fun t => exactRate ε hε h hne hh m g k hm hg hk r s t w) := by
  have hf := formFlow_continuous ε hε h hne hh m g k s w
  have hq : Continuous (referenceFormOperator ε hε h hne hh m g k) :=
    continuous_iff_continuousAt.mpr (fun t => (referenceForm_derivative ε hε h hne hh m g k t).continuousAt)
  have h1 := hf.inner (𝕜 := ℂ) (hq.clm_apply ((A r).continuous.comp hf))
  have h2 := hf.inner (𝕜 := ℂ) (hq.clm_apply ((A (-r)).continuous.comp hf))
  have hc := (continuous_const (y := coefficient h)).mul (h1.sub (Complex.continuous_conj.comp h2))
  simpa only [exactRate,rate] using hc

theorem expectation_integral (r s a b : ℝ) (w : V₀) :
    (∫ t in a..b, exactRate ε hε h hne hh m g k hm hg hk r s t w) =
      characteristic ε hε h hne hh m g k r s b w-characteristic ε hε h hne hh m g k r s a w :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => expectation_derivative ε hε h hne hh m g k hm hg hk r s t w)
    ((exactRate_continuous ε hε h hne hh m g k hm hg hk r s w).intervalIntegrable _ _)

theorem canonical_rate_bound (v H s t : ℝ) (hH : |h| ≤ H) (w : V₀) :
    ‖exactRate ε hε h hne hh m g k hm hg hk (h*v) s t w‖ ≤
      speedBound (energyWeight m g k 0) H v*E t (F s t w) := by
  have hb := KFCausalNeutralReferencePairing.canonical_rate_bound ε hε h hne hh m g k hm hg hk t v H hH (F s t w)
  simpa only [exactRate,speedBound_time m g k 0 t] using hb

theorem canonical_rate_initial_energy_bound (v H s t : ℝ) (hH : |h| ≤ H) (w : V₀) :
    ‖exactRate ε hε h hne hh m g k hm hg hk (h*v) s t w‖ ≤
      speedBound (energyWeight m g k 0) H v*(Real.exp (2*|t-s|)*E s w) := by
  have hb := canonical_rate_bound ε hε h hne hh m g k hm hg hk v H s t hH w
  have he := mul_le_mul_of_nonneg_left (formFlow_energy_bound ε hε h hne hh m g k s t w)
    (speedBound_nonneg (energyWeight m g k 0) H v ((abs_nonneg h).trans hH))
  exact hb.trans he

#print axioms coefficient_pairing
#print axioms expectation_derivative
#print axioms exactRate_continuous
#print axioms expectation_integral
#print axioms canonical_rate_bound
#print axioms canonical_rate_initial_energy_bound

end
end UnifiedTheory.Audit.KFCausalNeutralEhrenfest

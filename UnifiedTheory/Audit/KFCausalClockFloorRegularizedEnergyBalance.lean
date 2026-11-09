/- Exact regularized energy balance along the full quantum propagator.
The observable is the current Hamiltonian resolvent, and its frozen
commutator vanishes by the actual variational equation. -/
import UnifiedTheory.Audit.KFCausalClockFloorResolventFormLimit
import UnifiedTheory.Audit.KFCausalClockFloorMovingResolventEhrenfest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorRegularizedEnergyBalance
noncomputable section
open Filter
open scoped Topology ComplexConjugate
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormGeometry
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakIntegralEquation (limitSlope)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaEnergy
open UnifiedTheory.Audit.KFCausalClockFloorResolventTests
open UnifiedTheory.Audit.KFCausalClockFloorResolventEnergyControl
open UnifiedTheory.Audit.KFCausalClockFloorMovingResolvent
open UnifiedTheory.Audit.KFCausalClockFloorMovingResolventEhrenfest (reference_form_hermitian)
open UnifiedTheory.Audit.KFCausalNeutralEhrenfest (coefficient_pairing)
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V₀" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "R" => regularizer ε hε h hne hh m g k
local notation "A" => regularizerLift ε hε h hne hh m g k
local notation "S" => UnifiedTheory.Audit.KFCausalClockFloorMovingResolvent.derivative ε hε h hne hh m g k
local notation "G" => growingLift ε hε h hne hh m g k

def lift (a t : ℝ) : V₀ →L[ℂ] V₀ := (A a t).comp J

theorem lift_embedding (a t : ℝ) (x : V₀) :
    J (lift ε hε h hne hh m g k a t x) = R a t (J x) :=
  regularizerLift_embedding ε hε h hne hh m g k a t (J x)

theorem resolvent_form_real (a t : ℝ) (ha : 0 < a) (x : V₀) :
    inner ℂ x (Q t (lift ε hε h hne hh m g k a t x)) =
      conj (inner ℂ x (Q t (lift ε hε h hne hh m g k a t x))) := by
  have hr : conj (inner ℂ (J x-R a t (J x)) (J x)) = inner ℂ (J x-R a t (J x)) (J x) := by
    calc
      _ = inner ℂ (J x) (J x-R a t (J x)) := inner_conj_symm (𝕜 := ℂ) _ _
      _ = inner ℂ (J x) (J x)-inner ℂ (J x) (R a t (J x)) := inner_sub_right _ _ _
      _ = inner ℂ (J x) (J x)-inner ℂ (R a t (J x)) (J x) :=
        congrArg (fun c : ℂ => inner ℂ (J x) (J x)-c)
          (regularizer_symmetric ε hε h hne hh m g k a t ha (J x) (J x)).symm
      _ = _ := (inner_sub_left (𝕜 := ℂ) _ _ _).symm
  have hp : conj ((a:ℂ)*inner ℂ (J x-R a t (J x)) (J x)) =
      (a:ℂ)*inner ℂ (J x-R a t (J x)) (J x) :=
    (map_mul (starRingEnd ℂ) (a:ℂ) (inner ℂ (J x-R a t (J x)) (J x))).trans
      (congrArg₂ (fun b c : ℂ => b*c) (Complex.conj_ofReal a) hr)
  have he : inner ℂ x (Q t (lift ε hε h hne hh m g k a t x)) =
      (a:ℂ)*inner ℂ (J x-R a t (J x)) (J x) := by
    calc
      _ = conj (inner ℂ (lift ε hε h hne hh m g k a t x) (Q t x)) :=
        reference_form_hermitian ε hε h hne hh m g k t x _
      _ = conj ((a:ℂ)*inner ℂ (J x-R a t (J x)) (J x)) :=
        congrArg conj (regularizer_variational ε hε h hne hh m g k a t ha (J x) x)
      _ = _ := hp
  exact he.trans (hp.symm.trans (congrArg conj he.symm))

theorem frozen_resolvent_derivative (a : ℝ) (ha : 0 < a) (s t : ℝ) (w : V₀) :
    HasDerivAt (fun z => inner ℂ (U s z (J w)) (R a t (U s z (J w)))) 0 t := by
  let V := weakTrajectory ε hε h hne hh m g k s w
  let B := lift ε hε h hne hh m g k a t
  have hd := KFCausalComplexFormObservableDerivative.expectation_derivative J
    (R a t) (R a t) (massOperator ε hε h hne hh m g k) B B
    (mass_left_pairing ε hε h hne hh m g k)
    (lift_embedding ε hε h hne hh m g k a t)
    (lift_embedding ε hε h hne hh m g k a t)
    (regularizer_symmetric ε hε h hne hh m g k a t ha)
    V.formState (massSlope ε hε h hne hh m g k s w V t) t
    (massLipschitzBound ε hε h hne hh m g k s (|t|+1) w)
    (massLipschitzBound_nonneg ε hε h hne hh m g k s (|t|+1) w)
    (formFlow_continuous ε hε h hne hh m g k s w).continuousAt
    ?_ (mass_pairing_derivative ε hε h hne hh m g k s w V t)
  · have hr : inner ℂ (massSlope ε hε h hne hh m g k s w V t) (B (V.formState t))+
        conj (inner ℂ (massSlope ε hε h hne hh m g k s w V t) (B (V.formState t))) = 0 := by
      calc
        _ = coefficient h*(inner ℂ (V.formState t) (Q t (B (V.formState t)))-
            conj (inner ℂ (V.formState t) (Q t (B (V.formState t))))) := by
          simpa only [massSlope_pairing,limitSlope,coefficient] using
            coefficient_pairing h (inner ℂ (V.formState t) (Q t (B (V.formState t))))
              (inner ℂ (V.formState t) (Q t (B (V.formState t))))
        _ = 0 := by
          rw [sub_eq_zero.mpr (resolvent_form_real ε hε h hne hh m g k a t ha (V.formState t)),mul_zero]
    simpa only [KFCausalComplexFormObservableDerivative.expectation,evolution_embedding]
      using hd.congr_deriv hr
  · have he : ∀ᶠ z in 𝓝 (0:ℝ), |z| < 1 := by
      simpa only [abs_zero] using (continuous_abs.tendsto (0:ℝ)).eventually
        (gt_mem_nhds (by norm_num : |(0:ℝ)| < 1))
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with z hz
    have hsum : |t+z| ≤ |t|+|z| := abs_add_le _ _
    simpa only [add_sub_cancel_left] using
      massState_window_lipschitz ε hε h hne hh m g k s w V (|t|+1) t (t+z)
        (by positivity) (by linarith) (hsum.trans (by linarith))

theorem moving_resolvent_derivative (a : ℝ) (ha : 0 < a) (s t : ℝ) (w : V₀) :
    HasDerivAt (fun z => inner ℂ (U s z (J w)) (R a z (U s z (J w))))
      (inner ℂ (U s t (J w)) (S a t (U s t (J w)))) t := by
  simpa only [zero_add] using KFCausalMovingObservableDerivative.expectation_derivative
    (fun z => U s z (J w)) (R a) (S a t) t 0
    (evolution_strong_continuous ε hε h hne hh m g k s (J w)).continuousAt
    (regularizer_derivative ε hε h hne hh m g k a t ha)
    (frozen_resolvent_derivative ε hε h hne hh m g k a ha s t w)

theorem rate_pairing (a t : ℝ) (ha : 0 < a) (f : Hilbert) :
    -a*(inner ℂ f (S a t f)).re = 2*‖G a t f‖^2 := by
  have he := (derivative_symmetric ε hε h hne hh m g k a t ha f f).symm.trans
    (derivative_pairing ε hε h hne hh m g k a t ha f f)
  have hr := congrArg Complex.re he
  have hs : (inner ℂ (G a t f) (G a t f)).re = ‖G a t f‖^2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,
    Complex.neg_im,Complex.ofReal_im,neg_zero,zero_mul,sub_zero,hs] at hr
  calc
    _ = -a*(-(2/a)*‖G a t f‖^2) := congrArg (fun c : ℝ => -a*c) hr
    _ = _ := by field_simp [ha.ne']

theorem boundedEnergy_eq_regularizer (a t : ℝ) (f : Hilbert) :
    boundedEnergy ε hε h hne hh m g k a t f = a*(‖f‖^2-(inner ℂ f (R a t f)).re) := by
  unfold boundedEnergy UnifiedTheory.Audit.KFCausalSchrodingerEnergyEstimate.expectation
  rw [yosida_action]
  change (inner ℂ (a • (f-R a t f)) f).re = _
  rw [inner_smul_left_eq_smul,inner_sub_left]
  have hs : (inner ℂ f f).re = ‖f‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) f
  have hr : (inner ℂ (R a t f) f).re = (inner ℂ f (R a t f)).re :=
    inner_re_symm (𝕜 := ℂ) (R a t f) f
  simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.sub_re,hs,hr]

def value (a s t : ℝ) (w : V₀) : ℝ := boundedEnergy ε hε h hne hh m g k a t (U s t (J w))
def rate (a s t : ℝ) (w : V₀) : ℝ := 2*‖G a t (U s t (J w))‖^2

theorem value_derivative (a : ℝ) (ha : 0 < a) (s t : ℝ) (w : V₀) :
    HasDerivAt (fun z => value ε hε h hne hh m g k a s z w) (rate ε hε h hne hh m g k a s t w) t := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (moving_resolvent_derivative ε hε h hne hh m g k a ha s t w)
  have he : (fun z => value ε hε h hne hh m g k a s z w) =
      fun z => a*(‖J w‖^2-(inner ℂ (U s z (J w)) (R a z (U s z (J w)))).re) := by
    funext z
    exact (boundedEnergy_eq_regularizer ε hε h hne hh m g k a z (U s z (J w))).trans
      (congrArg (fun c : ℝ => a*(c^2-(inner ℂ (U s z (J w)) (R a z (U s z (J w)))).re))
        (evolution_norm ε hε h hne hh m g k s z (J w)))
  rw [he]
  convert (hd.const_sub (‖J w‖^2)).const_mul a using 1
  change 2*‖G a t (U s t (J w))‖^2 = a*(-(inner ℂ (U s t (J w)) (S a t (U s t (J w)))).re)
  nlinarith only [rate_pairing ε hε h hne hh m g k a t ha (U s t (J w))]

theorem rate_continuous (a : ℝ) (ha : 0 < a) (s : ℝ) (w : V₀) :
    Continuous (fun t => rate ε hε h hne hh m g k a s t w) := by
  have he : (fun t => rate ε hε h hne hh m g k a s t w) =
      fun t => -a*(inner ℂ (U s t (J w)) (S a t (U s t (J w)))).re := by
    funext t
    exact (rate_pairing ε hε h hne hh m g k a t ha (U s t (J w))).symm
  rw [he]
  have hu := evolution_strong_continuous ε hε h hne hh m g k s (J w)
  exact continuous_const.mul (Complex.continuous_re.comp
    (hu.inner (𝕜 := ℂ) ((derivative_continuous ε hε h hne hh m g k a ha).clm_apply hu)))

theorem value_integral (a : ℝ) (ha : 0 < a) (s r t : ℝ) (w : V₀) :
    (∫ z in r..t, rate ε hε h hne hh m g k a s z w) =
      value ε hε h hne hh m g k a s t w-value ε hε h hne hh m g k a s r w :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z _ => value_derivative ε hε h hne hh m g k a ha s z w)
    ((rate_continuous ε hε h hne hh m g k a ha s w).intervalIntegrable _ _)

#print axioms lift_embedding
#print axioms resolvent_form_real
#print axioms frozen_resolvent_derivative
#print axioms moving_resolvent_derivative
#print axioms rate_pairing
#print axioms boundedEnergy_eq_regularizer
#print axioms value_derivative
#print axioms rate_continuous
#print axioms value_integral
end
end UnifiedTheory.Audit.KFCausalClockFloorRegularizedEnergyBalance

/- A finite physical-time spectral exposure is bounded by the actual
clock-expectation drop for every Hilbert state, without an energy-domain
assumption. The bounded quadratic integral passes through Hilbert density. -/
import UnifiedTheory.Audit.KFCausalClockFloorFullTimeSpectrum
import UnifiedTheory.Audit.KFCausalStrongUnitaryContinuity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHilbertObservationBudget
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalClockFloorAveragedEvolution (evolution evolution_strong_continuous)
open KFCausalClockFloorLocalizedSpectrum (orbitObservation)
open KFCausalClockFloorDefectDissipationBudget (dissipation dissipation_continuous interval_budget)
open KFCausalClockFloorFrozenClockLoss (expectation)
open KFCausalClockFloorDefectOperator (defectOperator)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "U" => evolution ε hε h hne hb m g k
local notation "B" => orbitObservation ε hε h hne
local notation "X" => expectation ε hε

def exposure (R s a b : ℝ) (f : Hilbert) : ℝ :=
  ∫ t in a..b, Real.exp (2*t)*‖B R (U s t f)‖^2

def bound (R : ℝ) : ℝ := 2048*ε*Real.exp (-R)/k

theorem integrand_continuous (R s : ℝ) (f : Hilbert) :
    Continuous (fun t => Real.exp (2*t)*‖B R (U s t f)‖^2) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (((B R).continuous.comp (evolution_strong_continuous ε hε h hne hb m g k s f)).norm.pow 2)

theorem exposure_continuous (R s a b : ℝ) :
    Continuous (exposure ε hε h hne hb m g k R s a b) := by
  have hU := KFCausalStrongUnitaryContinuity.joint_evaluation_continuous
    (fun t => U s t) (evolution_strong_continuous ε hε h hne hb m g k s)
  have hc : Continuous (fun p : Hilbert × ℝ => Real.exp (2*p.2)*‖B R (U s p.2 p.1)‖^2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).mul
      (((B R).continuous.comp (hU.comp (continuous_snd.prodMk continuous_fst))).norm.pow 2)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc a b

theorem form_budget (hk : 0 < k) (R s a b : ℝ) (hab : a ≤ b) (v : V) :
    exposure ε hε h hne hb m g k R s a b (J v) ≤
      bound ε k R*(X (U s a (J v))-X (U s b (J v))) := by
  have hd := dissipation_continuous ε hε h hne hb m g k s v
  have hcd : Continuous (fun t => (64*ε*Real.exp (-R)/k)*dissipation ε hε h hne hb m g k s t v) :=
    continuous_const.mul hd
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    ((integrand_continuous ε hε h hne hb m g k R s (J v)).intervalIntegrable a b)
    (hcd.intervalIntegrable a b)
    (fun t _ => KFCausalClockFloorFullTimeSpectrum.detection_bound
      ε hε h hne hb m g k hk s t R v)
  rw [intervalIntegral.integral_const_mul] at hi
  have hbudget := mul_le_mul_of_nonneg_left (interval_budget ε hε h hne hb m g k s a b hab v)
    (show 0 ≤ 64*ε*Real.exp (-R)/k by positivity)
  exact hi.trans (hbudget.trans_eq (by
    unfold bound expectation KFCausalClockFloorDefectDissipationBudget.expectation
    ring))

theorem hilbert_budget (hk : 0 < k) (R s a b : ℝ) (hab : a ≤ b) (f : Hilbert) :
    exposure ε hε h hne hb m g k R s a b f ≤
      bound ε k R*(X (U s a f)-X (U s b f)) := by
  have hX : Continuous X :=
    Complex.continuous_re.comp (continuous_id.inner (defectOperator ε hε).continuous)
  have hr : Continuous (fun f : Hilbert => bound ε k R*(X (U s a f)-X (U s b f))) :=
    continuous_const.mul ((hX.comp (U s a).continuous).sub (hX.comp (U s b).continuous))
  exact (KFCausalClockFloorAveragedFormGeometry.embedding_dense ε hε h hne hb m g k 0).induction_on
    f (isClosed_le (exposure_continuous ε hε h hne hb m g k R s a b) hr)
    (form_budget ε hε h hne hb m g k hk R s a b hab)

theorem window_budget (hk : 0 < k) (R s a b : ℝ) (hab : a ≤ b) (f : Hilbert) :
    (∫ t in a..b, ‖B R (U s t f)‖^2) ≤
      (bound ε k R*Real.exp (-2*a))*(X (U s a f)-X (U s b f)) := by
  have hc := ((B R).continuous.comp (evolution_strong_continuous ε hε h hne hb m g k s f)).norm.pow 2
  have hcc : Continuous (fun t => Real.exp (2*a)*‖B R (U s t f)‖^2) := continuous_const.mul hc
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    (hcc.intervalIntegrable a b)
    ((integrand_continuous ε hε h hne hb m g k R s f).intervalIntegrable a b)
    (fun t ht => mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (show 2*a ≤ 2*t by linarith only [ht.1])) (sq_nonneg _))
  rw [intervalIntegral.integral_const_mul] at hi
  have hx := mul_le_mul_of_nonneg_left
    (hi.trans (hilbert_budget ε hε h hne hb m g k hk R s a b hab f))
    (Real.exp_pos (-2*a)).le
  have he : Real.exp (-2*a)*Real.exp (2*a) = 1 := by
    rw [← Real.exp_add,show -2*a+2*a = 0 by ring,Real.exp_zero]
  rw [← mul_assoc,he,one_mul] at hx
  exact hx.trans_eq (by ring)

theorem forward_budget (hk : 0 < k) (R s a b : ℝ) (hab : a ≤ b) (f : Hilbert) :
    exposure ε hε h hne hb m g k R s a b f ≤ bound ε k R*X (U s a f) := by
  have hx := KFCausalClockFloorStrictQuantumLimit.expectation_nonnegative ε hε (U s b f)
  exact (hilbert_budget ε hε h hne hb m g k hk R s a b hab f).trans
    (mul_le_mul_of_nonneg_left (sub_le_self _ hx) (by unfold bound; positivity))

#print axioms integrand_continuous
#print axioms exposure_continuous
#print axioms form_budget
#print axioms hilbert_budget
#print axioms window_budget
#print axioms forward_budget
end
end UnifiedTheory.Audit.KFCausalClockFloorHilbertObservationBudget

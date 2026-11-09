/- Actual clock-weighted radial moment outputs on the half-shifted line.
The clock multiplier is transported through the original mixed chart;
its spare Gaussian cancels against the actual narrower-clock output. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialMomentOutputRepresentative
import UnifiedTheory.Audit.KFCausalClockFloorOrderedStaticPacket

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialClockMomentRepresentative
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint split)
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalClockFloorMixedRadial (clockMixed clockMixed_relation)
open KFCausalClockWeightedIndependentHamiltonian (clockAction)
open KFCausalGaussianHolomorphicClockWeight (multiplier clockPower)
open KFCausalIndependentRadialMomentInput (numerator)
open KFCausalClockFloorOrderedStaticPacket (halfMoment clockMomentOutput)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalTwoShearClockQuotient (shift)

theorem clockAction_clockMixed (ε h a : ℝ) (hε : 0<ε) (ha : 0<a)
    (hb : |h|≤ε/10) (inverse : Bool) (y : ℝ) (hy : |y|≤|h|) (f : Hilbert) :
    clockMixed ε hε (clockAction ε h a hε ha hb inverse y hy f) =ᵐ[volume]
      fun x : Product => multiplier ε a inverse ((x.2 0:ℂ)+(y:ℂ)*Complex.I)*
        clockMixed ε hε f x := by
  have hm : Continuous (KFCausalAnalyticClockSecondTransport.line
      (multiplier ε a inverse) ε y) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (KFCausalGaussianHolomorphicClockWeight.multiplier_analytic ε h a inverse
      hε hb _ (by simpa using hy)).continuousAt.comp
      (((Complex.continuous_ofReal.comp
        (KFCausalRegularizedLongitudinalChart.chart_continuous ε)).add
          continuous_const).continuousAt)
  have ht : KFCausalPhysicalCircleAction.chargeCoordinates
      (clockAction ε h a hε ha hb inverse y hy f) =ᵐ[volume]
      fun x => KFCausalAnalyticClockSecondTransport.line (multiplier ε a inverse) ε y
        (x (.inr 0))*KFCausalPhysicalCircleAction.chargeCoordinates f x :=
    KFCausalBoundedClockCharge.multiplier_coordinates _ hm.measurable _
      (KFCausalGaussianHolomorphicClockWeight.bound_nonnegative ε h a inverse hε)
      (fun s => KFCausalGaussianHolomorphicClockWeight.multiplier_bound ε h a inverse
        hε hb ha _ (by simpa using hy)) f
  have hr := clockMixed_relation ε hε
    (fun x => KFCausalAnalyticClockSecondTransport.line (multiplier ε a inverse) ε y (x (.inr 0)))
    f (clockAction ε h a hε ha hb inverse y hy f) ht
  filter_upwards [hr] with x hx
  rw [hx]
  have hc : KFCausalRegularizedLongitudinalChart.chart ε
      ((KFCausalClockFloorMixedChart.mixedMap ε hε x).2 0)=x.2 0 :=
    (KFCausalRegularizedLongitudinalChart.chartIso ε hε).apply_symm_apply _
  change multiplier ε a inverse
      ((KFCausalRegularizedLongitudinalChart.chart ε
        ((KFCausalClockFloorMixedChart.mixedMap ε hε x).2 0):ℂ)+(y:ℂ)*Complex.I)*_=_
  rw [hc]

theorem numerator_clock_split (ε a α wL wR c : ℝ) (C : ℂ) (p : ℝ)
    (b : ℂ) (P : Polynomial ℂ) (m n : ℕ) (inverse : Bool) (q : ℂ) (x : Joint 2 4) :
    multiplier ε a inverse q*numerator ε (a/2) α wL wR c C p b P m n q x=
      clockPower ε inverse q*numerator ε a α wL wR c C p b P m n q x := by
  have he : Complex.exp (-((a/2:ℝ):ℂ)*q^2)*Complex.exp (-((a/2:ℝ):ℂ)*q^2)=
      Complex.exp (-(a:ℂ)*q^2) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold multiplier numerator
  dsimp only
  calc
    _ = clockPower ε inverse q *
        (KFCausalIndependentRadialMomentInput.left α wL
          (KFCausalIndependentRadialHolomorphicQuotient.baselineVector ε α wL wR c q x)^m *
         KFCausalIndependentRadialMomentInput.right α wR
          (KFCausalIndependentRadialHolomorphicQuotient.baselineVector ε α wL wR c q x)^n *
         ((Real.pi/α:ℝ)*C*KFCausalClockFloorCoherentStrip.clockPhase p
            (KFCausalComplexClockInverse.complexInverse ε q)*
          Complex.exp (-KFCausalComplexClockInverse.complexInverse ε q)*
          (Complex.exp (-((a/2:ℝ):ℂ)*q^2)*Complex.exp (-((a/2:ℝ):ℂ)*q^2))*
          Complex.exp (-KFCausalComplexQuadraticPerturbation.quadratic
            (fun i => KFCausalIndependentRadialHolomorphicQuotient.baselineVector ε α wL wR c q x i))*
          Complex.exp (b*KFCausalIndependentRadialMomentInput.neutral α
            (KFCausalIndependentRadialHolomorphicQuotient.baselineVector ε α wL wR c q x))*
          P.eval (KFCausalIndependentRadialMomentInput.neutral α
            (KFCausalIndependentRadialHolomorphicQuotient.baselineVector ε α wL wR c q x)))) := by ring
    _ = _ := by rw [he]

theorem halfMoment_clockMixed (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ)
    (b : ℂ) (P : Polynomial ℂ) (hε : 0<ε) (ha : 0<a) (hh : h≠0)
    (hL : 1≤wL) (hR : 1≤wR) (hb : |h|≤ε/10) (m n : ℕ) :
    clockMixed ε hε (halfMoment ε a h wL wR C p b P hε ha hh hL hR hb m n) =ᵐ[volume]
      fun x : Product => numerator ε a (groundWidth h) wL wR (momentumScale h)
        C p b P m n (shift (h/2) (x.2 0:ℂ)) ((split 2 4).symm x) := by
  simpa only [pow_zero,one_mul] using
    KFCausalIndependentRadialMomentOutputRepresentative.half_coe
      ε h a wL wL wR C p b P m n hε hh ha hL hR le_rfl hb 0

theorem clockMomentOutput_clockMixed (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ)
    (b : ℂ) (P : Polynomial ℂ) (hε : 0<ε) (ha : 0<a) (hh : h≠0)
    (hL : 1≤wL) (hR : 1≤wR) (hb : |h|≤ε/10) (inverse : Bool) (m n : ℕ) :
    clockMixed ε hε
      (clockMomentOutput ε a h wL wR C p b P hε ha hh hL hR hb inverse m n) =ᵐ[volume]
      fun x : Product => clockPower ε inverse (shift (h/2) (x.2 0:ℂ))*
        numerator ε a (groundWidth h) wL wR (momentumScale h) C p b P m n
          (shift (h/2) (x.2 0:ℂ)) ((split 2 4).symm x) := by
  have hs : |-h/2|≤|h| := by
    rw [abs_div,abs_neg,show |(2:ℝ)|=2 by norm_num]
    linarith [abs_nonneg h]
  filter_upwards [clockAction_clockMixed ε h a hε ha hb inverse (-h/2) hs
      (halfMoment ε (a/2) h wL wR C p b P hε (by positivity) hh hL hR hb m n),
    halfMoment_clockMixed ε (a/2) h wL wR C p b P hε (by positivity) hh hL hR hb m n]
    with x hx hm
  change clockMixed ε hε (clockMomentOutput ε a h wL wR C p b P hε ha hh hL hR hb inverse m n) x=_ at hx
  rw [hx,hm]
  have he : (x.2 0:ℂ)+(-h/2:ℝ)*Complex.I=shift (h/2) (x.2 0:ℂ) := by
    unfold shift
    push_cast
    ring
  rw [he]
  exact numerator_clock_split ε a (groundWidth h) wL wR (momentumScale h) C p b P m n inverse _ _

#print axioms clockAction_clockMixed
#print axioms numerator_clock_split
#print axioms halfMoment_clockMixed
#print axioms clockMomentOutput_clockMixed
end
end UnifiedTheory.Audit.KFCausalIndependentRadialClockMomentRepresentative

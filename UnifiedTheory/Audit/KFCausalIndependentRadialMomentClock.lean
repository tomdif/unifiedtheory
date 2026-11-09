/- Actual full-clock graphs for arbitrary radial polynomial moments.
The output is constructed by a bounded holomorphic multiplier on the
packet with half its clock Gaussian. Charge representatives identify it. -/
import UnifiedTheory.Audit.KFCausalClockWeightedIndependentHamiltonian
import UnifiedTheory.Audit.KFCausalIndependentRadialMomentCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialMomentClock
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalIndependentRadialPacketMoments (momentState momentState_charge_coe)
open KFCausalIndependentRadialPacketDerivatives (momentProfile)
open KFCausalIndependentRadialPacketProfiles (chargeProfile)
open KFCausalIndependentRadialPackets (clock)
open KFCausalGaussianHolomorphicClockWeight (multiplier physicalPower)
open KFCausalClockWeightedIndependentHamiltonian (clockAction)
open KFCausalRegularizedLongitudinalChart (chart)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorClockOperator (clockOperator)
open KFCausalStandingChargeOperator (zeroSector)

variable (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hL : 1 ≤ wL) (hR : 1 ≤ wR)
  (hb : |h| ≤ ε/10) (m n : ℕ)

def weightedState (inverse : Bool) : Hilbert :=
  clockAction ε h a hε ha hb inverse 0 (by simp)
    (momentState ε (a/2) h wL wR C p b P hε (by positivity) hh hL hR m n)

include hε in
theorem profile_split (inverse : Bool) (α β c : ℝ) (x : Joint 2 4) :
    multiplier ε a inverse (chart ε (x (.inr 0)):ℂ)*
      momentProfile α β wL wR c b P (clock ε (a/2) C p) m n x =
    physicalPower ε inverse (x (.inr 0))*
      momentProfile α β wL wR c b P (clock ε a C p) m n x := by
  have hc : Complex.exp (-((a/2:ℝ):ℂ)*(chart ε (x (.inr 0)):ℂ)^2)*
      KFCausalClockFloorInvariantTrial.clockFunction ε (a/2) (x (.inr 0)) =
      KFCausalClockFloorInvariantTrial.clockFunction ε a (x (.inr 0)) := by
    unfold KFCausalClockFloorInvariantTrial.clockFunction KFCausalClockFloorInvariantTrial.realClock
    push_cast
    rw [mul_left_comm,← Complex.exp_add]
    congr 2
    ring
  rw [multiplier,KFCausalGaussianHolomorphicClockWeight.clockPower_real ε inverse hε]
  unfold momentProfile chargeProfile clock
  calc
    _ = physicalPower ε inverse (x (.inr 0))*
      ((KFCausalIndependentRadialPacketDerivatives.leftRadius c x:ℂ)^m*
        (KFCausalIndependentRadialPacketDerivatives.rightRadius c x:ℂ)^n*
        (((Real.pi/α:ℝ):ℂ)*(C*KFCausalClockFloorCoherentStrip.clockPhase p (x (.inr 0):ℂ)*
          (Complex.exp (-((a/2:ℝ):ℂ)*(chart ε (x (.inr 0)):ℂ)^2)*
            KFCausalClockFloorInvariantTrial.clockFunction ε (a/2) (x (.inr 0))))*
          Complex.exp (-(α:ℂ)*(KFCausalIndependentRadialPacketProfiles.chargeQuadratic wL wR c x:ℂ))*
          KFCausalNeutralLinePackets.packet β b P (x (.inr 3)))) := by ring
    _ = _ := by rw [hc]

theorem weightedState_charge_coe (inverse : Bool) :
    chargeCoordinates (weightedState ε a h wL wR C p b P hε ha hh hL hR hb m n inverse) =ᵐ[volume]
      fun x => physicalPower ε inverse (x (.inr 0))*
        momentProfile (KFCausalChargeGaussianGeometry.groundWidth h)
          (KFCausalClockFloorInvariantTrial.neutralWidth h) wL wR
          (KFCausalNormalizedChargeFlow.momentumScale h) b P (clock ε a C p) m n x := by
  have ho : chargeCoordinates (weightedState ε a h wL wR C p b P hε ha hh hL hR hb m n inverse) =ᵐ[volume]
      fun x => KFCausalAnalyticClockSecondTransport.line (multiplier ε a inverse) ε 0 (x (.inr 0))*
        chargeCoordinates (momentState ε (a/2) h wL wR C p b P hε (by positivity) hh hL hR m n) x :=
    KFCausalBoundedClockCharge.multiplier_coordinates _ (by
      apply Continuous.measurable
      apply continuous_iff_continuousAt.mpr
      intro s
      exact (KFCausalGaussianHolomorphicClockWeight.multiplier_analytic ε h a inverse hε hb
        ((chart ε s:ℂ)+(0:ℂ)*Complex.I) (by simp)).continuousAt.comp
          (f := fun t : ℝ => (chart ε t:ℂ)+(0:ℂ)*Complex.I)
          (((Complex.continuous_ofReal.comp
            (KFCausalRegularizedLongitudinalChart.chart_continuous ε)).add continuous_const).continuousAt))
      _ (KFCausalGaussianHolomorphicClockWeight.bound_nonnegative ε h a inverse hε)
      (fun s => by
        simpa only [KFCausalAnalyticClockSecondTransport.line,Complex.ofReal_zero,zero_mul,add_zero] using
          KFCausalGaussianHolomorphicClockWeight.multiplier_bound ε h a inverse hε hb ha
            (chart ε s:ℂ) (by simp)) _
  filter_upwards [ho,momentState_charge_coe ε (a/2) h wL wR C p b P hε (by positivity) hh hL hR m n]
    with x hx hy
  rw [hx,hy]
  simpa only [KFCausalAnalyticClockSecondTransport.line,Complex.ofReal_zero,zero_mul,add_zero] using
    profile_split ε a wL wR C p b P hε m n inverse _ _ _ x

theorem weightedState_zeroSector (inverse : Bool) :
    weightedState ε a h wL wR C p b P hε ha hh hL hR hb m n inverse ∈ zeroSector h hh := by
  intro θ
  change KFCausalPhysicalCircleAction.action h hh θ
    (weightedState ε a h wL wR C p b P hε ha hh hL hR hb m n inverse) = _
  unfold weightedState clockAction
  rw [← KFCausalAnalyticClockSecondTransport.operator_charge]
  exact congrArg _ (KFCausalIndependentRadialMomentCharge.momentState_zeroSector
    ε (a/2) h wL wR C p b P hε (by positivity) hh hL hR m n θ)

theorem inverseL_sq_charge_coe (f : Hilbert) :
    chargeCoordinates (inverseL ε hε (inverseL ε hε f)) =ᵐ[volume]
      fun x => physicalPower ε true (x (.inr 0))*chargeCoordinates f x := by
  filter_upwards [KFCausalClockFloorAntisymmetricGraph.inverseL_charge_coe ε hε (inverseL ε hε f),
    KFCausalClockFloorAntisymmetricGraph.inverseL_charge_coe ε hε f] with x h2 h1
  rw [h2,h1,← mul_assoc,← pow_two,inv_pow,← Complex.ofReal_pow,
    Real.sq_sqrt (KFCausalClockFloorCanonicalDefect.clock_positive ε _ hε.le).le]
  rfl

theorem clock_graph :
    (momentState ε a h wL wR C p b P hε ha hh hL hR m n,
      weightedState ε a h wL wR C p b P hε ha hh hL hR hb m n false) ∈
        (clockOperator ε hε).graph := by
  apply (KFCausalClockMixedClockGraph.clockOperator_inverse_iff ε hε _ _).mpr
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [momentState_charge_coe ε a h wL wR C p b P hε ha hh hL hR m n,
    inverseL_sq_charge_coe ε hε (weightedState ε a h wL wR C p b P hε ha hh hL hR hb m n false),
    weightedState_charge_coe ε a h wL wR C p b P hε ha hh hL hR hb m n false] with x hf hd hg
  rw [hf,hd,hg]
  simp only [physicalPower,Bool.false_eq_true,ite_false,ite_true]
  rw [← mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (by positivity)),one_mul]

theorem inverse_state_eq :
    weightedState ε a h wL wR C p b P hε ha hh hL hR hb m n true =
      inverseL ε hε (inverseL ε hε (momentState ε a h wL wR C p b P hε ha hh hL hR m n)) := by
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [weightedState_charge_coe ε a h wL wR C p b P hε ha hh hL hR hb m n true,
    inverseL_sq_charge_coe ε hε (momentState ε a h wL wR C p b P hε ha hh hL hR m n),
    momentState_charge_coe ε a h wL wR C p b P hε ha hh hL hR m n] with x hw hd hf
  rw [hw,hd,hf]

theorem clock_component_graph :
    (momentState ε a h wL wR C p b P hε ha hh hL hR m n,
      weightedState ε a h wL wR C p b P hε ha hh hL hR hb m n false) ∈
        (KFCausalNaturalSecondHamiltonianGraph.component ε hε h 0).graph := by
  rw [KFCausalNaturalSecondHamiltonianGraph.component,KFCausalClockMixedClockGraph.actual_clockSecond_eq]
  exact clock_graph ε a h wL wR C p b P hε ha hh hL hR hb m n

#print axioms profile_split
#print axioms weightedState_charge_coe
#print axioms weightedState_zeroSector
#print axioms inverseL_sq_charge_coe
#print axioms clock_graph
#print axioms inverse_state_eq
#print axioms clock_component_graph
end
end UnifiedTheory.Audit.KFCausalIndependentRadialMomentClock

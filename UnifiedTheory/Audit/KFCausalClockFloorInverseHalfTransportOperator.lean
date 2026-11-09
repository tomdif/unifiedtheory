/- Operator-norm differentiation of the actual inverse half-clock under
longitudinal transport, with its explicit bounded drift. -/
import UnifiedTheory.Audit.KFCausalClockFloorInverseHalfTransportScalar
import UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
import UnifiedTheory.Audit.KFCausalClockFloorLpTransport
import UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse
import UnifiedTheory.Audit.KFCausalLpMultiplierDerivative
import UnifiedTheory.Audit.KFCausalQuadraticRemainderDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorInverseHalfTransportOperator
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorInverseHalfTransportScalar
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (inverseAction_coe)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryTransport
open UnifiedTheory.Audit.KFCausalClockFloorLpTransport
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect response)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart

variable (ε : ℝ) (hε : 0 < ε)

def weight (t : ℝ) (x : Configuration) : ℂ := (transported ε hε x.1 t:ℂ)

theorem weight_measurable (t : ℝ) : Measurable (weight ε hε t) := by
  have hc : Continuous (fun x : Configuration => logFlow ε hε x.1 t) :=
    (chartIso ε hε).symm.toHomeomorph.continuous.comp
      (((chart_continuous ε).comp continuous_fst).add continuous_const)
  unfold weight transported value KFCausalClockFloorFlow.clock
  exact Complex.measurable_ofReal.comp
    ((Real.continuous_sqrt.comp ((Real.continuous_exp.comp hc).add continuous_const)).measurable.inv)

theorem weight_bound (t : ℝ) (x : Configuration) : ‖weight ε hε t x‖ ≤ bound ε := by
  rw [weight,Complex.norm_real,Real.norm_eq_abs,transported,abs_of_pos (value_bounds ε _ hε).1]
  exact (value_bounds ε _ hε).2

def operator (t : ℝ) : Hilbert →L[ℂ] Hilbert :=
  KFCausalBoundedLpMultiplier.operator (weight ε hε t) (weight_measurable ε hε t)
    (bound ε) (by unfold bound; positivity) (weight_bound ε hε t)

def driftOperator : Hilbert →L[ℂ] Hilbert :=
  (-(1/(2*ε)):ℂ) • (defectOperator ε hε).comp
    ((responseOperator ε hε).comp (inverseL ε hε))

theorem operator_coe (t : ℝ) (f : Hilbert) :
    operator ε hε t f =ᵐ[volume] fun x => weight ε hε t x*f x :=
  KFCausalBoundedLpMultiplier.operator_coe _ _ _ _ _ f

theorem inverseL_coe (f : Hilbert) :
    inverseL ε hε f =ᵐ[volume] fun x => (value ε x.1:ℂ)*f x := by
  simpa only [value,KFCausalClockFloorFlow.clock,Complex.ofReal_inv] using inverseAction_coe ε hε f

theorem operator_initial : operator ε hε 0 = inverseL ε hε := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [operator_coe ε hε 0 f,inverseL_coe ε hε f] with x ht hr
  rw [ht,hr,weight,transported_initial]

theorem driftOperator_coe (f : Hilbert) :
    driftOperator ε hε f =ᵐ[volume] fun x => (drift ε (value ε x.1):ℂ)*f x := by
  let D := defectOperator ε hε
  let Q := responseOperator ε hε
  let R := inverseL ε hε
  change (-(1/(2*ε)):ℂ) • D (Q (R f)) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_smul (-(1/(2*ε)):ℂ) (D (Q (R f))),
    defectOperator_coe ε hε (Q (R f)),responseOperator_coe ε hε (R f),inverseL_coe ε hε f]
    with x hs hd hq hr
  change D (Q (R f)) x = _ at hd
  change Q (R f) x = _ at hq
  change R f x = _ at hr
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hd,hq,hr,drift_identity ε _ hε,
    Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_ofNat,mul_assoc]

theorem transport_inverseL (t : ℝ) (f : Hilbert) :
    transport ε hε t (inverseL ε hε f) = operator ε hε t (transport ε hε t f) := by
  apply Lp.ext
  filter_upwards [transport_coe ε hε t (inverseL ε hε f),
    operator_coe ε hε t (transport ε hε t f),transport_coe ε hε t f,
    (flow_quasiMeasurePreserving ε hε t).ae (inverseL_coe ε hε f)] with x hl hr hu hf
  rw [hl,hr]
  simp only [transportFunction]
  rw [hf,hu]
  dsimp only [transportFunction,weight,transported,KFCausalClockFloorFlow.coupledFlow]
  ring

theorem operator_remainder (t : ℝ) :
    ‖operator ε hε t-operator ε hε 0-t • driftOperator ε hε‖ ≤
      (slopeBound ε*speedBound ε)*t^2 := by
  apply KFCausalLpMultiplierDerivative.remainder_bound
    (operator ε hε) (driftOperator ε hε) (weight ε hε)
    (fun x : Configuration => (drift ε (value ε x.1):ℂ))
    (operator_coe ε hε) (driftOperator_coe ε hε)
    (slopeBound ε*speedBound ε) (by unfold slopeBound speedBound bound; positivity) ?_ t
  intro u x
  have he : weight ε hε u x-weight ε hε 0 x-(u:ℂ)*(drift ε (value ε x.1):ℂ) =
      ((transported ε hε x.1 u-value ε x.1-u*drift ε (value ε x.1):ℝ):ℂ) := by
    simp only [weight,transported_initial,Complex.ofReal_sub,Complex.ofReal_mul]
  rw [he,Complex.norm_real,Real.norm_eq_abs]
  exact transported_remainder ε hε x.1 u

theorem operator_derivative :
    HasDerivAt (fun t => (operator ε hε t).restrictScalars ℝ)
      ((driftOperator ε hε).restrictScalars ℝ) 0 := by
  apply KFCausalQuadraticRemainderDerivative.derivative_of_quadratic_remainder _ _
    (slopeBound ε*speedBound ε)
  intro t
  apply ContinuousLinearMap.opNorm_le_bound _ (by unfold slopeBound speedBound bound; positivity)
  intro f
  change ‖operator ε hε t f-operator ε hε 0 f-t • driftOperator ε hε f‖ ≤ _
  calc
    _ ≤ ‖operator ε hε t-operator ε hε 0-t • driftOperator ε hε‖*‖f‖ :=
      ContinuousLinearMap.le_opNorm _ f
    _ ≤ _ := by
      simpa only [sq_abs] using mul_le_mul_of_nonneg_right (operator_remainder ε hε t) (norm_nonneg f)

#print axioms weight_measurable
#print axioms weight_bound
#print axioms operator_coe
#print axioms inverseL_coe
#print axioms operator_initial
#print axioms driftOperator_coe
#print axioms transport_inverseL
#print axioms operator_remainder
#print axioms operator_derivative
end
end UnifiedTheory.Audit.KFCausalClockFloorInverseHalfTransportOperator

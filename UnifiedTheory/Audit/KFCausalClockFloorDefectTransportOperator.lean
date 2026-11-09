/- Operator-norm differentiation of the bounded clock defect under the
actual complete longitudinal transport. The multiplier identity holds on
the entire physical L2 space. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar
import UnifiedTheory.Audit.KFCausalQuadraticRemainderDerivative
import UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
import UnifiedTheory.Audit.KFCausalClockFloorLpTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectTransportOperator
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryTransport
open UnifiedTheory.Audit.KFCausalClockFloorLpTransport
open UnifiedTheory.Audit.KFCausalContractiveMultiplier
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalQuadraticRemainderDerivative

def transportedWeight (ε : ℝ) (hε : 0 < ε) (t : ℝ) (x : Configuration) : ℂ :=
  (transported ε hε x.1 t : ℂ)

theorem transportedWeight_measurable (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    Measurable (transportedWeight ε hε t) := by
  have hc : Continuous (fun x : Configuration => logFlow ε hε x.1 t) :=
    (chartIso ε hε).symm.toHomeomorph.continuous.comp
      (((chart_continuous ε).comp continuous_fst).add continuous_const)
  unfold transportedWeight transported defect KFCausalClockFloorFlow.clock
  exact Complex.measurable_ofReal.comp
    (measurable_const.div ((Real.continuous_exp.comp hc).measurable.add measurable_const))

theorem transportedWeight_bound (ε : ℝ) (hε : 0 < ε) (t : ℝ) (x : Configuration) :
    ‖transportedWeight ε hε t x‖ ≤ 1 := by
  rw [transportedWeight,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (transported_bounds ε hε x.1 t).1]
  exact (transported_bounds ε hε x.1 t).2

def transportedOperator (ε : ℝ) (hε : 0 < ε) (t : ℝ) : Hilbert →L[ℂ] Hilbert :=
  multiplyL (transportedWeight ε hε t) (transportedWeight_measurable ε hε t)
    (transportedWeight_bound ε hε t)

def driftOperator (ε : ℝ) (hε : 0 < ε) : Hilbert →L[ℂ] Hilbert :=
  (-(1/ε) : ℂ) • (defectOperator ε hε).comp
    ((defectOperator ε hε).comp (ContinuousLinearMap.id ℂ Hilbert-defectOperator ε hε))

theorem transportedOperator_coe (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Hilbert) :
    transportedOperator ε hε t f =ᵐ[volume] fun x => (transported ε hε x.1 t:ℂ)*f x :=
  multiplyL_coe _ _ _ f

theorem transportedOperator_initial (ε : ℝ) (hε : 0 < ε) :
    transportedOperator ε hε 0 = defectOperator ε hε := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [transportedOperator_coe ε hε 0 f,defectOperator_coe ε hε f] with x ht hd
  rw [ht,hd,transported_initial]

theorem driftOperator_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    driftOperator ε hε f =ᵐ[volume] fun x => (drift ε (defect ε x.1):ℂ)*f x := by
  let D := defectOperator ε hε
  change (-(1/ε):ℂ) • D (D (f-D f)) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_smul (-(1/ε):ℂ) (D (D (f-D f))),
    defectOperator_coe ε hε (D (f-D f)),defectOperator_coe ε hε (f-D f),
    Lp.coeFn_sub f (D f),defectOperator_coe ε hε f] with x hs hdd hd hsub hf
  change D (D (f-D f)) x = _ at hdd
  change D (f-D f) x = _ at hd
  change D f x = _ at hf
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hdd,hd,hsub,Pi.sub_apply,hf,
    drift,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_mul,
    Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow]
  ring

theorem transport_defect (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Hilbert) :
    transport ε hε t (defectOperator ε hε f) =
      transportedOperator ε hε t (transport ε hε t f) := by
  apply Lp.ext
  filter_upwards [transport_coe ε hε t (defectOperator ε hε f),
    transportedOperator_coe ε hε t (transport ε hε t f),transport_coe ε hε t f,
    (flow_quasiMeasurePreserving ε hε t).ae (defectOperator_coe ε hε f)] with x hl hr hu hd
  rw [hl,hr]
  simp only [transportFunction]
  rw [hd,hu]
  dsimp only [transportFunction,transported,KFCausalClockFloorFlow.coupledFlow]
  ring

theorem transportedOperator_remainder (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Hilbert) :
    ‖transportedOperator ε hε t f-defectOperator ε hε f-t • driftOperator ε hε f‖ ≤
      ((5/ε^2)*|t|^2)*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (transportedOperator ε hε t f-defectOperator ε hε f)
      (t • driftOperator ε hε f),
    Lp.coeFn_sub (transportedOperator ε hε t f) (defectOperator ε hε f),
    Lp.coeFn_smul t (driftOperator ε hε f),
    transportedOperator_coe ε hε t f,defectOperator_coe ε hε f,driftOperator_coe ε hε f]
    with x hs hs' hm ht hd hb
  rw [hs]
  simp only [Pi.sub_apply,hs',hm,Pi.smul_apply,ht,hd,hb,Complex.real_smul]
  have he : (transported ε hε x.1 t:ℂ)*f x-(defect ε x.1:ℂ)*f x-
      (t:ℂ)*((drift ε (defect ε x.1):ℂ)*f x) =
      ((transported ε hε x.1 t-defect ε x.1-t*drift ε (defect ε x.1):ℝ):ℂ)*f x := by
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (transported_remainder ε hε x.1 t) (norm_nonneg _)

theorem transportedOperator_derivative (ε : ℝ) (hε : 0 < ε) :
    HasDerivAt (fun t => (transportedOperator ε hε t).restrictScalars ℝ)
      ((driftOperator ε hε).restrictScalars ℝ) 0 := by
  apply derivative_of_quadratic_remainder _ _ (5/ε^2)
  intro t
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖transportedOperator ε hε t f-transportedOperator ε hε 0 f-t • driftOperator ε hε f‖ ≤ _
  rw [transportedOperator_initial]
  exact transportedOperator_remainder ε hε t f

#print axioms transportedWeight_measurable
#print axioms transportedWeight_bound
#print axioms transportedOperator_coe
#print axioms transportedOperator_initial
#print axioms driftOperator_coe
#print axioms transport_defect
#print axioms transportedOperator_remainder
#print axioms transportedOperator_derivative

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectTransportOperator

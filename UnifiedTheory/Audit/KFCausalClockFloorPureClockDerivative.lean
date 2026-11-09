/- Differential expression of the actual pure-clock unitary flow. The
half-density term is essential: the momentum is symmetrized inverse-clock
canonical momentum, not simply inverse-clock multiplication after P. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockTransport
import UnifiedTheory.Audit.KFCausalClockFloorInverseHalfTransportScalar
import UnifiedTheory.Audit.KFCausalCanonicalClockDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockDerivative
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect response clock_positive)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorPureClockLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorPureClockTransport
open UnifiedTheory.Audit.KFCausalClockFloorInverseHalfTransportScalar
open UnifiedTheory.Audit.KFCausalCanonicalClockDerivative (clockDerivative)

def rate (ε s : ℝ) : ℝ := -Real.exp s/(2*(clock ε s)^2)
def densityRatio (ε : ℝ) (hε : 0 < ε) (s t : ℝ) : ℝ :=
  Real.sqrt (clock ε s)*transported ε hε s t

theorem densityRatio_initial (ε : ℝ) (hε : 0 < ε) (s : ℝ) : densityRatio ε hε s 0 = 1 := by
  rw [densityRatio,transported_initial,value,mul_inv_cancel₀
    (Real.sqrt_pos.mpr (clock_positive ε s hε.le)).ne']

theorem densityRatio_derivative (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    HasDerivAt (densityRatio ε hε s) (rate ε s) 0 := by
  have hc := (clock_positive ε s hε.le).ne'
  have hr := (Real.sqrt_pos.mpr (clock_positive ε s hε.le)).ne'
  convert (transported_derivative ε hε s 0).const_mul (Real.sqrt (clock ε s)) using 1
  rw [transported_initial,drift_identity ε s hε]
  unfold rate defect response value
  field_simp

def expression (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Configuration → ℂ) (x : Configuration) : ℂ :=
  (densityRatio ε hε x.1 t:ℂ)*f (pureFlow ε hε t x)

def differential (ε : ℝ) (f : Configuration → ℂ) (x : Configuration) : ℂ :=
  ((clock ε x.1)⁻¹:ℂ)*clockDerivative f x+(rate ε x.1:ℂ)*f x

theorem expression_transport (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Configuration → ℂ) :
    expression ε hε t f = transportFunction ε hε t f := by
  funext x
  simp only [expression,transportFunction,densityRatio,transported,value,weight,pureFlow,clock,
    Complex.ofReal_mul,Complex.ofReal_inv,mul_assoc]

theorem expression_derivative (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (x : Configuration) (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t => expression ε hε t f x) (differential ε f x) 0 := by
  have hp := (densityRatio_derivative ε hε x.1).ofReal_comp
  have hfx : HasFDerivAt f (fderiv ℝ f x) (pureFlow ε hε 0 x) := by
    simpa only [pureFlow_initial] using hf.hasFDerivAt
  have hq := hfx.comp_hasDerivAt 0 (pureFlow_derivative ε hε 0 x)
  have hh := hp.mul hq
  simp only [Function.comp_apply,pureFlow_initial,densityRatio_initial,Complex.ofReal_one,
    one_mul,logFlow_initial] at hh
  convert hh using 1
  rw [show ((1/(Real.exp x.1+ε),0):Configuration) =
    (clock ε x.1)⁻¹ • ((1,0):Configuration) by simp [clock,Prod.smul_mk,one_div]]
  rw [map_smul]
  simp only [differential,clockDerivative,Complex.real_smul,Complex.ofReal_inv]
  ring

theorem inverse_shift (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) (t : ℝ)
    (x : Configuration) :
    inverseFunction ε hε f (KFCausalConfigurationTranslation.clockShift t x) =
      (weight ε ((chartHomeomorph ε hε).symm x))⁻¹*
        expression ε hε t f ((chartHomeomorph ε hε).symm x) := by
  have hi := inverse_shift_coordinates ε hε t ((chartHomeomorph ε hε).symm x)
  rw [Homeomorph.apply_symm_apply] at hi
  unfold inverseFunction
  rw [hi,expression_transport]
  simp only [transportFunction,← mul_assoc,inv_mul_cancel₀ (weight_ne_zero ε hε _),one_mul]

theorem inverse_clock_derivative (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (hf : Differentiable ℝ f) (x : Configuration) :
    HasDerivAt (fun t => inverseFunction ε hε f (KFCausalConfigurationTranslation.clockShift t x))
      (inverseFunction ε hε (differential ε f) x) 0 := by
  have hd := (expression_derivative ε hε f ((chartHomeomorph ε hε).symm x)
    (hf _)).const_mul (weight ε ((chartHomeomorph ε hε).symm x))⁻¹
  simpa only [← inverse_shift,inverseFunction] using hd

theorem longitudinal_split (ε : ℝ) (f : Configuration → ℂ) (x : Configuration) :
    KFCausalClockFloorDifferentialMomentum.differential ε f x = differential ε f x+
      ((clock ε x.1)⁻¹:ℂ)*(fderiv ℝ f x ((0,KFCausalTransverseDilationFlow.velocity x.2):Configuration)+f x) := by
  rw [KFCausalClockFloorDifferentialMomentum.differential,
    KFCausalClockFloorTransportDerivative.coupledVelocity_split,map_add,map_smul,map_smul]
  simp only [differential,clockDerivative,rate,KFCausalClockFloorTransportDerivative.rate,
    clock,Complex.real_smul]
  push_cast
  ring

#print axioms densityRatio_initial
#print axioms densityRatio_derivative
#print axioms expression_transport
#print axioms expression_derivative
#print axioms inverse_shift
#print axioms inverse_clock_derivative
#print axioms longitudinal_split
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockDerivative

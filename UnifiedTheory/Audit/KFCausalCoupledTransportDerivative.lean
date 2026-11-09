/- Pointwise infinitesimal expression of the constructed longitudinal
transport on differentiable tests, including the half-density correction.
This is not yet an L2 strong-derivative or self-adjoint-domain theorem. -/
import UnifiedTheory.Audit.KFCausalCoupledUnitaryTransport
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoupledTransportDerivative
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
open UnifiedTheory.Audit.KFCausalCoupledTestPullback
open UnifiedTheory.Audit.KFCausalCoupledUnitaryTransport

def amplitudeLogSlope (ε s : ℝ) : ℝ :=
  Real.exp s/(2*(Real.exp s+ε))-(1+ε*Real.exp (-s))

theorem amplitude_derivative (ε s : ℝ) (hε : 0 < ε) :
    HasDerivAt (amplitude ε) (amplitude ε s*amplitudeLogSlope ε s) s := by
  have hj : 0 < Real.exp s+ε := by positivity
  have hr : Real.sqrt (Real.exp s+ε) ≠ 0 := (Real.sqrt_pos.mpr hj).ne'
  have hs := Real.sq_sqrt hj.le
  have he : Real.exp s/(2*Real.sqrt (Real.exp s+ε)) =
      Real.sqrt (Real.exp s+ε)*(Real.exp s/(2*(Real.exp s+ε))) := by
    field_simp
    nlinarith [congrArg (fun z => Real.exp s*z) hs]
  have hh := (((Real.hasDerivAt_exp s).add_const ε).sqrt hj.ne').mul
    ((phase_derivative ε s).neg.exp)
  convert hh using 1
  rw [he]
  unfold amplitude amplitudeLogSlope
  simp only [Pi.neg_apply]
  ring

def rate (ε s : ℝ) : ℝ :=
  Real.exp (-s)-Real.exp s/(2*(Real.exp s+ε)^2)

theorem rate_identity (ε s : ℝ) (hε : 0 < ε) :
    -amplitudeLogSlope ε s/(Real.exp s+ε) = rate ε s := by
  have hj : Real.exp s+ε ≠ 0 := by positivity
  have hh := phase_velocity ε s hε
  unfold amplitudeLogSlope rate
  calc
    _ = (1+ε*Real.exp (-s))/(Real.exp s+ε)-Real.exp s/(2*(Real.exp s+ε)^2) := by
      field_simp
      ring
    _ = _ := by rw [hh]

def densityRatio (ε : ℝ) (hε : 0 < ε) (s t : ℝ) : ℝ :=
  amplitude ε s/amplitude ε (logFlow ε hε s t)

theorem densityRatio_initial (ε : ℝ) (hε : 0 < ε) (s : ℝ) : densityRatio ε hε s 0 = 1 := by
  rw [densityRatio,logFlow_initial,div_self (amplitude_positive ε s hε).ne']

theorem densityRatio_derivative (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    HasDerivAt (densityRatio ε hε s) (rate ε s) 0 := by
  have ht : HasDerivAt (logFlow ε hε s) (1/(Real.exp s+ε)) 0 := by
    simpa only [clockFlow,logFlow_initial] using logFlow_derivative ε hε s 0
  have ha : HasDerivAt (fun t => amplitude ε (logFlow ε hε s t))
      ((amplitude ε s*amplitudeLogSlope ε s)*(1/(Real.exp s+ε))) 0 := by
    simpa only [logFlow_initial] using
      (amplitude_derivative ε (logFlow ε hε s 0) hε).comp 0 ht
  have hn : amplitude ε (logFlow ε hε s 0) ≠ 0 := (amplitude_positive ε _ hε).ne'
  have hA : amplitude ε s ≠ 0 := (amplitude_positive ε s hε).ne'
  have hh := (hasDerivAt_const 0 (amplitude ε s)).div ha hn
  convert hh using 1
  rw [logFlow_initial,← rate_identity ε s hε]
  field_simp
  ring

def expression (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Configuration → ℂ)
    (x : Configuration) : ℂ := (densityRatio ε hε x.1 t:ℂ)*f (coupledFlow ε hε t x)

theorem testTransport_expression (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Test) (x : Configuration) :
    testTransport ε hε t f x = expression ε hε t f x := by
  rw [testTransport_apply]
  simp only [expression,densityRatio,weight,coupledFlow,div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv,mul_assoc]

theorem expression_derivative (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (x : Configuration) (f' : Configuration →L[ℝ] ℂ) (hf : HasFDerivAt f f' x) :
    HasDerivAt (fun t => expression ε hε t f x)
      ((rate ε x.1:ℂ)*f x+f' (coupledVelocity ε x)) 0 := by
  have hp := (densityRatio_derivative ε hε x.1).ofReal_comp
  have hfx : HasFDerivAt f f' (coupledFlow ε hε 0 x) := by
    simpa only [coupledFlow_initial] using hf
  have hq := hfx.comp_hasDerivAt 0 (coupledFlow_derivative ε hε 0 x)
  have hh := hp.mul hq
  simpa only [Function.comp_apply,expression,coupledFlow_initial,densityRatio_initial,Complex.ofReal_one,one_mul] using hh

def momentumExpression (ε hbar : ℝ) (f : Configuration → ℂ)
    (f' : Configuration →L[ℝ] ℂ) (x : Configuration) : ℂ :=
  -Complex.I*(hbar:ℂ)*((rate ε x.1:ℂ)*f x+f' (coupledVelocity ε x))

theorem infinitesimal_momentum (ε hbar : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (x : Configuration) (f' : Configuration →L[ℝ] ℂ) (hf : HasFDerivAt f f' x) :
    -Complex.I*(hbar:ℂ)*deriv (fun t => expression ε hε t f x) 0 =
      momentumExpression ε hbar f f' x := by
  rw [(expression_derivative ε hε f x f' hf).deriv]
  rfl

theorem coupledVelocity_split (ε : ℝ) (x : Configuration) :
    coupledVelocity ε x = (Real.exp x.1+ε)⁻¹ • ((1,0):Configuration) +
      Real.exp (-x.1) • ((0,velocity x.2):Configuration) := by
  simp [coupledVelocity,Prod.smul_mk,Prod.add_def]

theorem momentumExpression_split (ε hbar : ℝ) (f : Configuration → ℂ)
    (f' : Configuration →L[ℝ] ℂ) (x : Configuration) :
    momentumExpression ε hbar f f' x =
      -Complex.I*(hbar:ℂ)*
        (((Real.exp x.1+ε)⁻¹:ℝ) • f' ((1,0):Configuration) -
          (Real.exp x.1/(2*(Real.exp x.1+ε)^2):ℂ)*f x) +
      (Real.exp (-x.1):ℂ)*(-Complex.I*(hbar:ℂ)*(f' ((0,velocity x.2):Configuration)+f x)) := by
  rw [momentumExpression,coupledVelocity_split,map_add,map_smul,map_smul]
  simp only [rate,Complex.ofReal_sub,Complex.real_smul]
  push_cast
  ring

#print axioms amplitude_derivative
#print axioms rate_identity
#print axioms densityRatio_derivative
#print axioms testTransport_expression
#print axioms expression_derivative
#print axioms infinitesimal_momentum
#print axioms coupledVelocity_split
#print axioms momentumExpression_split

end
end UnifiedTheory.Audit.KFCausalCoupledTransportDerivative

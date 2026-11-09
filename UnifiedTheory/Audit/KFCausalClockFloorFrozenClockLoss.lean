/- Exact clock-defect expectation dynamics and an integrated positive
output budget for the actual full frozen flow in exponential time. -/
import UnifiedTheory.Audit.KFCausalMassObservableDerivative
import UnifiedTheory.Audit.KFCausalClockFloorFrozenFastEvolution
import UnifiedTheory.Audit.KFCausalClockFloorReferenceDefect
import UnifiedTheory.Audit.KFCausalClockFloorClockReferenceRate
import UnifiedTheory.Audit.KFCausalClockFloorDefectProductionCoercivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFrozenClockLoss
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalClockFloorAveragedRegularity (referenceFormOperator staticMap growingMap)
open KFCausalClockFloorFastTimeEnergy (physicalTime)
open KFCausalClockFloorReferenceDefect (formDefect formDefect_embedding reference_defect_pairing)
open KFCausalClockFloorDefectOperator (defectOperator)
open KFCausalClockFloorClockReferenceRate (output output_actual)

private theorem rate_algebra (h U : ℝ) (z : ℂ) :
    2*(starRingEnd ℂ (-Complex.I*((1/(2*h*U):ℝ):ℂ))*z).re=((-2/h)*z.im)/(2*U) := by
  simp only [map_mul,map_neg,Complex.conj_I,Complex.conj_ofReal,neg_neg,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,one_mul,mul_zero,sub_zero,zero_add,zero_sub]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

private theorem vector_rate {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (h U : ℝ) (x y : K) :
    2*(inner ℂ ((-Complex.I*((1/(2*h*U):ℝ):ℂ)) • x) y).re=((-2/h)*(inner ℂ x y).im)/(2*U) := by
  rw [inner_smul_left]
  exact rate_algebra h U _

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "D" => defectOperator ε hε
local notation "R" => formDefect ε hε h hne hb m g k 0
local notation "F" => KFCausalClockFloorFrozenFastEvolution.evolution ε hε h hne hb m g k
local notation "P" => KFCausalClockFloorFrozenFastEvolution.physical ε hε h hne hb m g k
local notation "Q" => referenceFormOperator ε hε h hne hb m g k
local notation "A" => KFCausalClockFloorEnergyDefectAction.outputAction ε hε h hb
local notation "C" => KFCausalClockFloorQuantumVelocityOutput.classicalOutput ε hε

def expectation (f : Hilbert) : ℝ := (inner ℂ f (D f)).re

def frozenOutput (U t : ℝ) (v : V) := output ε hε h hne hb m g k (physicalTime U) (F U t v)
local notation "O" => frozenOutput ε hε h hne hb m g k

def rate (U t : ℝ) (v : V) : ℝ := ((-2/h)*(inner ℂ (O U t v) ((A).compLp (O U t v))).im)/(2*U)
def dissipation (U t : ℝ) (v : V) : ℝ := -(inner ℂ (O U t v) ((C).compLp (O U t v))).re/(2*U)
local notation "r" => rate ε hε h hne hb m g k
local notation "d" => dissipation ε hε h hne hb m g k

theorem output_continuous (U : ℝ) (v : V) : Continuous (fun t => O U t v) := by
  let A0 := KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hne hb m g k 0
  let T := KFCausalClockFloorAveragedOutputTransport.timeOutputLp 0 (physicalTime U)
  change Continuous (fun t => T (A0 (F U t v)))
  exact T.continuous.comp (f := fun t => A0 (F U t v))
    (A0.continuous.comp (f := fun t => F U t v)
      (KFCausalClockFloorFrozenFastEvolution.evolution_continuous ε hε h hne hb m g k U v))

theorem expectation_derivative (U t : ℝ) (v : V) :
    HasDerivAt (fun s => expectation ε hε (P U s (J v))) (r U t v) t := by
  have hd := KFCausalMassObservableDerivative.expectation_derivative J D R
    (formDefect_embedding ε hε h hne hb m g k 0)
    (KFCausalClockFloorDefectForm.defect_inner ε hε) (fun s => F U s v)
    ((-Complex.I*((1/(2*h*U):ℝ):ℂ)) • Q (physicalTime U) (F U t v)) t
    (KFCausalClockFloorFrozenFastEvolution.evolution_continuous ε hε h hne hb m g k U v).continuousAt
    (KFCausalClockFloorFrozenReferenceEvolution.mass_derivative ε hε h hne hb m g k
      (physicalTime U) (1/(2*h*U)) v t)
  have hp : inner ℂ (Q (physicalTime U) (F U t v)) (R (F U t v))=
      inner ℂ (O U t v) ((A).compLp (O U t v)) := by
    have hs := KFCausalShiftedForm.formOperator_inner_symm (staticMap ε hε h hne hb m g k)
      (growingMap ε hε h hne hb m g k) (physicalTime U) (F U t v) (R (F U t v))
    have hp := reference_defect_pairing ε hε h hne hb m g k (physicalTime U) (F U t v)
    have ho := output_actual ε hε h hne hb m g k (physicalTime U) (F U t v)
    exact hs.trans (hp.trans (congrArg (fun z => inner ℂ z ((A).compLp z)) ho.symm))
  have he : 2*(inner ℂ ((-Complex.I*((1/(2*h*U):ℝ):ℂ)) • Q (physicalTime U) (F U t v))
      (R (F U t v))).re=r U t v := by
    exact (vector_rate h U _ _).trans (congrArg (fun z : ℂ => ((-2/h)*z.im)/(2*U)) hp)
  have hc := hd.congr_deriv he
  change HasDerivAt (fun s => expectation ε hε (J (F U s v))) (r U t v) t at hc
  have hf : (fun s => expectation ε hε (J (F U s v)))=(fun s => expectation ε hε (P U s (J v))) := by
    funext s
    exact congrArg (expectation ε hε)
      (KFCausalClockFloorFrozenFastEvolution.evolution_embedding ε hε h hne hb m g k U s v)
  exact (congrArg (fun f => HasDerivAt f (r U t v) t) hf).mp hc

theorem dissipation_nonnegative (U t : ℝ) (hU : 0 < U) (v : V) : 0 ≤ d U t v :=
  div_nonneg (neg_nonneg.mpr (KFCausalClockFloorDefectProductionCoercivity.averaged_classical_nonpositive
    ε hε (O U t v))) (by positivity)

theorem rate_coercivity (U t : ℝ) (hU : 0 < U) (v : V) : (1/32)*d U t v ≤ -r U t v := by
  have he := div_le_div_of_nonneg_right
    (KFCausalClockFloorDefectProductionCoercivity.averaged_coercivity ε hε h hne hb (O U t v))
    (by positivity : 0 ≤ 2*U)
  change ((-2/h)*(inner ℂ (O U t v) ((A).compLp (O U t v))).im)/(2*U) ≤
    ((1/32)*(inner ℂ (O U t v) ((C).compLp (O U t v))).re)/(2*U) at he
  unfold dissipation rate
  convert neg_le_neg he using 1
  ring

theorem rate_continuous (U : ℝ) (v : V) : Continuous (fun t => r U t v) :=
  (continuous_const.mul (Complex.continuous_im.comp ((output_continuous ε hε h hne hb m g k U v).inner
    (((A).compLpL 2 _).continuous.comp (output_continuous ε hε h hne hb m g k U v))))).div_const (2*U)

theorem dissipation_continuous (U : ℝ) (v : V) : Continuous (fun t => d U t v) :=
  (Complex.continuous_re.comp ((output_continuous ε hε h hne hb m g k U v).inner
    (((C).compLpL 2 _).continuous.comp (output_continuous ε hε h hne hb m g k U v)))).neg.div_const (2*U)

theorem expectation_antitone (U : ℝ) (hU : 0 < U) (v : V) :
    Antitone (fun t => expectation ε hε (P U t (J v))) := by
  apply antitone_of_hasDerivAt_nonpos (fun t => expectation_derivative ε hε h hne hb m g k U t v)
  intro t
  change r U t v ≤ 0
  linarith [rate_coercivity ε hε h hne hb m g k U t hU v,
    dissipation_nonnegative ε hε h hne hb m g k U t hU v]

theorem expectation_integral (U a b : ℝ) (v : V) :
    (∫ t in a..b, r U t v)=expectation ε hε (P U b (J v))-expectation ε hε (P U a (J v)) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => expectation_derivative ε hε h hne hb m g k U t v)
    ((rate_continuous ε hε h hne hb m g k U v).intervalIntegrable a b)

theorem dissipation_budget (U L : ℝ) (hU : 0 < U) (hL : 0 ≤ L) (v : V) :
    (∫ t in 0..L, d U t v) ≤ 32*(expectation ε hε (J v)-expectation ε hε (P U L (J v))) := by
  have hi := intervalIntegral.integral_mono_on (μ := volume) hL
    ((dissipation_continuous ε hε h hne hb m g k U v).intervalIntegrable 0 L)
    ((continuous_const.mul (rate_continuous ε hε h hne hb m g k U v)).intervalIntegrable 0 L)
    (fun t _ => show d U t v ≤ (-32)*r U t v by linarith [rate_coercivity ε hε h hne hb m g k U t hU v])
  simp only [Pi.mul_apply] at hi
  rw [intervalIntegral.integral_const_mul,expectation_integral ε hε h hne hb m g k U 0 L v] at hi
  have hz : P U 0 (J v)=J v := KFCausalClockFloorFrozenEvolution.evolution_initial
    ε hε h hne hb m g k (physicalTime U) (1/(2*h*U)) (J v)
  rw [hz] at hi
  linarith only [hi]

#print axioms output_continuous
#print axioms expectation_derivative
#print axioms dissipation_nonnegative
#print axioms rate_coercivity
#print axioms rate_continuous
#print axioms dissipation_continuous
#print axioms expectation_antitone
#print axioms expectation_integral
#print axioms dissipation_budget
end
end UnifiedTheory.Audit.KFCausalClockFloorFrozenClockLoss

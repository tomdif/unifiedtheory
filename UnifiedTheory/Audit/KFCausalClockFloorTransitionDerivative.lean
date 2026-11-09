/- Scalar transition amplitudes of the actual nonautonomous evolution
are differentiable for completed-form initial and test states. The
derivative follows from the proved weak integral equation and strong
continuity in the form space; no operator-domain trajectory assumption
is introduced. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
import UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorTransitionDerivative
noncomputable section
open MeasureTheory
open KFCausalClockFloorAveragedFormTransport
open KFCausalClockFloorAveragedRegularity
open KFCausalClockFloorAveragedFormFlow
open KFCausalClockFloorStrongFormEvolution
open KFCausalClockFloorAveragedEvolution

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "V" => FormSpace ε hε h hh hb mass2 quartic vacuum 0
local notation "J" => embedding ε hε h hh hb mass2 quartic vacuum 0
local notation "F" => formFlow ε hε h hh hb mass2 quartic vacuum
local notation "A" => referenceFormOperator ε hε h hh hb mass2 quartic vacuum
local notation "U" => evolution ε hε h hh hb mass2 quartic vacuum

def transition (s : ℝ) (w v : V) (t : ℝ) : ℂ :=
  inner ℂ (U s t (J w)) (J v)

def current (s : ℝ) (w v : V) (t : ℝ) : ℂ :=
  inner ℂ (F s t w) (A t v)

theorem referenceForm_continuous : Continuous A :=
  (show Differentiable ℝ A from fun t =>
    (referenceForm_derivative ε hε h hh hb mass2 quartic vacuum t).differentiableAt).continuous

theorem current_continuous (s : ℝ) (w v : V) :
    Continuous (current ε hε h hh hb mass2 quartic vacuum s w v) :=
  (formFlow_continuous ε hε h hh hb mass2 quartic vacuum s w).inner
    ((referenceForm_continuous ε hε h hh hb mass2 quartic vacuum).clm_apply continuous_const)

theorem integral_equation (s : ℝ) (w v : V) (r t : ℝ) :
    (∫ z in r..t, current ε hε h hh hb mass2 quartic vacuum s w v z) =
      (-Complex.I*(h:ℂ))*
        (transition ε hε h hh hb mass2 quartic vacuum s w v t-
         transition ε hε h hh hb mass2 quartic vacuum s w v r) :=
  evolution_schrodinger_integral ε hε h hh hb mass2 quartic vacuum s hh w v r t

theorem transition_hasDerivAt (s : ℝ) (w v : V) (r : ℝ) :
    HasDerivAt (transition ε hε h hh hb mass2 quartic vacuum s w v)
      ((-Complex.I*(h:ℂ))⁻¹*current ε hε h hh hb mass2 quartic vacuum s w v r) r := by
  have hc : -Complex.I*(h:ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by exact_mod_cast hh)
  have hI := (current_continuous ε hε h hh hb mass2 quartic vacuum s w v).integral_hasStrictDerivAt r r
  have hd := (hI.hasDerivAt.const_mul (-Complex.I*(h:ℂ))⁻¹).add_const
    (transition ε hε h hh hb mass2 quartic vacuum s w v r)
  have he : (fun t => (-Complex.I*(h:ℂ))⁻¹*
      (∫ z in r..t, current ε hε h hh hb mass2 quartic vacuum s w v z)+
        transition ε hε h hh hb mass2 quartic vacuum s w v r) =
      transition ε hε h hh hb mass2 quartic vacuum s w v := by
    funext t
    rw [integral_equation,← mul_assoc,inv_mul_cancel₀ hc,one_mul,sub_add_cancel]
  rw [he] at hd
  exact hd

theorem transition_initial_hasDerivAt (s : ℝ) (w v : V) :
    HasDerivAt (transition ε hε h hh hb mass2 quartic vacuum s w v)
      ((-Complex.I*(h:ℂ))⁻¹*inner ℂ w (A s v)) s := by
  have hd := transition_hasDerivAt ε hε h hh hb mass2 quartic vacuum s w v s
  simpa only [current,formFlow_initial] using hd

#print axioms referenceForm_continuous
#print axioms current_continuous
#print axioms integral_equation
#print axioms transition_hasDerivAt
#print axioms transition_initial_hasDerivAt
end
end UnifiedTheory.Audit.KFCausalClockFloorTransitionDerivative

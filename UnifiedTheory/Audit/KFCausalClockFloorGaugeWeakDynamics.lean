/- Actual finite-energy quantum trajectories satisfy the transformed
weak Schrodinger equation. The unbounded chart term acts on the test
vector. No chart moment or Hamiltonian domain of the state is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaugePairing
import UnifiedTheory.Audit.KFCausalClockFloorGaugeDerivative
import UnifiedTheory.Audit.KFCausalMovingTestDerivative
import UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorGaugeWeakDynamics
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory (weakTrajectory)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakIntegralEquation (limitSlope)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorReferenceChartModulation
open UnifiedTheory.Audit.KFCausalClockFloorGaugeEnergy (rate fixedOutputLp kineticOutputLp)
open UnifiedTheory.Audit.KFCausalClockFloorGaugePairing
open UnifiedTheory.Audit.KFCausalClockFloorGaugeDerivative

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
  (m q k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m q k 0
local notation "J" => embedding ε hε h hne hh m q k 0
local notation "A" => energyOutput ε hε h hne hh m q k 0
local notation "R" => (fun r : ℝ => formAction ε hε h hne hh m q k r 0)
local notation "Q" => referenceFormOperator ε hε h hne hh m q k
local notation "F" => formFlow ε hε h hne hh m q k
local notation "U" => evolution ε hε h hne hh m q k

def transformedState (s t : ℝ) (f : Hilbert) : Hilbert := gauge ε h (-t) (U s t f)
def transformedFormState (s t : ℝ) (w : V) : V := R (-rate h t) (F s t w)

def transformedPairing (t : ℝ) (u v : V) (chartOutput : Hilbert) : ℂ :=
  inner ℂ (fixedOutputLp (A u)) (fixedOutputLp (A v))+(Real.exp (2*t):ℂ)*
    inner ℂ (kineticOutputLp (A u)) (kineticOutputLp (A v))-2*inner ℂ (J u) chartOutput

theorem physical_pairing_derivative (s t : ℝ) (w v : V) :
    HasDerivAt (fun z => inner ℂ (U s z (J w)) (J v))
      ((Complex.I*((1/h:ℝ):ℂ))*inner ℂ (F s t w) (Q t v)) t := by
  have hd := mass_pairing_derivative ε hε h hne hh m q k s w
    (weakTrajectory ε hε h hne hh m q k s w) t v
  simp only [massState,mass_left_pairing,massSlope_pairing,limitSlope] at hd
  change HasDerivAt (fun z => inner ℂ (J (F s z w)) (J v))
    ((Complex.I*((1/h:ℝ):ℂ))*inner ℂ (F s t w) (Q t v)) t at hd
  simpa only [evolution_embedding] using hd

theorem transformed_embedding (s t : ℝ) (w : V) :
    J (transformedFormState ε hε h hne hh m q k s t w) =
      transformedState ε hε h hne hh m q k s t (J w) := by
  unfold transformedFormState transformedState
  rw [formAction_embedding,evolution_embedding]
  unfold KFCausalClockFloorGaugeDerivative.gauge
  rw [show rate h (-t) = -rate h t by unfold rate; ring]

theorem transformed_initial (s : ℝ) (w : V) :
    transformedState ε hε h hne hh m q k s s (J w) = gauge ε h (-s) (J w) := by
  simp only [transformedState,evolution_embedding,formFlow_initial]

theorem transformed_density (s t : ℝ) (f : Hilbert) :
    (fun x => ‖transformedState ε hε h hne hh m q k s t f x‖) =ᵐ[volume]
      fun x => ‖U s t f x‖ :=
  KFCausalClockFloorChartModulation.modulation_density ε (rate h (-t)) (U s t f)

theorem transformed_weak_derivative (s t : ℝ) (w v : V) (g : Hilbert)
    (hvg : (J v,g) ∈ (chartOperator ε).graph) :
    HasDerivAt (fun z => inner ℂ (transformedState ε hε h hne hh m q k s z (J w)) (J v))
      ((Complex.I*((1/h:ℝ):ℂ))*transformedPairing ε hε h hne hh m q k t
        (transformedFormState ε hε h hne hh m q k s t w) v g) t := by
  have hf := physical_pairing_derivative ε hε h hne hh m q k s t w (R (rate h t) v)
  simp only [formAction_embedding] at hf
  have hd := KFCausalMovingTestDerivative.pairing_derivative
    (fun z => U s z (J w)) (fun z => gauge ε h z (J v)) t
    ((Complex.I*((-2/h:ℝ):ℂ)) • gauge ε h t g)
    ((Complex.I*((1/h:ℝ):ℂ))*inner ℂ (F s t w) (Q t (R (rate h t) v)))
    (evolution_strong_continuous ε hε h hne hh m q k s (J w)).continuousAt
    (gauge_derivative ε h hne (J v) g hvg t) hf
  have he : (Complex.I*((1/h:ℝ):ℂ))*inner ℂ (F s t w) (Q t (R (rate h t) v))+
      inner ℂ (U s t (J w)) ((Complex.I*((-2/h:ℝ):ℂ)) • gauge ε h t g) =
      (Complex.I*((1/h:ℝ):ℂ))*transformedPairing ε hε h hne hh m q k t
        (transformedFormState ε hε h hne hh m q k s t w) v g := by
    let P : ℂ := inner ℂ (fixedOutputLp (A (R (-rate h t) (F s t w)))) (fixedOutputLp (A v))+
      (Real.exp (2*t):ℂ)*inner ℂ (kineticOutputLp (A (R (-rate h t) (F s t w)))) (kineticOutputLp (A v))
    let z : ℂ := inner ℂ (gauge ε h (-t) (U s t (J w))) g
    have ha : inner ℂ (F s t w) (Q t (R (rate h t) v)) = P :=
      reference_mixed_pairing ε hε h hne hh m q k t (F s t w) v
    have hb : inner ℂ (U s t (J w)) ((Complex.I*((-2/h:ℝ):ℂ)) • gauge ε h t g) =
        (Complex.I*((-2/h:ℝ):ℂ))*z :=
      (inner_smul_right (𝕜 := ℂ) (E := Hilbert) (U s t (J w)) (gauge ε h t g)
        (Complex.I*((-2/h:ℝ):ℂ))).trans
        (congrArg (fun y : ℂ => (Complex.I*((-2/h:ℝ):ℂ))*y)
          (gauge_pairing ε h t (U s t (J w)) g).symm)
    have hp : transformedPairing ε hε h hne hh m q k t
        (transformedFormState ε hε h hne hh m q k s t w) v g = P-2*z :=
      congrArg (fun x : Hilbert => P-2*inner ℂ x g)
        (transformed_embedding ε hε h hne hh m q k s t w)
    have hc : (Complex.I*((1/h:ℝ):ℂ))*P+(Complex.I*((-2/h:ℝ):ℂ))*z =
        (Complex.I*((1/h:ℝ):ℂ))*(P-2*z) := by
      push_cast
      ring
    exact (congrArg₂ (fun x y : ℂ => x+y)
      (congrArg (fun y : ℂ => (Complex.I*((1/h:ℝ):ℂ))*y) ha) hb).trans
      (hc.trans (congrArg (fun y : ℂ => (Complex.I*((1/h:ℝ):ℂ))*y) hp.symm))
  have hfun : (fun z => inner ℂ (transformedState ε hε h hne hh m q k s z (J w)) (J v)) =
      (fun z => inner ℂ (U s z (J w)) (gauge ε h z (J v))) :=
    funext (fun z => gauge_pairing ε h z (U s z (J w)) (J v))
  rw [hfun]
  exact hd.congr_deriv he

#print axioms physical_pairing_derivative
#print axioms transformed_embedding
#print axioms transformed_initial
#print axioms transformed_density
#print axioms transformed_weak_derivative
end
end UnifiedTheory.Audit.KFCausalClockFloorGaugeWeakDynamics

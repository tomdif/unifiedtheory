/- An exact clock-defect expectation derivative for the actual bounded
Yosida dynamics, with a classical-coefficient error uniform in the cutoff
on initial energy-form states. It does not identify classical trajectories. -/
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianVelocity
import UnifiedTheory.Audit.KFCausalYosidaObservableVelocity
import UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorEhrenfestVelocity
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectForm (defect_inner)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityPairing (defect_inner_im_zero)
open UnifiedTheory.Audit.KFCausalClockFloorHamiltonianVelocity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent (shiftedResolvent)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosida
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaEnergy
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy)
open UnifiedTheory.Audit.KFCausalYosidaObservableVelocity

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hne : hbar ≠ 0)
  (hh : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "H" => hamiltonian ε hε hbar hne hh mass2 quartic vacuum
local notation "R" => shiftedResolvent ε hε hbar hne hh mass2 quartic vacuum
local notation "V" => dynamics ε hε hbar hne hh mass2 quartic vacuum
local notation "D" => defectOperator ε hε

def smoothedDomainState (a : ℝ) (ha : 0 < a) (s t : ℝ) (f : Hilbert) : (H t).domain :=
  smoothedPoint (H t) (R a t) a (averaged_resolves ε hε hbar hne hh mass2 quartic vacuum a t ha)
    (V a ha s t f)

def expectationCurve (a : ℝ) (ha : 0 < a) (s t : ℝ) (f : Hilbert) : ℝ :=
  (inner ℂ (V a ha s t f) (D (V a ha s t f))).re

def quantumRate (a : ℝ) (ha : 0 < a) (s t : ℝ) (f : Hilbert) : ℝ :=
  (-2/hbar)*(inner ℂ (H t (smoothedDomainState ε hε hbar hne hh mass2 quartic vacuum a ha s t f))
    (D (smoothedDomainState ε hε hbar hne hh mass2 quartic vacuum a ha s t f))).im

def classicalRate (a : ℝ) (ha : 0 < a) (s t : ℝ) (f : Hilbert) : ℝ :=
  classicalVelocity ε hε hbar hne hh mass2 quartic vacuum t
    (smoothedDomainState ε hε hbar hne hh mass2 quartic vacuum a ha s t f)

theorem expectationCurve_derivative (a : ℝ) (ha : 0 < a) (s t : ℝ) (f : Hilbert) :
    HasDerivAt (fun r => expectationCurve ε hε hbar hne hh mass2 quartic vacuum a ha s r f)
      (quantumRate ε hε hbar hne hh mass2 quartic vacuum a ha s t f) t := by
  have hd := expectation_derivative D (defect_inner ε hε) (fun r => V a ha s r f)
    (averagedYosida ε hε hbar hne hh mass2 quartic vacuum a t (V a ha s t f)) hbar t
    (dynamics_state_derivative ε hε hbar hne hh mass2 quartic vacuum a ha s t f)
  have hp := smoothed_pairing (H t) (R a t) D a
    (averaged_resolves ε hε hbar hne hh mass2 quartic vacuum a t ha)
    (defect_inner_im_zero ε hε) (V a ha s t f)
  change (inner ℂ (averagedYosida ε hε hbar hne hh mass2 quartic vacuum a t (V a ha s t f))
    (D (V a ha s t f))).im = _ at hp
  rw [hp] at hd
  exact hd

theorem rate_error (a : ℝ) (ha : 0 < a) (s t : ℝ) (f : Hilbert) :
    |quantumRate ε hε hbar hne hh mass2 quartic vacuum a ha s t f-
      classicalRate ε hε hbar hne hh mass2 quartic vacuum a ha s t f| ≤
      (20*|hbar|/ε^2)*trajectoryEnergy ε hε hbar hne hh mass2 quartic vacuum a ha s t f := by
  apply (hamiltonian_velocity_error ε hε hbar hne hh mass2 quartic vacuum t
    (smoothedDomainState ε hε hbar hne hh mass2 quartic vacuum a ha s t f)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact smoothed_energy_le (H t) (R a t) a ha.le
    (averaged_resolves ε hε hbar hne hh mass2 quartic vacuum a t ha) (V a ha s t f)

theorem uniform_rate_error (a : ℝ) (ha : 0 < a) (s t : ℝ)
    (w : FormSpace ε hε hbar hne hh mass2 quartic vacuum 0) :
    |quantumRate ε hε hbar hne hh mass2 quartic vacuum a ha s t
        (embedding ε hε hbar hne hh mass2 quartic vacuum 0 w)-
      classicalRate ε hε hbar hne hh mass2 quartic vacuum a ha s t
        (embedding ε hε hbar hne hh mass2 quartic vacuum 0 w)| ≤
      (20*|hbar|/ε^2)*(Real.exp (2*|t-s|)*timeEnergy ε hε hbar hne hh mass2 quartic vacuum s w) :=
  (rate_error ε hε hbar hne hh mass2 quartic vacuum a ha s t _).trans
    (mul_le_mul_of_nonneg_left
      (uniform_energy_bound ε hε hbar hne hh mass2 quartic vacuum a ha s t w) (by positivity))

theorem quantumRate_bound (a : ℝ) (ha : 0 < a) (s t : ℝ) (f : Hilbert) :
    |quantumRate ε hε hbar hne hh mass2 quartic vacuum a ha s t f| ≤
      (20*|hbar|/ε^2+1/ε)*trajectoryEnergy ε hε hbar hne hh mass2 quartic vacuum a ha s t f := by
  apply (hamiltonian_velocity_bound ε hε hbar hne hh mass2 quartic vacuum t
    (smoothedDomainState ε hε hbar hne hh mass2 quartic vacuum a ha s t f)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact smoothed_energy_le (H t) (R a t) a ha.le
    (averaged_resolves ε hε hbar hne hh mass2 quartic vacuum a t ha) (V a ha s t f)

theorem uniform_quantumRate_bound (a : ℝ) (ha : 0 < a) (s t : ℝ)
    (w : FormSpace ε hε hbar hne hh mass2 quartic vacuum 0) :
    |quantumRate ε hε hbar hne hh mass2 quartic vacuum a ha s t
        (embedding ε hε hbar hne hh mass2 quartic vacuum 0 w)| ≤
      (20*|hbar|/ε^2+1/ε)*(Real.exp (2*|t-s|)*timeEnergy ε hε hbar hne hh mass2 quartic vacuum s w) :=
  (quantumRate_bound ε hε hbar hne hh mass2 quartic vacuum a ha s t _).trans
    (mul_le_mul_of_nonneg_left
      (uniform_energy_bound ε hε hbar hne hh mass2 quartic vacuum a ha s t w) (by positivity))

#print axioms expectationCurve_derivative
#print axioms rate_error
#print axioms uniform_rate_error
#print axioms quantumRate_bound
#print axioms uniform_quantumRate_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorEhrenfestVelocity

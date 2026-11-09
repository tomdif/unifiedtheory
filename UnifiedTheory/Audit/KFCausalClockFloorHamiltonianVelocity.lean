/- A controlled classical-coefficient comparison for the actual
charge-averaged Hamiltonian's clock-defect form commutator. All operator
and form domains are supplied by the existing construction. -/
import UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput
import UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityClassical
import UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonianDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHamiltonianVelocity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormDefect
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hne : hbar ≠ 0)
  (hh : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)
local notation "hb" => hamiltonian_bound ε hbar hh
local notation "𝒟" => formData ε hε hbar hne hh mass2 quartic vacuum t
local notation "H" => hamiltonian ε hε hbar hne hh mass2 quartic vacuum t
local notation "F" => formAction ε hε hbar hne hh mass2 quartic vacuum t
local notation "R" => outputAction ε hε hbar hh
local notation "Q" => classicalOutput ε hε

def hamiltonianOutput (x : (H).domain) :=
  KFCausalClosedGraphForm.energyOutput 𝒟 (KFCausalClosedGraphForm.formLift 𝒟 x)

def classicalVelocity (x : (H).domain) : ℝ :=
  (inner ℂ (hamiltonianOutput ε hε hbar hne hh mass2 quartic vacuum t x)
    ((Q).compLp (hamiltonianOutput ε hε hbar hne hh mass2 quartic vacuum t x))).re

theorem hamiltonian_velocity_pairing (x : (H).domain) :
    inner ℂ (H x) (defectOperator ε hε x) =
      inner ℂ (hamiltonianOutput ε hε hbar hne hh mass2 quartic vacuum t x)
        ((R).compLp (hamiltonianOutput ε hε hbar hne hh mass2 quartic vacuum t x)) := by
  obtain ⟨u,hu⟩ := graphFormVector_surjective ε hε hbar hne hh mass2 quartic vacuum t
    (KFCausalClosedGraphForm.formLift 𝒟 x)
  have he : embedding ε hε hbar hb hne mass2 quartic vacuum t u = (x:Hilbert) :=
    (congrArg (KFCausalClosedGraphForm.embedding 𝒟) hu).trans
      (KFCausalClosedGraphForm.embedding_formLift 𝒟 x)
  have ho : energyOutput ε hε hbar hb hne mass2 quartic vacuum t u =
      hamiltonianOutput ε hε hbar hne hh mass2 quartic vacuum t x :=
    congrArg (KFCausalClosedGraphForm.energyOutput 𝒟) hu
  have hp := hamiltonian_represents_averaged_form ε hε hbar hne hh mass2 quartic vacuum t x (F u)
  simp only [formAction_embedding,formAction_output,he,ho] at hp
  exact hp.symm

theorem hamiltonian_velocity_error (x : (H).domain) :
    |(-2/hbar)*(inner ℂ (H x) (defectOperator ε hε x)).im-
      classicalVelocity ε hε hbar hne hh mass2 quartic vacuum t x| ≤
      (20*|hbar|/ε^2)*(inner ℂ (H x) (x:Hilbert)).re := by
  have he : (inner ℂ (H x) (x:Hilbert)).re =
      ‖hamiltonianOutput ε hε hbar hne hh mass2 quartic vacuum t x‖^2 :=
    KFCausalClosedGraphForm.hamiltonian_energy 𝒟 x
  rw [hamiltonian_velocity_pairing,classicalVelocity,he]
  exact outputLp_velocity_error ε hε hbar hne hh _

theorem hamiltonian_velocity_error_of_energy_bound (x : (H).domain) (E : ℝ)
    (hE : (inner ℂ (H x) (x:Hilbert)).re ≤ E) :
    |(-2/hbar)*(inner ℂ (H x) (defectOperator ε hε x)).im-
      classicalVelocity ε hε hbar hne hh mass2 quartic vacuum t x| ≤
      (20*|hbar|/ε^2)*E :=
  (hamiltonian_velocity_error ε hε hbar hne hh mass2 quartic vacuum t x).trans
    (mul_le_mul_of_nonneg_left hE (by positivity))

theorem classical_velocity_bound (x : (H).domain) :
    |classicalVelocity ε hε hbar hne hh mass2 quartic vacuum t x| ≤
      (1/ε)*(inner ℂ (H x) (x:Hilbert)).re := by
  have he : (inner ℂ (H x) (x:Hilbert)).re =
      ‖hamiltonianOutput ε hε hbar hne hh mass2 quartic vacuum t x‖^2 :=
    KFCausalClosedGraphForm.hamiltonian_energy 𝒟 x
  rw [he]
  exact classicalOutputLp_pairing_bound ε hε _

theorem hamiltonian_velocity_bound (x : (H).domain) :
    |(-2/hbar)*(inner ℂ (H x) (defectOperator ε hε x)).im| ≤
      (20*|hbar|/ε^2+1/ε)*(inner ℂ (H x) (x:Hilbert)).re := by
  have herror := hamiltonian_velocity_error ε hε hbar hne hh mass2 quartic vacuum t x
  have hc := classical_velocity_bound ε hε hbar hne hh mass2 quartic vacuum t x
  have ha := abs_add_le
    ((-2/hbar)*(inner ℂ (H x) (defectOperator ε hε x)).im-
      classicalVelocity ε hε hbar hne hh mass2 quartic vacuum t x)
    (classicalVelocity ε hε hbar hne hh mass2 quartic vacuum t x)
  rw [sub_add_cancel] at ha
  nlinarith

#print axioms hamiltonian_velocity_pairing
#print axioms hamiltonian_velocity_error
#print axioms hamiltonian_velocity_error_of_energy_bound
#print axioms classical_velocity_bound
#print axioms hamiltonian_velocity_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorHamiltonianVelocity

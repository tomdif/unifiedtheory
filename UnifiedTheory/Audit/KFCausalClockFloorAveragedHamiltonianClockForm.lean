/- Identification of the clock-response form with the actual averaged
Hamiltonian weak pairing. This uses actual clock/form graph pairs and does
not claim that C preserves the Hamiltonian operator domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedClockResponse
import UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonianClockForm
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalClockFloorAveragedClockResponse
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorClockOperator

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)
local notation "hb" => KFCausalClockFloorClosedEnergyDefect.energy_bound ε hε h hh
local notation "𝒱" => AveragedSpace ε hε h hb hne mass2 quartic vacuum t
local notation "J" => embedding ε hε h hb hne mass2 quartic vacuum t
local notation "A" => energyOutput ε hε h hb hne mass2 quartic vacuum t
local notation "𝒟" => formData ε hε h hne hh mass2 quartic vacuum t
local notation "ℋ" => hamiltonian ε hε h hne hh mass2 quartic vacuum t

theorem hamiltonian_pairing (x : (ℋ).domain) (u v : 𝒱) (hu : J u = (x:Hilbert)) :
    inner ℂ (A u) (A v) = inner ℂ (ℋ x) (J v) := by
  have he : graphFormVector ε hε h hne hh mass2 quartic vacuum t u = KFCausalClosedGraphForm.formLift 𝒟 x :=
    KFCausalClosedGraphForm.embedding_injective 𝒟
      ((graphFormVector_embedding ε hε h hne hh mass2 quartic vacuum t u).trans
        (hu.trans (KFCausalClosedGraphForm.embedding_formLift 𝒟 x).symm))
  have hout : A u = KFCausalClosedGraphForm.energyOutput 𝒟 (KFCausalClosedGraphForm.formLift 𝒟 x) :=
    (graphFormVector_output ε hε h hne hh mass2 quartic vacuum t u).symm.trans
      (congrArg (KFCausalClosedGraphForm.energyOutput 𝒟) he)
  exact (congrArg (fun z => inner ℂ z (A v)) hout).trans
    (hamiltonian_represents_averaged_form ε hε h hne hh mass2 quartic vacuum t x v)

theorem weak_clock_response (x y : (ℋ).domain) (u uc v vc : 𝒱)
    (hu : J u = (x:Hilbert)) (hv : J v = (y:Hilbert))
    (hc : (J u,J uc) ∈ (clockOperator ε hε).graph)
    (hd : (J v,J vc) ∈ (clockOperator ε hε).graph) :
    inner ℂ (ℋ x) (J vc)-inner ℂ (J uc) (ℋ y) =
      formResponse ε hε h hne hh mass2 quartic vacuum t u v := by
  have hx := hamiltonian_pairing ε hε h hne hh mass2 quartic vacuum t x u vc hu
  have hy := hamiltonian_pairing ε hε h hne hh mass2 quartic vacuum t y v uc hv
  have hy' : inner ℂ (A uc) (A v) = inner ℂ (J uc) (ℋ y) := by
    simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) hy
  exact (congrArg₂ (fun a b : ℂ => a-b) hx.symm hy'.symm).trans
    (core_agreement ε hε h hne hh mass2 quartic vacuum t u uc v vc hc hd)

theorem weak_clock_response_bound (x y : (ℋ).domain) (u uc v vc : 𝒱)
    (hu : J u = (x:Hilbert)) (hv : J v = (y:Hilbert))
    (hc : (J u,J uc) ∈ (clockOperator ε hε).graph)
    (hd : (J v,J vc) ∈ (clockOperator ε hε).graph) :
    ‖inner ℂ (ℋ x) (J vc)-inner ℂ (J uc) (ℋ y)‖ ≤ 2*|h| * ‖A u‖*‖A v‖ :=
  (congrArg norm (weak_clock_response ε hε h hne hh mass2 quartic vacuum t x y u uc v vc hu hv hc hd)).le.trans
    (formResponse_norm ε hε h hne hh mass2 quartic vacuum t u v)

theorem diagonal_response_bound (x : (ℋ).domain) (u uc : 𝒱)
    (hu : J u = (x:Hilbert)) (hc : (J u,J uc) ∈ (clockOperator ε hε).graph) :
    ‖inner ℂ (ℋ x) (J uc)-inner ℂ (J uc) (ℋ x)‖ ≤ 2*|h| * ‖A u‖^2 := by
  have hbnd := weak_clock_response_bound ε hε h hne hh mass2 quartic vacuum t x x u uc u uc hu hu hc hc
  simpa only [pow_two,mul_assoc] using hbnd

#print axioms hamiltonian_pairing
#print axioms weak_clock_response
#print axioms weak_clock_response_bound
#print axioms diagonal_response_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonianClockForm

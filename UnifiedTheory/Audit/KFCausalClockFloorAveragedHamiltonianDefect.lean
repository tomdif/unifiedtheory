/- Signed clock-defect pairing for the actual averaged Hamiltonian on
its full operator domain. The proof uses the complete averaged form
action and the existing form representation, not operator-domain invariance. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormDefect
import UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonianDefect
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hne : hbar ≠ 0)
  (hh : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)

local notation "hb" => hamiltonian_bound ε hbar hh
local notation "𝒟" => formData ε hε hbar hne hh mass2 quartic vacuum t
local notation "H" => hamiltonian ε hε hbar hne hh mass2 quartic vacuum t
local notation "F" => formAction ε hε hbar hne hh mass2 quartic vacuum t

theorem hamiltonian_square_sign (x : (H).domain) :
    0 ≤ hbar*(inner ℂ (H x) (defectOperator ε hε (defectOperator ε hε x))).im := by
  obtain ⟨u,hu⟩ := graphFormVector_surjective ε hε hbar hne hh mass2 quartic vacuum t
    (KFCausalClosedGraphForm.formLift 𝒟 x)
  have he : embedding ε hε hbar hb hne mass2 quartic vacuum t u = (x:Hilbert) :=
    (congrArg (KFCausalClosedGraphForm.embedding 𝒟) hu).trans
      (KFCausalClosedGraphForm.embedding_formLift 𝒟 x)
  have ho : energyOutput ε hε hbar hb hne mass2 quartic vacuum t u =
      KFCausalClosedGraphForm.energyOutput 𝒟 (KFCausalClosedGraphForm.formLift 𝒟 x) :=
    congrArg (KFCausalClosedGraphForm.energyOutput 𝒟) hu
  have hp := hamiltonian_represents_averaged_form ε hε hbar hne hh mass2 quartic vacuum t x (F (F u))
  simp only [formAction_embedding,he,← ho] at hp
  rw [← hp]
  exact formAction_square_sign ε hε hbar hne hh mass2 quartic vacuum t u

#print axioms hamiltonian_square_sign

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonianDefect

/- The differentiable averaged form curve represents the actual
unbounded Hamiltonian at every time, including its variational domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonianBridge
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian formData)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)

local notation "D" => formData ε hε hbar hh hbound mass2 quartic vacuum t
local notation "R" => formTransfer ε hε hbar hh hbound mass2 quartic vacuum
local notation "J" => embedding ε hε hbar hh hbound mass2 quartic vacuum
local notation "A" => energyOutput ε hε hbar hh hbound mass2 quartic vacuum
local notation "H" => hamiltonian ε hε hbar hh hbound mass2 quartic vacuum t

theorem hamiltonian_reference_domain (u : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (y : Hilbert) :
    (∃ hx : J 0 u ∈ (H).domain, H ⟨J 0 u,hx⟩ = y) ↔
      ∀ v, inner ℂ u (referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum t v) =
        inner ℂ y (J 0 v) := by
  have hc := KFCausalClosedGraphForm.hamiltonian_domain_characterization D (R 0 t u) y
  have hj := transfer_embedding ε hε hbar hh hbound mass2 quartic vacuum 0 t u
  have hjp := congrArg (fun f : Hilbert => ∃ hx : f ∈ (H).domain, H ⟨f,hx⟩ = y) hj
  refine (Iff.of_eq hjp.symm).trans (hc.trans ?_)
  constructor
  · intro hp v
    have hv := congrArg (fun f : Hilbert => inner ℂ y f)
      (transfer_embedding ε hε hbar hh hbound mass2 quartic vacuum 0 t v)
    exact (referenceForm_represents_closed_form ε hε hbar hh hbound mass2 quartic vacuum t u v).trans
      ((hp (R 0 t v)).trans hv)
  · intro hp w
    have hr := referenceForm_represents_closed_form ε hε hbar hh hbound mass2 quartic vacuum t u (R t 0 w)
    have hi := transfer_inverse ε hε hbar hh hbound mass2 quartic vacuum t 0 w
    have he := congrArg (fun z => inner ℂ (A t (R 0 t u)) (A t z)) hi
    have hw := congrArg (fun f : Hilbert => inner ℂ y f)
      (transfer_embedding ε hε hbar hh hbound mass2 quartic vacuum t 0 w)
    exact he.symm.trans (hr.symm.trans ((hp (R t 0 w)).trans hw))

def referenceLift (x : (H).domain) : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0 :=
  R t 0 (KFCausalClosedGraphForm.formLift D x)

theorem embedding_referenceLift (x : (H).domain) :
    J 0 (referenceLift ε hε hbar hh hbound mass2 quartic vacuum t x) = (x:Hilbert) :=
  (transfer_embedding ε hε hbar hh hbound mass2 quartic vacuum t 0
    (KFCausalClosedGraphForm.formLift D x)).trans (KFCausalClosedGraphForm.embedding_formLift D x)

theorem hamiltonian_reference_pairing (x : (H).domain)
    (v : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    inner ℂ (referenceLift ε hε hbar hh hbound mass2 quartic vacuum t x)
      (referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum t v) =
        inner ℂ (H x) (J 0 v) := by
  have hr := referenceForm_represents_closed_form ε hε hbar hh hbound mass2 quartic vacuum t
    (referenceLift ε hε hbar hh hbound mass2 quartic vacuum t x) v
  have hi := transfer_inverse ε hε hbar hh hbound mass2 quartic vacuum t 0 (KFCausalClosedGraphForm.formLift D x)
  have he := congrArg (fun z => inner ℂ (A t z) (A t (R 0 t v))) hi
  have hv := congrArg (fun f : Hilbert => inner ℂ (H x) f)
    (transfer_embedding ε hε hbar hh hbound mass2 quartic vacuum 0 t v)
  exact hr.trans (he.trans ((KFCausalClosedGraphForm.hamiltonian_represents_form D x (R 0 t v)).trans hv))

#print axioms hamiltonian_reference_domain
#print axioms embedding_referenceLift
#print axioms hamiltonian_reference_pairing

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonianBridge

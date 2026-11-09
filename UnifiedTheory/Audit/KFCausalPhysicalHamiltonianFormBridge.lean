/- Exact identification of the unbounded Hamiltonian family with its
differentiable bounded form curve on the fixed completed form space.
This is not a differentiability assertion for unbounded operators. -/
import UnifiedTheory.Audit.KFCausalPhysicalFormRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalHamiltonianFormBridge
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalPhysicalFormTransport
open UnifiedTheory.Audit.KFCausalPhysicalFormRegularity
open UnifiedTheory.Audit.KFCausalPhysicalFormHamiltonian (hamiltonian formData)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε)
  (mass2 quartic vacuum t : ℝ)

theorem hamiltonian_reference_domain (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) (y : Hilbert) :
    (∃ hx : embedding ε hε hbar hh mass2 quartic vacuum 0 u ∈ (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain,
      hamiltonian ε hε hbar hh mass2 quartic vacuum t ⟨embedding ε hε hbar hh mass2 quartic vacuum 0 u,hx⟩=y) ↔
    ∀ v, inner ℂ u (referenceFormOperator ε hε hbar hh mass2 quartic vacuum t v)=
      inner ℂ y (embedding ε hε hbar hh mass2 quartic vacuum 0 v) := by
  have hc := KFCausalPhysicalFormHamiltonian.hamiltonian_domain_characterization
    ε hε hbar hh mass2 quartic vacuum t (formTransfer ε hε hbar hh mass2 quartic vacuum 0 t u) y
  change (∃ hx : embedding ε hε hbar hh mass2 quartic vacuum t
      (formTransfer ε hε hbar hh mass2 quartic vacuum 0 t u) ∈ (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain,
      hamiltonian ε hε hbar hh mass2 quartic vacuum t
        ⟨embedding ε hε hbar hh mass2 quartic vacuum t (formTransfer ε hε hbar hh mass2 quartic vacuum 0 t u),hx⟩=y) ↔
    ∀ w, inner ℂ (energyOutput ε hε hbar hh mass2 quartic vacuum t (formTransfer ε hε hbar hh mass2 quartic vacuum 0 t u))
      (energyOutput ε hε hbar hh mass2 quartic vacuum t w)=
      inner ℂ y (embedding ε hε hbar hh mass2 quartic vacuum t w) at hc
  rw [transfer_embedding] at hc
  constructor
  · intro hu v
    have hp := hc.mp hu (formTransfer ε hε hbar hh mass2 quartic vacuum 0 t v)
    rw [transfer_embedding] at hp
    rw [referenceForm_represents_closed_form]
    exact hp
  · intro hu
    apply hc.mpr
    intro w
    have hp := hu (formTransfer ε hε hbar hh mass2 quartic vacuum t 0 w)
    rw [referenceForm_represents_closed_form,transfer_inverse,transfer_embedding] at hp
    exact hp

def referenceLift (x : (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain) :
    FormSpace ε hε hbar hh mass2 quartic vacuum 0 :=
  formTransfer ε hε hbar hh mass2 quartic vacuum t 0
    (KFCausalClosedGraphForm.formLift (formData ε hε hbar hh mass2 quartic vacuum t) x)

theorem embedding_referenceLift (x : (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain) :
    embedding ε hε hbar hh mass2 quartic vacuum 0 (referenceLift ε hε hbar hh mass2 quartic vacuum t x)=x := by
  rw [referenceLift,transfer_embedding]
  exact KFCausalClosedGraphForm.embedding_formLift _ x

theorem hamiltonian_reference_pairing (x : (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain)
    (v : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    inner ℂ (referenceLift ε hε hbar hh mass2 quartic vacuum t x)
      (referenceFormOperator ε hε hbar hh mass2 quartic vacuum t v)=
    inner ℂ (hamiltonian ε hε hbar hh mass2 quartic vacuum t x) (embedding ε hε hbar hh mass2 quartic vacuum 0 v) := by
  rw [referenceForm_represents_closed_form,referenceLift,transfer_inverse]
  have hp := KFCausalPhysicalFormHamiltonian.hamiltonian_represents_form
    ε hε hbar hh mass2 quartic vacuum t x (formTransfer ε hε hbar hh mass2 quartic vacuum 0 t v)
  change inner ℂ (energyOutput ε hε hbar hh mass2 quartic vacuum t
    (KFCausalClosedGraphForm.formLift (formData ε hε hbar hh mass2 quartic vacuum t) x))
      (energyOutput ε hε hbar hh mass2 quartic vacuum t (formTransfer ε hε hbar hh mass2 quartic vacuum 0 t v))=
    inner ℂ (hamiltonian ε hε hbar hh mass2 quartic vacuum t x)
      (embedding ε hε hbar hh mass2 quartic vacuum t (formTransfer ε hε hbar hh mass2 quartic vacuum 0 t v)) at hp
  rwa [transfer_embedding] at hp

#print axioms hamiltonian_reference_domain
#print axioms embedding_referenceLift
#print axioms hamiltonian_reference_pairing

end
end UnifiedTheory.Audit.KFCausalPhysicalHamiltonianFormBridge

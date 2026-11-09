/- The fixed-reference form equation characterizes the already constructed
unbounded homogeneous Hamiltonian and its actual domain at each time. -/
import UnifiedTheory.Audit.KFCausalRegularizedHamiltonian
import UnifiedTheory.Audit.KFCausalRegularizedFormRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedHamiltonianFormBridge
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
open UnifiedTheory.Audit.KFCausalRegularizedHamiltonian
open UnifiedTheory.Audit.KFCausalRegularizedFormTransport
open UnifiedTheory.Audit.KFCausalRegularizedFormRegularity

def referenceLift (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (x : (homogeneousHamiltonian ε hε hbar coupling t).domain) :
    FormSpace ε hε hbar coupling 0 :=
  formTransfer ε hε hbar coupling t 0 (homogeneousFormLift ε hε hbar coupling t x)

theorem referenceLift_embedding (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (x : (homogeneousHamiltonian ε hε hbar coupling t).domain) :
    embedding ε hε hbar coupling 0 (referenceLift ε hε hbar coupling t x) = x := by
  exact (transfer_embedding ε hε hbar coupling t 0 _).trans
    (homogeneous_lift_embedding ε hε hbar coupling t x)

theorem referenceLift_transport (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (x : (homogeneousHamiltonian ε hε hbar coupling t).domain) :
    formTransfer ε hε hbar coupling 0 t (referenceLift ε hε hbar coupling t x) =
      homogeneousFormLift ε hε hbar coupling t x :=
  transfer_inverse ε hε hbar coupling t 0 _

theorem reference_hamiltonian_pairing (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (x : (homogeneousHamiltonian ε hε hbar coupling t).domain)
    (v : FormSpace ε hε hbar coupling 0) :
    inner ℂ (referenceLift ε hε hbar coupling t x) (referenceFormOperator ε hε hbar coupling t v) =
      inner ℂ (homogeneousHamiltonian ε hε hbar coupling t x) (embedding ε hε hbar coupling 0 v) := by
  rw [referenceForm_represents_closed_form ε hε hbar coupling t, referenceLift_transport ε hε hbar coupling t]
  exact (homogeneous_represents_form ε hε hbar coupling t x
    (formTransfer ε hε hbar coupling 0 t v)).trans
    (congrArg (inner ℂ (homogeneousHamiltonian ε hε hbar coupling t x))
      (transfer_embedding ε hε hbar coupling 0 t v))

theorem reference_domain_characterization (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (u : FormSpace ε hε hbar coupling 0) (y : Hilbert) :
    (∃ hx : embedding ε hε hbar coupling 0 u ∈ (homogeneousHamiltonian ε hε hbar coupling t).domain,
      homogeneousHamiltonian ε hε hbar coupling t ⟨embedding ε hε hbar coupling 0 u,hx⟩ = y) ↔
    ∀ v, inner ℂ u (referenceFormOperator ε hε hbar coupling t v) =
      inner ℂ y (embedding ε hε hbar coupling 0 v) := by
  have ht := homogeneous_domain_characterization ε hε hbar coupling t
    (formTransfer ε hε hbar coupling 0 t u) y
  rw [transfer_embedding ε hε hbar coupling 0 t] at ht
  constructor
  · intro hu v
    rw [referenceForm_represents_closed_form ε hε hbar coupling t]
    exact (ht.mp hu (formTransfer ε hε hbar coupling 0 t v)).trans
      (congrArg (inner ℂ y) (transfer_embedding ε hε hbar coupling 0 t v))
  · intro hq
    apply ht.mpr
    intro w
    have hp := hq (formTransfer ε hε hbar coupling t 0 w)
    rw [referenceForm_represents_closed_form ε hε hbar coupling t,
      transfer_inverse ε hε hbar coupling t 0,transfer_embedding ε hε hbar coupling t 0] at hp
    exact hp

#print axioms referenceLift_embedding
#print axioms referenceLift_transport
#print axioms reference_hamiltonian_pairing
#print axioms reference_domain_characterization

end
end UnifiedTheory.Audit.KFCausalRegularizedHamiltonianFormBridge

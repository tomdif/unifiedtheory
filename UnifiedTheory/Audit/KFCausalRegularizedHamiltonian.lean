/- The actual homogeneous regularized energy form has a constructed
positive self-adjoint Hamiltonian at every fixed time. This is not a
construction of a nonautonomous propagator or a six-mode infinite limit. -/
import UnifiedTheory.Audit.KFCausalFormHamiltonian
import UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalRegularizedHamiltonian
noncomputable section
open UnifiedTheory.Audit.KFCausalFormResolvent
open UnifiedTheory.Audit.KFCausalResolventHamiltonian
open UnifiedTheory.Audit.KFCausalFormHamiltonian
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedFormDomain
open UnifiedTheory.Audit.KFCausalRegularizedClosedForm
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding

def homogeneousResolvent (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) : Hilbert →L[ℂ] Hilbert :=
  resolvent (E := FormSpace ε hε hbar coupling t) (H := Hilbert) (embedding ε hε hbar coupling t)

def homogeneousHamiltonian (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  hamiltonian (E := FormSpace ε hε hbar coupling t) (H := Hilbert) (embedding ε hε hbar coupling t)
    (embedding_injective ε hε hbar coupling t) (embedding_dense ε hε hbar coupling t)

theorem homogeneous_selfAdjoint (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    IsSelfAdjoint (homogeneousHamiltonian ε hε hbar coupling t) :=
  hamiltonian_selfAdjoint _ _ _

theorem homogeneous_closed (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    (homogeneousHamiltonian ε hε hbar coupling t).IsClosed :=
  (homogeneous_selfAdjoint ε hε hbar coupling t).isClosed

theorem homogeneous_dense_domain (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    Dense ((homogeneousHamiltonian ε hε hbar coupling t).domain : Set Hilbert) :=
  (homogeneous_selfAdjoint ε hε hbar coupling t).dense_domain

theorem homogeneous_positive (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (x : (homogeneousHamiltonian ε hε hbar coupling t).domain) :
    0 ≤ (inner ℂ (homogeneousHamiltonian ε hε hbar coupling t x) (x:Hilbert)).re :=
  hamiltonian_positive _ _ _ (embedding_contraction ε hε hbar coupling t) x

theorem homogeneous_resolvent_domain (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    (homogeneousHamiltonian ε hε hbar coupling t).domain =
      (homogeneousResolvent ε hε hbar coupling t).range := rfl

theorem homogeneous_resolvent_identity (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (x : (homogeneousHamiltonian ε hε hbar coupling t).domain) :
    homogeneousResolvent ε hε hbar coupling t
      (homogeneousHamiltonian ε hε hbar coupling t x + (x:Hilbert)) = x :=
  inverseShift_resolvent _ _ x

def homogeneousFormLift (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (x : (homogeneousHamiltonian ε hε hbar coupling t).domain) : FormSpace ε hε hbar coupling t :=
  formLift _ _ _ x

theorem homogeneous_operator_form_dense (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    DenseRange (homogeneousFormLift ε hε hbar coupling t) :=
  operator_domain_form_dense _ _ _

theorem homogeneous_lift_embedding (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (x : (homogeneousHamiltonian ε hε hbar coupling t).domain) :
    embedding ε hε hbar coupling t (homogeneousFormLift ε hε hbar coupling t x) = x :=
  embedding_formLift _ _ _ x

theorem form_inner_identity (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (u v : FormSpace ε hε hbar coupling t) :
    inner ℂ u v = inner ℂ (embedding ε hε hbar coupling t u) (embedding ε hε hbar coupling t v) +
      inner ℂ (energyOutput ε hε hbar coupling t u) (energyOutput ε hε hbar coupling t v) := rfl

theorem homogeneous_represents_form (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (x : (homogeneousHamiltonian ε hε hbar coupling t).domain) (v : FormSpace ε hε hbar coupling t) :
    inner ℂ (energyOutput ε hε hbar coupling t (homogeneousFormLift ε hε hbar coupling t x))
      (energyOutput ε hε hbar coupling t v) =
    inner ℂ (homogeneousHamiltonian ε hε hbar coupling t x) (embedding ε hε hbar coupling t v) := by
  have hp : inner ℂ (homogeneousFormLift ε hε hbar coupling t x) v -
      inner ℂ (x:Hilbert) (embedding ε hε hbar coupling t v) =
      inner ℂ (homogeneousHamiltonian ε hε hbar coupling t x) (embedding ε hε hbar coupling t v) :=
    hamiltonian_form_pairing _ _ _ x v
  rw [form_inner_identity ε hε hbar coupling t,
    homogeneous_lift_embedding ε hε hbar coupling t, add_sub_cancel_left] at hp
  exact hp

theorem homogeneous_energy_expectation (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (x : (homogeneousHamiltonian ε hε hbar coupling t).domain) :
    (inner ℂ (homogeneousHamiltonian ε hε hbar coupling t x) (x:Hilbert)).re =
      ‖energyOutput ε hε hbar coupling t (homogeneousFormLift ε hε hbar coupling t x)‖^2 := by
  have hp := homogeneous_represents_form ε hε hbar coupling t x
    (homogeneousFormLift ε hε hbar coupling t x)
  rw [homogeneous_lift_embedding ε hε hbar coupling t] at hp
  rw [← hp]
  exact inner_self_eq_norm_sq (𝕜 := ℂ)
    (energyOutput ε hε hbar coupling t (homogeneousFormLift ε hε hbar coupling t x))

theorem homogeneous_domain_characterization (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (u : FormSpace ε hε hbar coupling t) (y : Hilbert) :
    (∃ hx : embedding ε hε hbar coupling t u ∈ (homogeneousHamiltonian ε hε hbar coupling t).domain,
      homogeneousHamiltonian ε hε hbar coupling t ⟨embedding ε hε hbar coupling t u,hx⟩ = y) ↔
    ∀ v, inner ℂ (energyOutput ε hε hbar coupling t u) (energyOutput ε hε hbar coupling t v) =
      inner ℂ y (embedding ε hε hbar coupling t v) := by
  constructor
  · rintro ⟨hx, hy⟩ v
    have hl : homogeneousFormLift ε hε hbar coupling t
        ⟨embedding ε hε hbar coupling t u,hx⟩ = u :=
      embedding_injective ε hε hbar coupling t (homogeneous_lift_embedding ε hε hbar coupling t _)
    have hp := homogeneous_represents_form ε hε hbar coupling t
      ⟨embedding ε hε hbar coupling t u,hx⟩ v
    rwa [hl, hy] at hp
  · intro hq
    have hq' : ∀ v, inner ℂ u v -
        inner ℂ (embedding ε hε hbar coupling t u) (embedding ε hε hbar coupling t v) =
        inner ℂ y (embedding ε hε hbar coupling t v) := by
      intro v
      rw [form_inner_identity ε hε hbar coupling t, add_sub_cancel_left, hq v]
    have hm : embedding ε hε hbar coupling t u ∈
        (homogeneousHamiltonian ε hε hbar coupling t).domain :=
      variational_mem_domain _ _ _ u y hq'
    refine ⟨hm, ?_⟩
    exact variational_value _ _ _ u y hq'

def homogeneousCoreVector (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (f : functionCore ε hε hbar) : FormSpace ε hε hbar coupling t :=
  ⟨WithLp.toLp 2 (coreToHilbert ε hε hbar f,
    coreToJoint ε hε hbar (Real.sqrt (1/2)) (Real.sqrt coupling * Real.exp t) f),
    joint_contains_core ε hε hbar _ _ f⟩

/-- Agreement with the signed energy expression is asserted for nonnegative coupling.
Core form vectors need not themselves belong to the Hamiltonian operator domain. -/
theorem homogeneous_core_energy_agreement (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (hc : 0 ≤ coupling) (f : functionCore ε hε hbar) :
    ‖energyOutput ε hε hbar coupling t (homogeneousCoreVector ε hε hbar coupling t f)‖^2 =
      homogeneousEnergy ε hε hbar coupling t f :=
  joint_norm_energy ε hε hbar coupling t hc f

#print axioms homogeneous_selfAdjoint
#print axioms homogeneous_closed
#print axioms homogeneous_dense_domain
#print axioms homogeneous_positive
#print axioms homogeneous_resolvent_domain
#print axioms homogeneous_resolvent_identity
#print axioms homogeneous_lift_embedding
#print axioms homogeneous_operator_form_dense
#print axioms homogeneous_represents_form
#print axioms homogeneous_energy_expectation
#print axioms homogeneous_domain_characterization
#print axioms homogeneous_core_energy_agreement

end
end UnifiedTheory.Audit.KFCausalRegularizedHamiltonian

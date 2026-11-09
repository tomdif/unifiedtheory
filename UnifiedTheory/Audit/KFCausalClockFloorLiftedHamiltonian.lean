/- The actual Hamiltonian realized on the completed form space, with a
closed dense domain and a proved bridge to physical Hamiltonian outputs. -/
import UnifiedTheory.Audit.KFCausalMassFormOperator
import UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
import UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonianBridge
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "A" => referenceShift ε hε h hne hh m g k
local notation "P" => referenceInverse ε hε h hne hh m g k
local notation "H" => hamiltonian ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k

def liftedHamiltonian (s : ℝ) : V →ₗ.[ℂ] V := KFCausalMassFormOperator.operator M (Q s)

theorem mass_injective : Function.Injective M :=
  KFCausalMassGram.gram_injective J (embedding_injective ε hε h hne hh m g k 0)

theorem lifted_graph_iff (s : ℝ) (w v : V) :
    (w,v) ∈ (liftedHamiltonian ε hε h hne hh m g k s).graph ↔ Q s w = M v :=
  KFCausalMassFormOperator.graph_iff M (Q s) (mass_injective ε hε h hne hh m g k) w v

theorem lifted_closed (s : ℝ) : (liftedHamiltonian ε hε h hne hh m g k s).IsClosed :=
  KFCausalMassFormOperator.operator_closed M (Q s) (mass_injective ε hε h hne hh m g k)

theorem lifted_dense (s : ℝ) : Dense ((liftedHamiltonian ε hε h hne hh m g k s).domain : Set V) := by
  have hp : Function.Surjective (P 1 s) := by
    intro w
    exact ⟨A 1 s w,referenceInverse_left ε hε h hne hh m g k 1 s (by norm_num) w⟩
  exact KFCausalMassFormOperator.operator_dense M (Q s) (P 1 s)
    (mass_injective ε hε h hne hh m g k) (mass_dense ε hε h hne hh m g k) hp 1
    (fun w => referenceInverse_right ε hε h hne hh m g k 1 s (by norm_num) w)

theorem physical_graph_iff (s : ℝ) (w v : V) :
    (w,v) ∈ (liftedHamiltonian ε hε h hne hh m g k s).graph ↔
      (J w,J v) ∈ (H s).graph := by
  have hp := hamiltonian_reference_domain ε hε h hne hh m g k s w (J v)
  have hrep : Q s w = M v ↔ ∀ y, inner ℂ w (Q s y) = inner ℂ (J v) (J y) := by
    constructor
    · intro hw y
      have hs : inner ℂ w (Q s y) = inner ℂ (Q s w) y :=
        (KFCausalShiftedForm.formOperator_inner_symm
          (staticMap ε hε h hne hh m g k) (growingMap ε hε h hne hh m g k) s w y).symm
      exact hs.trans ((congrArg (fun z : V => inner ℂ z y) hw).trans
        (mass_left_pairing ε hε h hne hh m g k v y))
    · intro hw
      apply ext_inner_right ℂ
      intro y
      exact (KFCausalShiftedForm.formOperator_inner_symm
        (staticMap ε hε h hne hh m g k) (growingMap ε hε h hne hh m g k) s w y).trans
        ((hw y).trans (mass_left_pairing ε hε h hne hh m g k v y).symm)
  exact (lifted_graph_iff ε hε h hne hh m g k s w v).trans
    (hrep.trans (hp.symm.trans (KFCausalMassFormOperator.graph_domain_iff (H s) (J w) (J v)).symm))

theorem transport_lifted_graph (a s t : ℝ) (ha : 0 < a) (w v : V)
    (hw : (w,v) ∈ (liftedHamiltonian ε hε h hne hh m g k s).graph) :
    (S a s t w,v+a • w-a • S a s t w) ∈
      (liftedHamiltonian ε hε h hne hh m g k t).graph := by
  apply (lifted_graph_iff ε hε h hne hh m g k t _ _).mpr
  have hi (x : V) : a • M (S a s t x)+Q t (S a s t x) = a • M x+Q s x :=
    congrArg (fun T : V →L[ℂ] V => T x)
      (transport_intertwines ε hε h hne hh m g k a s t ha)
  exact KFCausalMassFormOperator.transport_relation M (Q s) (Q t) (S a s t) a hi w v
    ((lifted_graph_iff ε hε h hne hh m g k s w v).mp hw)

theorem transport_lifted_domain_iff (a s t : ℝ) (ha : 0 < a) (w : V) :
    S a s t w ∈ (liftedHamiltonian ε hε h hne hh m g k t).domain ↔
      w ∈ (liftedHamiltonian ε hε h hne hh m g k s).domain := by
  apply KFCausalMassFormOperator.domain_transport_iff
    (liftedHamiltonian ε hε h hne hh m g k s) (liftedHamiltonian ε hε h hne hh m g k t)
    (S a s t) (S a t s)
    (fun x v hx => ⟨_,transport_lifted_graph ε hε h hne hh m g k a s t ha x v hx⟩)
    (fun x v hx => ⟨_,transport_lifted_graph ε hε h hne hh m g k a t s ha x v hx⟩)
  intro x
  have hc := congrArg (fun T : V →L[ℂ] V => T x)
    (transport_compose ε hε h hne hh m g k a s t s ha)
  have he := congrArg (fun T : V →L[ℂ] V => T x)
    (transport_initial ε hε h hne hh m g k a s ha)
  exact hc.trans he

#print axioms mass_injective
#print axioms lifted_graph_iff
#print axioms lifted_closed
#print axioms lifted_dense
#print axioms physical_graph_iff
#print axioms transport_lifted_graph
#print axioms transport_lifted_domain_iff
end
end UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian

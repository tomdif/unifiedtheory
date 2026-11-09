/- Bounded physical Hamiltonian output after an initial shifted resolvent,
derived from the proved lifted-domain propagation and a physical adjoint. -/
import UnifiedTheory.Audit.KFCausalLiftedToPhysicalDomain
import UnifiedTheory.Audit.KFCausalClockFloorForwardStrongDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorPhysicalGraphEvolution
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormLinearity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian)
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "A" => referenceShift ε hε h hne hh m g k
local notation "P" => referenceInverse ε hε h hne hh m g k
local notation "R" => shiftedResolvent ε hε h hne hh m g k
local notation "L" => liftedHamiltonian ε hε h hne hh m g k
local notation "H" => hamiltonian ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k

theorem shift_symmetric (a t : ℝ) (x y : V) :
    inner ℂ (A a t x) y = inner ℂ x (A a t y) :=
  KFCausalSplitTargetShiftedForm.shiftForm_inner_symm J
    (staticMap ε hε h hne hh m g k) (growingMap ε hε h hne hh m g k) a t x y

theorem shifted_lift_domain (a t : ℝ) (ha : 0 < a) (v : V) :
    P a t (M v) ∈ (L t).domain :=
  LinearPMap.mem_domain_of_mem_graph (KFCausalMassFormOperator.shifted_resolves
    M (Q t) (P a t) (mass_injective ε hε h hne hh m g k) a
    (referenceInverse_right ε hε h hne hh m g k a t ha) v)

theorem shifted_graph_mass (a t : ℝ) (x y : V) (hg : (x,y) ∈ (L t).graph) :
    M (a • x+y) = A a t x :=
  KFCausalLiftedToPhysicalDomain.mass_shift M (Q t) a x y
    ((lifted_graph_iff ε hε h hne hh m g k t x y).mp hg)

theorem resolvent_embedding (a t : ℝ) (v : V) :
    R a t (J v) = J (P a t (M v)) := rfl

theorem exists_graph_evolution (a s t : ℝ) (ha : 0 < a) (hst : s ≤ t) :
    ∃ E : Hilbert →L[ℂ] Hilbert, ∀ v : Hilbert, (U s t (R a s v),E v) ∈ (H t).graph :=
  KFCausalLiftedToPhysicalDomain.exists_graph_evolution J
    (embedding_injective ε hε h hne hh m g k 0)
    (KFCausalClockFloorAveragedFormGeometry.embedding_dense ε hε h hne hh m g k 0)
    M (A a s) (A a t) (P a s) (L s) (L t) (H t)
    (U s t : Hilbert →L[ℂ] Hilbert) (R a s)
    (formLinearMap ε hε h hne hh m g k s t) a
    (mass_left_pairing ε hε h hne hh m g k)
    (shift_symmetric ε hε h hne hh m g k a s)
    (shift_symmetric ε hε h hne hh m g k a t)
    (referenceInverse_right ε hε h hne hh m g k a s ha)
    (lifted_closed ε hε h hne hh m g k t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_closed ε hε h hne hh m g k t)
    (shifted_graph_mass ε hε h hne hh m g k a t)
    (fun x y hg => (physical_graph_iff ε hε h hne hh m g k t x y).mp hg)
    (shifted_lift_domain ε hε h hne hh m g k a s ha)
    (KFCausalClockFloorForwardStrongDynamics.lifted_domain ε hε h hne hh m g k s t hst)
    (fun x => (evolution_embedding ε hε h hne hh m g k s t x).symm)
    (resolvent_embedding ε hε h hne hh m g k a s)

#print axioms shift_symmetric
#print axioms shifted_lift_domain
#print axioms shifted_graph_mass
#print axioms resolvent_embedding
#print axioms exists_graph_evolution
end
end UnifiedTheory.Audit.KFCausalClockFloorPhysicalGraphEvolution

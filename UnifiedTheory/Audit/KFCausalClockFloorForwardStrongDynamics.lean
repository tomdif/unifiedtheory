/- Forward lifted-domain propagation and the strong physical Schrodinger
equation for lifted-domain initial states. This does not assert propagation
for every state in the full physical Hamiltonian domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorLimitDomain
import UnifiedTheory.Audit.KFCausalPropagatedStrongEquation
import UnifiedTheory.Audit.KFCausalClockFloorDomainSchrodinger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorForwardStrongDynamics
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian)
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "L" => liftedHamiltonian ε hε h hne hh m g k
local notation "H" => hamiltonian ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

theorem lifted_domain (s t : ℝ) (hst : s ≤ t) (x : (L s).domain) :
    F s t x ∈ (L t).domain := by
  have hc : S 1 t s (F s t x) ∈ (L s).domain := by
    have hd := KFCausalClockFloorLimitDomain.coordinate_domain ε hε h hne hh m g k
      1 s s t (by norm_num) hst x t ⟨hst,le_rfl⟩
    simpa only [transport_initial ε hε h hne hh m g k 1 s (by norm_num),
      ContinuousLinearMap.one_apply] using hd
  exact KFCausalPropagatedStrongEquation.inverse_coordinate_domain (L s).domain (L t).domain
    (S 1 s t) (S 1 t s)
    (transport_lifted_domain_iff ε hε h hne hh m g k 1 s t (by norm_num))
    (KFCausalClockFloorFixedDomainApproximation.transport_inverse ε hε h hne hh m g k 1 s t (by norm_num))
    (F s t x) hc

theorem physical_domain (s t : ℝ) (hst : s ≤ t) (x : (L s).domain) :
    U s t (J x) ∈ (H t).domain := by
  have hd := KFCausalPropagatedStrongEquation.embedding_domain (L t) (H t) J
    (fun w v hw => (physical_graph_iff ε hε h hne hh m g k t w v).mp hw)
    ⟨F s t x,lifted_domain ε hε h hne hh m g k s t hst x⟩
  simpa only [evolution_embedding] using hd

theorem forward_schrodinger (s t : ℝ) (hst : s ≤ t) (x : (L s).domain) :
    ∃ hx : U s t (J x) ∈ (H t).domain,
      HasDerivAt (fun r => U s r (J x)) (c • H t ⟨U s t (J x),hx⟩) t := by
  let hx := physical_domain ε hε h hne hh m g k s t hst x
  exact ⟨hx,KFCausalPropagatedStrongEquation.at_propagated_domain
    (fun s t => (U s t : Hilbert →L[ℂ] Hilbert)) H c
    (evolution_compose ε hε h hne hh m g k)
    (KFCausalClockFloorDomainSchrodinger.hamiltonian_initial ε hε h hne hh m g k)
    s t (J x) hx⟩

theorem regular_initial_states_dense (s : ℝ) :
    DenseRange (fun x : (L s).domain => J x) :=
  KFCausalPropagatedStrongEquation.embedded_domain_dense (L s) J
    (lifted_dense ε hε h hne hh m g k s)
    (KFCausalClockFloorAveragedFormGeometry.embedding_dense ε hε h hne hh m g k 0)

theorem forward_schrodinger_of_regular_output (s t : ℝ) (hst : s ≤ t)
    (x : (H s).domain) (hout : H s x ∈ range J) :
    ∃ hx : U s t x ∈ (H t).domain,
      HasDerivAt (fun r => U s r x) (c • H t ⟨U s t x,hx⟩) t := by
  let lift := KFCausalClockFloorAveragedHamiltonianBridge.referenceLift ε hε h hne hh m g k s
  have hlift := KFCausalClockFloorAveragedHamiltonianBridge.embedding_referenceLift
    ε hε h hne hh m g k s
  have hd := KFCausalPropagatedStrongEquation.lifted_domain_of_output_range
    (L s) (H s) J lift (physical_graph_iff ε hε h hne hh m g k s) hlift x hout
  have hj : J (lift x) = (x:Hilbert) := hlift x
  simpa only [hj] using forward_schrodinger ε hε h hne hh m g k s t hst ⟨lift x,hd⟩

#print axioms lifted_domain
#print axioms physical_domain
#print axioms forward_schrodinger
#print axioms regular_initial_states_dense
#print axioms forward_schrodinger_of_regular_output
end
end UnifiedTheory.Audit.KFCausalClockFloorForwardStrongDynamics

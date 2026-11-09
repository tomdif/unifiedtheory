/- Forward propagation of the full physical Hamiltonian domain and the
strong physical Schrodinger equation, with no extra form-output condition. -/
import UnifiedTheory.Audit.KFCausalClockFloorPhysicalGraphEvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorFullDomainDynamics
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "H" => hamiltonian ε hε h hne hh m g k
local notation "R" => shiftedResolvent ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

theorem forward_domain (s t : ℝ) (hst : s ≤ t) (x : (H s).domain) :
    U s t x ∈ (H t).domain :=
  Exists.elim (KFCausalClockFloorPhysicalGraphEvolution.exists_graph_evolution
    ε hε h hne hh m g k 1 s t (by norm_num) hst) (fun E hE =>
      KFCausalEmbeddedGraphExtension.domain_of_resolvent (H s) (H t)
        (U s t : Hilbert →L[ℂ] Hilbert) (R 1 s) E 1
        (fun y => by simpa only [add_comm] using
          shiftedResolvent_left ε hε h hne hh m g k 1 s (by norm_num) y) hE x)

theorem forward_schrodinger (s t : ℝ) (hst : s ≤ t) (x : (H s).domain) :
    ∃ hx : U s t x ∈ (H t).domain,
      HasDerivAt (fun r => U s r x) (c • H t ⟨U s t x,hx⟩) t := by
  let hx := forward_domain ε hε h hne hh m g k s t hst x
  exact ⟨hx,KFCausalPropagatedStrongEquation.at_propagated_domain
    (fun s t => (U s t : Hilbert →L[ℂ] Hilbert)) H c
    (evolution_compose ε hε h hne hh m g k)
    (KFCausalClockFloorDomainSchrodinger.hamiltonian_initial ε hε h hne hh m g k)
    s t x hx⟩

theorem exists_output_bound (s t : ℝ) (hst : s ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : (H s).domain, ∃ hx : U s t x ∈ (H t).domain,
      ‖H t ⟨U s t x,hx⟩‖ ≤ C*(‖(x:Hilbert)‖+‖H s x‖) :=
  Exists.elim (KFCausalClockFloorPhysicalGraphEvolution.exists_graph_evolution
    ε hε h hne hh m g k 1 s t (by norm_num) hst) (fun E hE =>
      KFCausalEmbeddedGraphExtension.exists_output_bound (H s) (H t)
        (U s t : Hilbert →L[ℂ] Hilbert) (R 1 s) E
        (fun y => by simpa only [one_smul,add_comm] using
          shiftedResolvent_left ε hε h hne hh m g k 1 s (by norm_num) y) hE)

#print axioms forward_domain
#print axioms forward_schrodinger
#print axioms exists_output_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorFullDomainDynamics

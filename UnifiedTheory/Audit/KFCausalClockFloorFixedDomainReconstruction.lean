/- A strong solution on the constructed fixed form-operator domain
reconstructs a strong solution for the actual physical Hamiltonian.
This supplies reconstruction and identification, not existence. -/
import UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
import UnifiedTheory.Audit.KFCausalClockFloorStrongSolutionIdentification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorFixedDomainReconstruction
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "S" => transport ε hε h hne hh m g k
local notation "S'" => transportDerivative ε hε h hne hh m g k
local notation "L" => liftedHamiltonian ε hε h hne hh m g k
local notation "H" => hamiltonian ε hε h hne hh m g k
local notation "G" => fixedGenerator ε hε h hne hh m g k
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

theorem physical_reconstruction (a s t : ℝ) (ha : 0 < a) (w : ℝ → V)
    (hw : w t ∈ (L s).domain) (hd : HasDerivAt w (G a s t ⟨w t,hw⟩) t) :
    ∃ hx : J (S a s t (w t)) ∈ (H t).domain,
      HasDerivAt (fun r => J (S a s r (w r)))
        (c • H t ⟨J (S a s t (w t)),hx⟩) t := by
  let x : (L s).domain := ⟨w t,hw⟩
  let v : V := L s x+a • w t-a • S a s t (w t)
  have hg := transport_lifted_graph ε hε h hne hh m g k a s t ha (w t) (L s x)
    ((L s).mem_graph x)
  have hp := (physical_graph_iff ε hε h hne hh m g k t (S a s t (w t)) v).mp hg
  have he : S' a s t (w t)+S a s t (G a s t x) = c • v :=
    (add_comm _ _).trans (transported_action ε hε h hne hh m g k a s t ha x)
  exact KFCausalStrongEvolutionReconstruction.graph_reconstruction
    J (S a s) w (S' a s t) (G a s t x) v c t (H t) hp
    (transport_derivative ε hε h hne hh m g k a s t ha) hd he

theorem solution_matches_evolution (a s : ℝ) (ha : 0 < a) (w : ℝ → V)
    (hw : ∀ t, w t ∈ (L s).domain)
    (hd : ∀ t, HasDerivAt w (G a s t ⟨w t,hw t⟩) t) (t : ℝ) :
    J (S a s t (w t)) =
      KFCausalClockFloorAveragedEvolution.evolution ε hε h hne hh m g k s t (J (w s)) := by
  have hp (r : ℝ) := physical_reconstruction ε hε h hne hh m g k a s r ha w (hw r) (hd r)
  have he := KFCausalClockFloorStrongSolutionIdentification.solution_matches_evolution
    ε hε h hne hh m g k (fun r => J (S a s r (w r)))
    (fun r => (hp r).choose) (fun r => (hp r).choose_spec) s t
  have hi : J (S a s s (w s)) = J (w s) :=
    congrArg (fun T : V →L[ℂ] V => J (T (w s)))
      (transport_initial ε hε h hne hh m g k a s ha)
  exact he.trans (congrArg
    (KFCausalClockFloorAveragedEvolution.evolution ε hε h hne hh m g k s t) hi)

#print axioms physical_reconstruction
#print axioms solution_matches_evolution
end
end UnifiedTheory.Audit.KFCausalClockFloorFixedDomainReconstruction

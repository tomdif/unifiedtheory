/- Every strong physical Hamiltonian solution agrees with the existing
unitary propagator. This uniqueness statement does not assume that the
propagator itself preserves the Hamiltonian domain. -/
import UnifiedTheory.Audit.KFCausalStrongEvolutionReconstruction
import UnifiedTheory.Audit.KFCausalClockFloorBackwardSchrodinger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorStrongSolutionIdentification
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolutionContinuity
open UnifiedTheory.Audit.KFCausalClockFloorBackwardSchrodinger

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "U" => evolution ε hε h hne hh m g k
local notation "H" => hamiltonian ε hε h hne hh m g k
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

theorem backward_transport_derivative_zero (f : ℝ → Hilbert) (s t : ℝ)
    (hf : f s ∈ (H s).domain)
    (hd : HasDerivAt f (c • H s ⟨f s,hf⟩) s) :
    HasDerivAt (fun r => U r t (f r)) 0 s := by
  have hp := KFCausalStrongEvolutionReconstruction.moving_isometry_derivative
    (fun r => U r t)
    (fun x => evolution_initial_time_continuous ε hε h hne hh m g k t x)
    f (c • H s ⟨f s,hf⟩) (-c • U s t (H s ⟨f s,hf⟩)) s hd
    (backward_derivative ε hε h hne hh m g k s t ⟨f s,hf⟩)
  simpa only [map_smul,neg_smul,add_neg_cancel] using hp

theorem solution_matches_evolution (f : ℝ → Hilbert)
    (hf : ∀ r, f r ∈ (H r).domain)
    (hd : ∀ r, HasDerivAt f (c • H r ⟨f r,hf r⟩) r) (s t : ℝ) :
    f t = U s t (f s) := by
  have hz (r : ℝ) : HasDerivAt (fun q => U q t (f q)) 0 r :=
    backward_transport_derivative_zero ε hε h hne hh m g k f r t (hf r) (hd r)
  have he := is_const_of_deriv_eq_zero (fun r => (hz r).differentiableAt)
    (fun r => (hz r).deriv) t s
  have hi : U t t (f t) = f t :=
    congrArg (fun A : Hilbert →L[ℂ] Hilbert => A (f t))
      (evolution_initial ε hε h hne hh m g k t)
  exact hi.symm.trans he

#print axioms backward_transport_derivative_zero
#print axioms solution_matches_evolution
end
end UnifiedTheory.Audit.KFCausalClockFloorStrongSolutionIdentification

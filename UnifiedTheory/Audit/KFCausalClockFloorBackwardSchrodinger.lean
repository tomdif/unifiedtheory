/- The actual full propagator satisfies the strong backward Schrodinger
 equation on the entire Hamiltonian domain at the varying initial time. -/
import UnifiedTheory.Audit.KFCausalClockFloorDomainSchrodinger
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolutionContinuity
import UnifiedTheory.Audit.KFCausalStrongIsometryDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorBackwardSchrodinger
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolutionContinuity
open UnifiedTheory.Audit.KFCausalClockFloorDomainSchrodinger

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "U" => evolution ε hε h hne hh m g k
local notation "H" => hamiltonian ε hε h hne hh m g k
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

theorem backward_derivative (s t : ℝ) (x : (H s).domain) :
    HasDerivAt (fun r => U r t (x:Hilbert)) (-c • U s t (H s x)) s := by
  have h0 : (x:Hilbert)-U s s (x:Hilbert) = 0 := by
    have hi := congrArg (fun P : Hilbert →L[ℂ] Hilbert => P (x:Hilbert))
      (evolution_initial ε hε h hne hh m g k s)
    change U s s (x:Hilbert) = (x:Hilbert) at hi
    rw [hi,sub_self]
  have hd := KFCausalStrongIsometryDerivative.derivative_at_zero_vector
    (fun r => U r t) (fun f => evolution_initial_time_continuous ε hε h hne hh m g k t f)
    (fun r => (x:Hilbert)-U s r (x:Hilbert)) (-(c • H s x)) s
    (by simpa only [zero_sub] using
      (hasDerivAt_const s (x:Hilbert)).sub (hamiltonian_initial ε hε h hne hh m g k s x)) h0
  have he (r : ℝ) : U r t ((x:Hilbert)-U s r (x:Hilbert)) =
      U r t (x:Hilbert)-U s t (x:Hilbert) := by
    have hc := congrArg (fun P : Hilbert →L[ℂ] Hilbert => P (x:Hilbert))
      (evolution_compose ε hε h hne hh m g k s r t)
    change U r t (U s r (x:Hilbert)) = U s t (x:Hilbert) at hc
    rw [map_sub,hc]
  have hp := hd.add_const (U s t (x:Hilbert))
  simpa only [he,sub_add_cancel,map_neg,map_smul,neg_smul] using hp

#print axioms backward_derivative
end
end UnifiedTheory.Audit.KFCausalClockFloorBackwardSchrodinger

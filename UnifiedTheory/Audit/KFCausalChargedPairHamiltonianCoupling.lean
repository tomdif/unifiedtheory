/- The complete charge-averaged Hamiltonian form couples the centered
state to the explicit zero-charge quadratic state outside the restricted
neutral closure. All kinetic cross terms cancel by proved coordinate
symmetries; the full pairing therefore has strictly negative real part
at every time for the unit potential couplings. -/
import UnifiedTheory.Audit.KFCausalChargedPairKineticCancellation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalChargedPairHamiltonianCoupling
noncomputable section
open MeasureTheory
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalChargedPairHamiltonianForm
open KFCausalChargedPairKineticPairing
open KFCausalChargedPairKineticCancellation
open KFCausalChargedPairPotentialCoupling (potentialPairing)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
variable (hb : |h| ≤ 2*Real.pi*ε/3)

theorem clock_factor_zero : factorPairing ε a h hε ha hh hb 0 = 0 := by
  rw [clock_pairing,clock_integral_zero]

theorem static_pair_zero :
    factorPairing ε a h hε ha hh hb 1+factorPairing ε a h hε ha hh hb 2 = 0 := by
  have h0 := momentum_pairing ε a h hε ha hh hb 0
  have h1 := momentum_pairing ε a h hε ha hh hb 1
  change factorPairing ε a h hε ha hh hb 1 =
    ∫ x, momentumDensity ε a h (modelDirections 0) x at h0
  change factorPairing ε a h hε ha hh hb 2 =
    ∫ x, momentumDensity ε a h (modelDirections 1) x at h1
  rw [h0,h1,← integral_add (momentumDensity_integrable ε a h hε ha hh hb 0)
    (momentumDensity_integrable ε a h hε ha hh hb 1)]
  exact static_integral_zero ε a h hε ha hh hb

theorem growing_pair_zero :
    factorPairing ε a h hε ha hh hb 3+factorPairing ε a h hε ha hh hb 4 = 0 := by
  have h2 := momentum_pairing ε a h hε ha hh hb 2
  have h3 := momentum_pairing ε a h hε ha hh hb 3
  change factorPairing ε a h hε ha hh hb 3 =
    ∫ x, momentumDensity ε a h (modelDirections 2) x at h2
  change factorPairing ε a h hε ha hh hb 4 =
    ∫ x, momentumDensity ε a h (modelDirections 3) x at h3
  rw [h2,h3,← integral_add (momentumDensity_integrable ε a h hε ha hh hb 2)
    (momentumDensity_integrable ε a h hε ha hh hb 3)]
  exact growing_integral_zero ε a h

theorem kineticPairing_zero (t : ℝ) :
    kineticPairing ε a h hε ha hh hb t = 0 := by
  unfold kineticPairing
  rw [clock_factor_zero,zero_add,static_pair_zero,growing_pair_zero]
  simp

theorem formPairing_eq_potential (t : ℝ) :
    formPairing ε a h hε ha hh hb 1 1 1 t =
      (Real.exp (2*t):ℂ)*potentialPairing ε a h hε ha hh hb := by
  rw [unit_decomposition,kineticPairing_zero,zero_add]

theorem formPairing_re_negative (t : ℝ) :
    (formPairing ε a h hε ha hh hb 1 1 1 t).re < 0 := by
  rw [formPairing_eq_potential]
  exact potential_contribution_re_negative ε a h hε ha hh hb t

theorem formPairing_ne_zero (t : ℝ) :
    formPairing ε a h hε ha hh hb 1 1 1 t ≠ 0 := by
  intro hz
  have hn := formPairing_re_negative ε a h hε ha hh hb t
  rw [hz] at hn
  exact (lt_irrefl 0) hn

#print axioms clock_factor_zero
#print axioms static_pair_zero
#print axioms growing_pair_zero
#print axioms kineticPairing_zero
#print axioms formPairing_eq_potential
#print axioms formPairing_re_negative
#print axioms formPairing_ne_zero
end
end UnifiedTheory.Audit.KFCausalChargedPairHamiltonianCoupling

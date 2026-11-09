import UnifiedTheory.Audit.KFCausalOccupationSpectralSearch
import UnifiedTheory.Audit.KFCausalFreeChargedNormalForm

open UnifiedTheory.Audit
open KFCausalOccupationSpectralSearch KFCausalFreeChargedNormalForm

#print axioms neutralOneEquiv
#print axioms neutralHamiltonian_eq_matrix
#print axioms neutralHamiltonian_no_quadratic
#print axioms similar_affine_idempotent_quadratic
#print axioms no_affine_idempotent_similarity
#print axioms squeeze_inverse
#print axioms squeeze_symplectic
#print axioms squeeze_charge_equivariant
#print axioms kinetic_normal_form
#print axioms free_hamiltonian_normal_form
#print axioms free_clock_rate_zero
#print axioms free_hamiltonian_independent_clock_momentum
#print axioms balanced_charged_count
#print axioms chargedPairSeries_euler
#print axioms coeff_chargedPairSeries

example : Fintype.card (BalancedCharged 4) = 25 := by
  rw [balanced_charged_count]
  norm_num

example : PowerSeries.coeff 4 chargedPairSeries = 25 := by
  rw [coeff_chargedPairSeries, balanced_charged_count]
  norm_num

-- This rules out every invertible change of basis, not merely diagonal relabeling.
example (U V N : Matrix (Fin 3) (Fin 3) ℂ) (hUV : U * V = 1) (hVU : V * U = 1)
    (hN : N * N = N) (e g : ℂ) :
    neutralHamiltonian ≠ U * (e • 1 + g • N) * V :=
  no_affine_idempotent_similarity N U V hN hUV hVU e g

/-
  Scalar support for MICROSCOPIC_SPIN_TWO_SEED.md. Exact four-spin matrices
  are checked separately by the symbolic audit. No many-body phase,
  gravitational constraint, or emergent spacetime theorem is asserted.
-/
import UnifiedTheory.Audit.KFCausalEntangledAcoustic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalMicroscopicSpinTwo
noncomputable section

def quintetPolynomial (c : ℝ) : ℝ := c * (c - 2) / 24
def singletPolynomial (c : ℝ) : ℝ := (c - 2) * (c - 6) / 12

theorem quintet_polynomial_values :
    quintetPolynomial 0 = 0 ∧ quintetPolynomial 2 = 0 ∧ quintetPolynomial 6 = 1 := by
  norm_num [quintetPolynomial]

theorem singlet_polynomial_values :
    singletPolynomial 0 = 1 ∧ singletPolynomial 2 = 0 ∧ singletPolynomial 6 = 0 := by
  norm_num [singletPolynomial]

theorem quintet_idempotent_on_casimir_spectrum (c : ℝ)
    (hc : c = 0 ∨ c = 2 ∨ c = 6) :
    quintetPolynomial c ^ 2 = quintetPolynomial c := by
  rcases hc with rfl | rfl | rfl <;> norm_num [quintetPolynomial]

theorem singlet_quintet_orthogonal_on_spectrum (c : ℝ)
    (hc : c = 0 ∨ c = 2 ∨ c = 6) :
    singletPolynomial c * quintetPolynomial c = 0 := by
  rcases hc with rfl | rfl | rfl <;> norm_num [singletPolynomial, quintetPolynomial]

theorem onsite_energy_nonnegative (mu M K n triplet inactive : ℝ)
    (hm : 0 ≤ mu) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hn : 0 ≤ n) (ht : 0 ≤ triplet) (hi : 0 ≤ inactive) :
    0 ≤ mu * n + M * triplet + K * inactive := by
  positivity

theorem zero_energy_has_no_excited_population (mu n rest : ℝ)
    (hm : 0 < mu) (hn : 0 ≤ n) (hr : 0 ≤ rest)
    (he : mu * n + rest = 0) : n = 0 := by
  nlinarith

theorem onsite_gap_lower_bound (mu M K n triplet inactive : ℝ)
    (hM : mu ≤ M) (hK : mu ≤ K) (ht : 0 ≤ triplet) (hi : 0 ≤ inactive) :
    mu * (n + triplet + inactive) ≤ mu * n + M * triplet + K * inactive := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hM) ht, mul_nonneg (sub_nonneg.mpr hK) hi]

theorem hopping_square_identity (x y : ℝ) :
    (x - y) ^ 2 = x ^ 2 + y ^ 2 - 2 * x * y := by ring

theorem traceless_dyad_norm (x y z : ℝ) :
    (x ^ 2 - y ^ 2) ^ 2 / 2 + (x ^ 2 + y ^ 2 - 2 * z ^ 2) ^ 2 / 6 +
      2 * x ^ 2 * y ^ 2 + 2 * y ^ 2 * z ^ 2 + 2 * z ^ 2 * x ^ 2 =
      (2 / 3 : ℝ) * (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 := by ring

theorem central_difference_energy (a b : ℝ) :
    ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem coupled_strain_lower_bound (field mixing kappa gamma c edge : ℝ)
    (hf : kappa / 8 * edge ≤ field)
    (hm : -(|gamma| * c / 2 * edge) ≤ mixing) :
    (kappa / 4 - |gamma| * c) / 2 * edge ≤ field + mixing := by
  nlinarith

theorem coupled_margin_positive (kappa gamma c : ℝ)
    (h : |gamma| * c < kappa / 4) : 0 < kappa / 4 - |gamma| * c := by
  linarith

theorem dilute_commutator_error (n volume tolerance : ℝ)
    (hv : 0 < volume) (hd : n / volume ≤ tolerance / 2) :
    2 * n / volume ≤ tolerance := by
  have h := (div_le_iff₀ hv).mp hd
  apply (div_le_iff₀ hv).mpr
  nlinarith

theorem quadratic_clock_scaling (a mass hopping momentumSquared : ℝ) (ha : a ≠ 0) :
    (a ^ 2 * mass + hopping * a ^ 2 * momentumSquared) / a ^ 2 =
      mass + hopping * momentumSquared := by
  field_simp

theorem gapped_defect_replacement (energy replaced ground gap : ℝ)
    (hr : replaced = energy - gap) (hg : ground ≤ replaced) :
    ground + gap ≤ energy := by linarith

#print axioms quintet_polynomial_values
#print axioms singlet_polynomial_values
#print axioms quintet_idempotent_on_casimir_spectrum
#print axioms singlet_quintet_orthogonal_on_spectrum
#print axioms onsite_energy_nonnegative
#print axioms zero_energy_has_no_excited_population
#print axioms onsite_gap_lower_bound
#print axioms hopping_square_identity
#print axioms traceless_dyad_norm
#print axioms central_difference_energy
#print axioms coupled_strain_lower_bound
#print axioms coupled_margin_positive
#print axioms dilute_commutator_error
#print axioms quadratic_clock_scaling
#print axioms gapped_defect_replacement

end
end UnifiedTheory.Audit.KFCausalMicroscopicSpinTwo

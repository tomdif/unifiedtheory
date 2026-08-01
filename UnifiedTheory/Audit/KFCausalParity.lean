/-
  Audit/KFCausalParity.lean
  — THE DIMENSIONAL PARITY THEOREM (even case): even-dimensional
    smeared weight systems are INTEGRAL

  The Dowker–Glaser layer coefficients have the closed form
  (derived from their fixing equation, H acting on V^a as a·d;
  validated against all seven rows of Table 1 of 1305.2588 in
  parity_theorem.py):

    C_i^(d) = Σ_{a=0}^{i−1} (−1)^a binom(i−1, a)
              · Π_{j=1}^{n+1} (a·d + 2j) / (2^(n+1)·(n+1)!),
    n = ⌊d/2⌋.

  For EVEN d = 2n every factor is 2(na + j), and the product of the
  shifted integers is a rising factorial:

    Π_{j=1}^{n+1} (2na + 2j) = 2^(n+1) · (n+1)! · binom(na+n+1, n+1)

  (even_layer_product), so each term of C_i is an integer times a
  binomial coefficient (even_dim_coeff_integral): even-dimensional
  weight systems are integral.  This discharges the
  integer-coefficient hypothesis of madic_law (KFCausalMAdicLaw.lean)
  for EVERY even dimension: even-d resonant congruence webs at
  ε = p/m are purely m-adic.  The odd-d complement (denominators are
  pure 2-powers, exactly 2^(n+1+v₂((n+1)!)) — 8, 16, 128 for
  d = 3, 5, 7, matching Table 1) is proven by the arithmetic-
  progression valuation argument in parity_theorem.py's header and
  verified on the grid d ≤ 21; its odd-a step is not yet formalized.

  Zero sorry.  Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalParity

open Finset

/-- **The even-layer product identity**: the layer product at even
dimension d = 2n is 2^(n+1)·(n+1)!·binom(na+n+1, n+1). -/
theorem even_layer_product (n a : ℕ) :
    ∏ j ∈ range (n + 1), (2 * n * a + 2 * (j + 1))
      = 2 ^ (n + 1) * Nat.factorial (n + 1)
        * Nat.choose (n * a + n + 1) (n + 1) := by
  have h1 : ∀ j ∈ range (n + 1),
      2 * n * a + 2 * (j + 1) = 2 * (n * a + 1 + j) := by
    intro j _; ring
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_range]
  have h2 : ∏ j ∈ range (n + 1), (n * a + 1 + j)
      = (n * a + 1).ascFactorial (n + 1) := by
    rw [Nat.ascFactorial_eq_prod_range]
  rw [h2, Nat.ascFactorial_eq_factorial_mul_choose]
  have h3 : n * a + (n + 1) = n * a + n + 1 := by omega
  rw [h3]
  ring

/-- **Even-dimensional coefficients are integral**: the closed-form
sum for C_i at d = 2n, with the exact rational division, equals an
integer (an alternating sum of products of binomials).  Instantiates
madic_law's integer-coefficient hypothesis for every even dimension. -/
theorem even_dim_coeff_integral (n i : ℕ) :
    ∑ a ∈ range i, (-1 : ℚ) ^ a * ((i - 1).choose a : ℚ) *
      (((∏ j ∈ range (n + 1), (2 * n * a + 2 * (j + 1)) : ℕ) : ℚ)
        / ((2 : ℚ) ^ (n + 1) * (Nat.factorial (n + 1) : ℚ)))
    = ((∑ a ∈ range i, (-1 : ℤ) ^ a * ((i - 1).choose a : ℤ) *
        ((n * a + n + 1).choose (n + 1) : ℤ) : ℤ) : ℚ) := by
  have h2 : ((2 : ℚ) ^ (n + 1) * (Nat.factorial (n + 1) : ℚ)) ≠ 0 := by
    have := Nat.factorial_pos (n + 1)
    positivity
  simp only [even_layer_product]
  push_cast
  apply Finset.sum_congr rfl
  intro a _
  field_simp

#print axioms even_layer_product
#print axioms even_dim_coeff_integral

end UnifiedTheory.Audit.KFCausalParity

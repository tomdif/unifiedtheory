/- The circular monomial ordering makes the oscillator triangular.
The lower term decreases both circular degrees. -/
import UnifiedTheory.Audit.KFCausalCircularOscillatorPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCircularOscillatorTriangular
noncomputable section
open MvPolynomial
open KFCausalPlanePolynomialGaussian (Poly)
open KFCausalCircularPolynomialBasis (exponent)
open KFCausalScaledCircularPolynomials (polynomialBasis)
open KFCausalCircularOscillatorPolynomial

theorem basis_apply (c : ℝ) (hc : c ≠ 0) (n : ℕ) :
    polynomialBasis c hc n = change c (monomial (exponent n) 1) := by
  change KFCausalScaledCircularPolynomials.scale c
    (KFCausalCircularPolynomialBasis.polynomialBasis n) = _
  rw [KFCausalCircularPolynomialBasis.polynomialBasis_apply]
  rfl

def energy (c b : ℝ) (n : ℕ) : ℝ :=
  4*b*c^2*((exponent n 0:ℝ)+(exponent n 1:ℝ)+1)

theorem lower_index_lt (n : ℕ) (h0 : exponent n 0 ≠ 0) (h1 : exponent n 1 ≠ 0) :
    exponent.symm (lower (exponent n)) < n := by
  have hpair : Nat.pair (exponent n 0) (exponent n 1) = n := exponent.left_inv n
  change Nat.pair ((lower (exponent n)) 0) ((lower (exponent n)) 1) < n
  simp only [lower, Finsupp.tsub_apply, Finsupp.single_apply]
  norm_num only [Fin.zero_eta, Fin.isValue, ↓reduceIte, Nat.sub_zero]
  have h0' : exponent n 0 - 1 < exponent n 0 := Nat.sub_lt (Nat.pos_of_ne_zero h0) (by omega)
  have h1' : exponent n 1 - 1 < exponent n 1 := Nat.sub_lt (Nat.pos_of_ne_zero h1) (by omega)
  exact lt_of_lt_of_eq ((Nat.pair_lt_pair_left (exponent n 1 - 1) h0').trans
    (Nat.pair_lt_pair_right (exponent n 0) h1')) hpair

theorem triangular (c : ℝ) (hc : c ≠ 0) (b : ℝ) (n : ℕ) :
    oscillator c b (polynomialBasis c hc n) - (energy c b n:ℂ) • polynomialBasis c hc n ∈
      Submodule.span ℂ (polynomialBasis c hc '' Set.Iio n) := by
  rw [basis_apply, monomial_action]
  have he : (energy c b n:ℂ) =
      4*(b:ℂ)*(c:ℂ)^2*((exponent n 0:ℂ)+(exponent n 1:ℂ)+1) := by
    simp [energy]
  rw [he, sub_sub_cancel_left]
  by_cases h0 : exponent n 0 = 0
  · simp [h0]
  by_cases h1 : exponent n 1 = 0
  · simp [h1]
  apply Submodule.neg_mem
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨exponent.symm (lower (exponent n)), lower_index_lt n h0 h1, ?_⟩
  rw [basis_apply, Equiv.apply_symm_apply]

#print axioms lower_index_lt
#print axioms triangular
end
end UnifiedTheory.Audit.KFCausalCircularOscillatorTriangular

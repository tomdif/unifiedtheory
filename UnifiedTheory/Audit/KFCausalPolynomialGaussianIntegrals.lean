/- Polynomial integrability against a positive diagonal real Gaussian.
This supplies actual integrability, rather than a premise on the coupling
integrals used below. -/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalPolynomialGaussianIntegrals
noncomputable section
open MeasureTheory

def weight {n : ℕ} (a : Fin n → ℝ) (u : Fin n → ℝ) : ℝ :=
  ∏ i, Real.exp (-a i * (u i)^2)

theorem scalar_moment_integrable (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Integrable (fun x : ℝ => x^k * Real.exp (-a*x^2)) volume := by
  have hi := integrable_rpow_mul_exp_neg_mul_sq ha
    (show (-1:ℝ) < (k:ℝ) by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  simpa only [Real.rpow_natCast] using hi

theorem moment_integrable (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (k : Fin n → ℕ) :
    Integrable (fun u : Fin n → ℝ => (∏ i, (u i)^(k i))*weight a u) volume := by
  have hi := Integrable.fintype_prod (fun i => scalar_moment_integrable (a i) (ha i) (k i))
  simpa only [Finset.prod_mul_distrib, weight] using hi

theorem polynomial_integrable (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (P : MvPolynomial (Fin n) ℝ) :
    Integrable (fun u : Fin n → ℝ => MvPolynomial.eval u P * weight a u) volume := by
  have hi := integrable_finset_sum P.support
    (fun k _ => (moment_integrable n a ha k).const_mul (P.coeff k))
  convert hi using 1
  funext u
  simp only [MvPolynomial.eval_eq', Finset.sum_mul, mul_assoc]

theorem weight_positive (n : ℕ) (a u : Fin n → ℝ) : 0 < weight a u := by
  exact Finset.prod_pos (fun _ _ => Real.exp_pos _)

theorem weight_continuous (n : ℕ) (a : Fin n → ℝ) : Continuous (weight a) := by
  unfold weight
  fun_prop

#print axioms scalar_moment_integrable
#print axioms moment_integrable
#print axioms polynomial_integrable
#print axioms weight_positive
#print axioms weight_continuous
end
end UnifiedTheory.Audit.KFCausalPolynomialGaussianIntegrals

/- Exact finite Gaussian moment formulas, including polynomial dependence
on an external real parameter. Smoothness follows from a change of scale;
no differentiation under an unevaluated integral is assumed. -/
import UnifiedTheory.Audit.KFCausalPolynomialGaussianIntegrals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalPolynomialGaussianMoments
noncomputable section
open MeasureTheory
open KFCausalPolynomialGaussianIntegrals

def standardMoment (k : ℕ) : ℝ := ∫ x : ℝ, x^k * Real.exp (-x^2)
def scalarFormula (k : ℕ) (a : ℝ) : ℝ :=
  standardMoment k / (Real.sqrt a)^(k+1)

theorem scalar_integral_formula (a : ℝ) (ha : 0 < a) (k : ℕ) :
    (∫ x : ℝ, x^k * Real.exp (-a*x^2)) = scalarFormula k a := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have he : ∀ x : ℝ,
      (Real.sqrt a*x)^k * Real.exp (-(Real.sqrt a*x)^2) =
        (Real.sqrt a)^k * (x^k * Real.exp (-a*x^2)) := by
    intro x
    rw [mul_pow, mul_pow, Real.sq_sqrt ha.le, neg_mul]
    ring
  have hi := Measure.integral_comp_mul_left (fun x : ℝ => x^k * Real.exp (-x^2)) (Real.sqrt a)
  simp_rw [he] at hi
  rw [integral_const_mul, abs_of_pos (inv_pos.2 hs), smul_eq_mul] at hi
  unfold scalarFormula standardMoment
  rw [eq_div_iff (pow_ne_zero _ hs.ne'), pow_succ]
  calc
    _ = ((Real.sqrt a)^k * ∫ x : ℝ, x^k * Real.exp (-a*x^2))*Real.sqrt a := by ring
    _ = _ := by rw [hi]; field_simp

theorem moment_integral_formula (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (k : Fin n → ℕ) :
    (∫ u : Fin n → ℝ, (∏ i, (u i)^(k i))*weight a u) =
      ∏ i, scalarFormula (k i) (a i) := by
  simp_rw [weight, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod (fun i (x : ℝ) =>
    x^(k i)*Real.exp (-a i*x^2))]
  apply Finset.prod_congr rfl
  intro i _
  exact scalar_integral_formula (a i) (ha i) (k i)

def formula {n : ℕ} (P : MvPolynomial (Fin n) (Polynomial ℝ))
    (d : ℝ) (a : Fin n → ℝ) : ℝ :=
  ∑ k ∈ P.support, (P.coeff k).eval d * ∏ i, scalarFormula (k i) (a i)

theorem parameter_polynomial_integrable (n : ℕ)
    (P : MvPolynomial (Fin n) (Polynomial ℝ)) (d : ℝ)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    Integrable (fun u : Fin n → ℝ =>
      MvPolynomial.eval₂ (Polynomial.evalRingHom d) u P * weight a u) volume := by
  simp_rw [MvPolynomial.eval₂_eq_eval_map]
  exact polynomial_integrable n a ha _

theorem parameter_integral_formula (n : ℕ)
    (P : MvPolynomial (Fin n) (Polynomial ℝ)) (d : ℝ)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    (∫ u : Fin n → ℝ,
      MvPolynomial.eval₂ (Polynomial.evalRingHom d) u P * weight a u) =
        formula P d a := by
  simp_rw [MvPolynomial.eval₂_eq', Finset.sum_mul, mul_assoc]
  rw [integral_finset_sum P.support (fun k _ =>
    (moment_integrable n a ha k).const_mul ((Polynomial.evalRingHom d) (P.coeff k)))]
  simp_rw [integral_const_mul, moment_integral_formula n a ha]
  rfl

theorem scalarFormula_smooth (k : ℕ) (a : ℝ) (ha : 0 < a) :
    ContDiffAt ℝ ⊤ (scalarFormula k) a := by
  unfold scalarFormula
  exact contDiffAt_const.div
    ((contDiffAt_id.sqrt ha.ne').pow (k+1))
    (pow_ne_zero _ (Real.sqrt_pos.2 ha).ne')

theorem formula_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (P : MvPolynomial (Fin n) (Polynomial ℝ))
    (d : E → ℝ) (a : E → Fin n → ℝ) (x : E)
    (hd : ContDiffAt ℝ ⊤ d x) (ha : ∀ i, ContDiffAt ℝ ⊤ (fun y => a y i) x)
    (hp : ∀ i, 0 < a x i) :
    ContDiffAt ℝ ⊤ (fun y => formula P (d y) (a y)) x := by
  unfold formula
  apply ContDiffAt.sum
  intro k _
  have hc : ContDiffAt ℝ ⊤ (fun y => (P.coeff k).eval (d y)) x := by
    have hh := ((P.coeff k).contDiff_aeval (𝕜 := ℝ) ⊤).contDiffAt.comp x hd
    simpa only [Polynomial.aeval_def, Polynomial.eval₂_id] using hh
  apply hc.mul
  apply contDiffAt_prod
  intro i _
  have hh := (scalarFormula_smooth (k i) (a x i) (hp i)).comp x (ha i)
  exact hh

#print axioms scalar_integral_formula
#print axioms moment_integral_formula
#print axioms parameter_polynomial_integrable
#print axioms parameter_integral_formula
#print axioms scalarFormula_smooth
#print axioms formula_smooth
end
end UnifiedTheory.Audit.KFCausalPolynomialGaussianMoments

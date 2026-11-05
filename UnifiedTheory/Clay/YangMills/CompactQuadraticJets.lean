/- Actual all-order source derivatives with a signed quadratic counterterm.
The counterterm polynomials and derivative domination are constructed at each
compact cutoff. No uniform continuum hierarchy bound is inferred. -/
import UnifiedTheory.Clay.YangMills.CompactGibbsSource
import UnifiedTheory.Clay.YangMills.LocalCountertermReflection
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CompactQuadraticJets
noncomputable section
open MeasureTheory Polynomial

/-- A polynomial differential recurrence valid for either sign of q. -/
def wickPolynomial (q : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => X * wickPolynomial q n - C (2 * q) * (wickPolynomial q n).derivative

theorem wickPolynomial_zero (q y : ℝ) : (wickPolynomial q 0).eval y = 1 := by
  simp [wickPolynomial]

theorem wickPolynomial_succ (q y : ℝ) (n : ℕ) :
    (wickPolynomial q (n + 1)).eval y =
      y * (wickPolynomial q n).eval y - 2 * q * (wickPolynomial q n).derivative.eval y := by
  simp only [wickPolynomial, eval_sub, eval_mul, eval_X, eval_C]

theorem wickPolynomial_one (q y : ℝ) : (wickPolynomial q 1).eval y = y := by
  simp [wickPolynomial]

theorem wickPolynomial_two (q y : ℝ) :
    (wickPolynomial q 2).eval y = y ^ 2 - 2 * q := by
  norm_num [wickPolynomial, pow_two]

theorem wickPolynomial_four (q y : ℝ) :
    (wickPolynomial q 4).eval y = y ^ 4 - 12 * q * y ^ 2 + 12 * q ^ 2 := by
  norm_num [wickPolynomial, derivative_sub, derivative_mul]
  ring

section Compact
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def integrand (F : X → ℝ) (q : ℝ) (n : ℕ) (t : ℝ) (x : X) : ℝ :=
  (wickPolynomial q n).eval (F x - 2 * q * t) * Real.exp (t * F x - q * t ^ 2)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem integrand_continuous (F : X → ℝ) (hF : Continuous F) (q : ℝ) (n : ℕ) :
    Continuous (integrand F q n).uncurry := by
  unfold integrand Function.uncurry
  fun_prop

omit [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem integrand_hasDerivAt (F : X → ℝ) (q : ℝ) (n : ℕ) (t : ℝ) (x : X) :
    HasDerivAt (fun s => integrand F q n s x) (integrand F q (n + 1) t x) t := by
  have hl : HasDerivAt (fun s : ℝ => F x - 2 * q * s) (-(2 * q)) t := by
    convert (hasDerivAt_const t (F x)).sub ((hasDerivAt_id t).const_mul (2 * q)) using 1
    ring
  have hp := (wickPolynomial q n).hasDerivAt (F x - 2 * q * t)
  have he : HasDerivAt (fun s : ℝ => s * F x - q * s ^ 2) (F x - 2 * q * t) t := by
    convert ((hasDerivAt_id t).mul_const (F x)).sub
      (((hasDerivAt_id t).pow 2).const_mul q) using 1
    simp only [id_eq]
    ring
  have h := (hp.comp t hl).mul he.exp
  simp only [Function.comp_apply] at h
  convert h using 1
  unfold integrand
  rw [wickPolynomial_succ]
  ring

def jet (F : X → ℝ) (q : ℝ) (n : ℕ) (t : ℝ) : ℝ := ∫ x, integrand F q n t x ∂μ

/-- Compactness proves the domination required for each derivative. -/
theorem jet_hasDerivAt (F : X → ℝ) (hF : Continuous F) (q : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (jet μ F q n) (jet μ F q (n + 1) t) t :=
  CompactGibbsSource.integral_hasDerivAt μ _ _
    (integrand_continuous F hF q n) (integrand_continuous F hF q (n + 1))
    (fun s x => integrand_hasDerivAt F q n s x) t

def sourcePartition (F : X → ℝ) (t : ℝ) : ℝ := ∫ x, Real.exp (t * F x) ∂μ

def renormalized (F : X → ℝ) (q : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-q * t ^ 2) * sourcePartition μ F t

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem jet_zero (F : X → ℝ) (q t : ℝ) : jet μ F q 0 t = renormalized μ F q t := by
  unfold jet integrand renormalized sourcePartition
  simp only [wickPolynomial_zero, one_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [← Real.exp_add]
  congr 1
  ring

/-- Every source derivative is a constructed polynomial insertion under the
original measure. No source differentiability is assumed. -/
theorem iteratedDeriv_eq_jet (F : X → ℝ) (hF : Continuous F) (q : ℝ) (n : ℕ) :
    iteratedDeriv n (renormalized μ F q) = jet μ F q n := by
  induction n with
  | zero => exact funext (fun t => (jet_zero μ F q t).symm)
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext (fun t => (jet_hasDerivAt μ F hF q n t).deriv)

/-- All orders at zero are actual counterterm-polynomial moments. -/
theorem iteratedDeriv_zero_source (F : X → ℝ) (hF : Continuous F) (q : ℝ) (n : ℕ) :
    iteratedDeriv n (renormalized μ F q) 0 =
      ∫ x, (wickPolynomial q n).eval (F x) ∂μ := by
  rw [iteratedDeriv_eq_jet μ F hF q n]
  simp [jet, integrand]

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] in
theorem renormalized_normalized (F : X → ℝ) (q : ℝ) : renormalized μ F q 0 = 1 := by
  simp [renormalized, sourcePartition]

theorem first_derivative (F : X → ℝ) (hF : Continuous F) (q : ℝ) :
    iteratedDeriv 1 (renormalized μ F q) 0 = ∫ x, F x ∂μ := by
  rw [iteratedDeriv_zero_source μ F hF q 1]
  simp only [wickPolynomial_one]

theorem second_derivative (F : X → ℝ) (hF : Continuous F) (q : ℝ) :
    iteratedDeriv 2 (renormalized μ F q) 0 = (∫ x, (F x) ^ 2 ∂μ) - 2 * q := by
  rw [iteratedDeriv_zero_source μ F hF q 2]
  simp only [wickPolynomial_two]
  rw [integral_sub ((hF.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (integrable_const _)]
  simp

theorem fourth_derivative (F : X → ℝ) (hF : Continuous F) (q : ℝ) :
    iteratedDeriv 4 (renormalized μ F q) 0 =
      (∫ x, (F x) ^ 4 ∂μ) - 12 * q * (∫ x, (F x) ^ 2 ∂μ) + 12 * q ^ 2 := by
  rw [iteratedDeriv_zero_source μ F hF q 4]
  simp only [wickPolynomial_four]
  have hi2 : Integrable (fun x => (F x)^2) μ :=
    (hF.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi4 : Integrable (fun x => (F x)^4) μ :=
    (hF.pow 4).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hadd := integral_add (hi4.sub (hi2.const_mul (12 * q)))
    (integrable_const (12 * q ^ 2))
  have hsub := integral_sub hi4 (hi2.const_mul (12 * q))
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul]
  simp

end Compact
end
end UnifiedTheory.Clay.YangMills.CompactQuadraticJets

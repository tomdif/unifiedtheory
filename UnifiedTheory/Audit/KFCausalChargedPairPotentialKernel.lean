/- The exact transverse potential kernel of the paired quadratic state.
Its moment formula includes the r^2 multiplier and the full unit-coupling
potential 1+z^2/2+z^4/4. All five Gaussian integrations are retained. -/
import UnifiedTheory.Audit.KFCausalPolynomialGaussianMoments
import UnifiedTheory.Audit.KFCausalChargedPairTransverseCoupling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalChargedPairPotentialKernel
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalChargedPairCoordinates
open KFCausalPolynomialGaussianIntegrals (weight)
open KFCausalPolynomialGaussianMoments
open KFCausalQuarticPlaneDomination (potential)
open KFCausalRelativeGaussianDifferential (exponent)
open KFCausalMatterOrderedDomain (pointField)

def polynomial : MvPolynomial (Fin 5) (Polynomial ℝ) :=
  let X := fun i : Fin 5 => (MvPolynomial.X i : MvPolynomial (Fin 5) (Polynomial ℝ))
  let C := fun a : ℝ => MvPolynomial.C (Polynomial.C a)
  let V := X 4+MvPolynomial.C Polynomial.X*X 2
  (X 0*X 1-C (1/4)*(X 2^2-X 3^2))^2*(1+C (1/2)*V^2+C (1/4)*V^4)

def widths (α β : ℝ) (r : ℂ) : Fin 5 → ℝ :=
  ![2*wideWidth α r, 2*wideWidth α r, narrowWidth α β r, wideWidth α r, 2*β]

def density (α β : ℝ) (r : ℂ) (u : Transverse) : ℝ :=
  (u 0*u 1-((u 2)^2-(u 3)^2)/4)^2 *
    potential (u 4+fieldSlope r*u 2)*weight (widths α β r) u

def physicalDensity (α β : ℝ) (r : ℂ) (q : Transverse) : ℝ :=
  potential (pointField q) *
    ‖r^2*(pairPolynomial q:ℂ)*Complex.exp (exponent α β 0 r q)‖^2

def kernel (α β : ℝ) (r : ℂ) : ℝ := ∫ q, physicalDensity α β r q

def kernelFormula (α β : ℝ) (r : ℂ) : ℝ :=
  (Complex.normSq r)^2/2 * formula polynomial (fieldSlope r) (widths α β r)

theorem polynomial_eval (d : ℝ) (u : Transverse) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom d) u polynomial =
      (u 0*u 1-((u 2)^2-(u 3)^2)/4)^2*potential (u 4+d*u 2) := by
  simp only [polynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_add, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_one,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X, potential]
  ring

theorem widths_positive (α β : ℝ) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    ∀ i, 0 < widths α β r i := by
  intro i
  fin_cases i <;> dsimp [widths] <;> positivity

theorem density_integrable (α β : ℝ) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    Integrable (density α β r) volume := by
  have hi := parameter_polynomial_integrable 5 polynomial (fieldSlope r) (widths α β r)
    (widths_positive α β r hA hB hβ)
  simpa only [polynomial_eval, density] using hi

theorem density_integral (α β : ℝ) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    (∫ u, density α β r u) = formula polynomial (fieldSlope r) (widths α β r) := by
  have hi := parameter_integral_formula 5 polynomial (fieldSlope r) (widths α β r)
    (widths_positive α β r hA hB hβ)
  simpa only [polynomial_eval, density] using hi

theorem density_reconstruct (α β : ℝ) (r : ℂ) (u : Transverse) :
    physicalDensity α β r (reconstruct r u) = ‖r‖^4*density α β r u := by
  simp only [physicalDensity, field_reconstruct, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, pair_reconstruct,
    gaussian_norm_reconstruct, KFCausalChargedPairTransverseCoupling.gaussian_weight]
  unfold density widths
  ring

theorem kernel_formula (α β : ℝ) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    kernel α β r = kernelFormula α β r := by
  rw [kernel, integral_coordinates r]
  simp_rw [density_reconstruct]
  rw [integral_const_mul, density_integral α β r hA hB hβ]
  unfold kernelFormula
  rw [Complex.normSq_eq_norm_sq]
  ring

theorem density_integral_positive (α β : ℝ) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    0 < ∫ u, density α β r u := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (f := density α β r) (x := ![1,1,0,0,0])
  · unfold density potential
    exact (by fun_prop : Continuous (fun u : Transverse =>
      (u 0*u 1-((u 2)^2-(u 3)^2)/4)^2 *
        (1+(u 4+fieldSlope r*u 2)^2/2+(u 4+fieldSlope r*u 2)^4/4))).mul
      (KFCausalPolynomialGaussianIntegrals.weight_continuous 5 _)
  · exact density_integrable α β r hA hB hβ
  · intro u
    unfold density potential
    exact mul_nonneg (by positivity) (KFCausalPolynomialGaussianIntegrals.weight_positive 5 _ u).le
  · simpa [density, potential, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] using
        (KFCausalPolynomialGaussianIntegrals.weight_positive 5 (widths α β r) ![1,1,0,0,0]).ne'

theorem kernelFormula_positive (α β : ℝ) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β)
    (hr : r ≠ 0) : 0 < kernelFormula α β r := by
  have hi := density_integral_positive α β r hA hB hβ
  rw [density_integral α β r hA hB hβ] at hi
  unfold kernelFormula
  have hn : 0 < Complex.normSq r := Complex.normSq_pos.mpr hr
  positivity

theorem kernelFormula_smooth (α β : ℝ) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    ContDiffAt ℝ ⊤ (kernelFormula α β) r := by
  have hre : ContDiffAt ℝ ⊤ Complex.re r := Complex.reCLM.contDiff.contDiffAt
  have him : ContDiffAt ℝ ⊤ Complex.im r := Complex.imCLM.contDiff.contDiffAt
  have hf := formula_smooth 5 polynomial fieldSlope (widths α β) r
    (by unfold fieldSlope; fun_prop)
    (by intro i; fin_cases i <;> dsimp [widths, narrowWidth, wideWidth] <;> fun_prop)
    (widths_positive α β r hA hB hβ)
  have hp : ContDiffAt ℝ ⊤ (fun z : ℂ => (Complex.normSq z)^2/2) r := by
    simp only [Complex.normSq_apply]
    fun_prop
  exact hp.mul hf

#print axioms polynomial_eval
#print axioms widths_positive
#print axioms density_integrable
#print axioms density_integral
#print axioms density_reconstruct
#print axioms kernel_formula
#print axioms density_integral_positive
#print axioms kernelFormula_positive
#print axioms kernelFormula_smooth
end
end UnifiedTheory.Audit.KFCausalChargedPairPotentialKernel

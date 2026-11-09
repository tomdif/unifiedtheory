/- Exact five-dimensional potential kernel for reciprocal Gaussian widths.
After the determinant-four change of variables, k=1/sqrt(w) enters only
polynomially. The endpoint k=0 gives a positive smooth marginal formula. -/
import UnifiedTheory.Audit.KFCausalPolynomialGaussianMoments
import UnifiedTheory.Audit.KFCausalReciprocalGaussianCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianKernel
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalReciprocalGaussianCoordinates
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalPolynomialGaussianIntegrals (weight)
open KFCausalPolynomialGaussianMoments
open KFCausalQuarticPlaneDomination (potential)
open KFCausalMatterOrderedDomain (pointField)

def polynomial : MvPolynomial (Fin 5) (Polynomial ℝ) :=
  let X := fun i : Fin 5 => (MvPolynomial.X i : MvPolynomial (Fin 5) (Polynomial ℝ))
  let C := fun a : ℝ => MvPolynomial.C (Polynomial.C a)
  let V := X 4+MvPolynomial.C Polynomial.X*X 2
  1+C (1/2)*V^2+C (1/4)*V^4

def widths (α β k : ℝ) (r : ℂ) : Fin 5 → ℝ :=
  ![α*area r, α*area r, narrow α β k r, α*area r, 2*β]

def density (α β k : ℝ) (r : ℂ) (u : Transverse) : ℝ :=
  potential (u 4+(k*fieldSlope r)*u 2)*weight (widths α β k r) u

def physicalDensity (α β w : ℝ) (r : ℂ) (q : Transverse) : ℝ :=
  potential (pointField q) * ‖Complex.exp (exponent α β w r q)‖^2

def kernel (α β w : ℝ) (r : ℂ) : ℝ := ∫ q, physicalDensity α β w r q

def kernelFormula (α β : ℝ) (p : ℝ × ℂ) : ℝ :=
  (1/4:ℝ)*formula polynomial (p.1*fieldSlope p.2) (widths α β p.1 p.2)

theorem polynomial_eval (d : ℝ) (u : Transverse) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom d) u polynomial = potential (u 4+d*u 2) := by
  simp only [polynomial, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_add, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_one,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X, potential]
  ring

theorem widths_positive (α β k : ℝ) (r : ℂ)
    (hA : 0 < narrow α β k r) (hB : 0 < α*area r) (hβ : 0 < β) :
    ∀ i, 0 < widths α β k r i := by
  intro i
  fin_cases i <;> dsimp [widths] <;> positivity

theorem density_integrable (α β k : ℝ) (r : ℂ)
    (hA : 0 < narrow α β k r) (hB : 0 < α*area r) (hβ : 0 < β) :
    Integrable (density α β k r) volume := by
  have hi := parameter_polynomial_integrable 5 polynomial (k*fieldSlope r) (widths α β k r)
    (widths_positive α β k r hA hB hβ)
  simpa only [polynomial_eval, density] using hi

theorem density_integral (α β k : ℝ) (r : ℂ)
    (hA : 0 < narrow α β k r) (hB : 0 < α*area r) (hβ : 0 < β) :
    (∫ u, density α β k r u) = formula polynomial (k*fieldSlope r) (widths α β k r) := by
  have hi := parameter_integral_formula 5 polynomial (k*fieldSlope r) (widths α β k r)
    (widths_positive α β k r hA hB hβ)
  simpa only [polynomial_eval, density] using hi

theorem gaussian_weight (α β k : ℝ) (r : ℂ) (u : Transverse) :
    Real.exp (-diagonalQuadratic α β k r u) = weight (widths α β k r) u := by
  simp only [weight,widths,Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.prod_univ_zero,mul_one,← Real.exp_add]
  congr 1
  change -diagonalQuadratic α β k r u =
    -(α*area r)*u 0^2+(-(α*area r)*u 1^2+
      (-narrow α β k r*u 2^2+(-(α*area r)*u 3^2+-(2*β)*u 4^2)))
  unfold diagonalQuadratic
  ring

theorem density_reconstruct (α β k : ℝ) (hk : k ≠ 0) (r : ℂ) (u : Transverse) :
    physicalDensity α β (1/k^2) r (reconstruct k r u) = density α β k r u := by
  rw [physicalDensity,field_reconstruct,gaussian_norm_reconstruct α β k hk,gaussian_weight]
  rfl

theorem kernel_formula (α β k : ℝ) (hk : k ≠ 0) (r : ℂ)
    (hA : 0 < narrow α β k r) (hB : 0 < α*area r) (hβ : 0 < β) :
    kernel α β (1/k^2) r = kernelFormula α β (k,r) := by
  rw [kernel,integral_coordinates k hk r]
  simp_rw [density_reconstruct α β k hk]
  rw [density_integral α β k r hA hB hβ]
  rfl

theorem kernelFormula_positive (α β k : ℝ) (r : ℂ)
    (hA : 0 < narrow α β k r) (hB : 0 < α*area r) (hβ : 0 < β) :
    0 < kernelFormula α β (k,r) := by
  have hi : 0 < ∫ u, density α β k r u := by
    apply integral_pos_of_integrable_nonneg_nonzero (f := density α β k r) (x := 0)
    · unfold density potential
      exact (by fun_prop : Continuous (fun u : Transverse =>
        1+(u 4+(k*fieldSlope r)*u 2)^2/2+(u 4+(k*fieldSlope r)*u 2)^4/4)).mul
        (KFCausalPolynomialGaussianIntegrals.weight_continuous 5 _)
    · exact density_integrable α β k r hA hB hβ
    · intro u
      unfold density potential
      exact mul_nonneg (by positivity) (KFCausalPolynomialGaussianIntegrals.weight_positive 5 _ u).le
    · simpa [density,potential] using
        (KFCausalPolynomialGaussianIntegrals.weight_positive 5 (widths α β k r) 0).ne'
  rw [density_integral α β k r hA hB hβ] at hi
  exact mul_pos (by norm_num) hi

theorem kernelFormula_smooth (α β : ℝ) (p : ℝ × ℂ)
    (hA : 0 < narrow α β p.1 p.2) (hB : 0 < α*area p.2) (hβ : 0 < β) :
    ContDiffAt ℝ ⊤ (kernelFormula α β) p := by
  have hre : ContDiffAt ℝ ⊤ Complex.re p.2 := Complex.reCLM.contDiff.contDiffAt
  have him : ContDiffAt ℝ ⊤ Complex.im p.2 := Complex.imCLM.contDiff.contDiffAt
  have hf := formula_smooth 5 polynomial (fun q : ℝ × ℂ => q.1*fieldSlope q.2)
    (fun q : ℝ × ℂ => widths α β q.1 q.2) p
    (by unfold fieldSlope; fun_prop)
    (by intro i; fin_cases i <;> dsimp [widths,narrow,area] <;> fun_prop)
    (widths_positive α β p.1 p.2 hA hB hβ)
  exact contDiffAt_const.mul hf

#print axioms polynomial_eval
#print axioms widths_positive
#print axioms density_integrable
#print axioms density_integral
#print axioms gaussian_weight
#print axioms density_reconstruct
#print axioms kernel_formula
#print axioms kernelFormula_positive
#print axioms kernelFormula_smooth
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianKernel

/- Gaussian moments for the complete centered/paired transverse span.
The term linear in the paired polynomial is retained: it is the actual
interference term and need not vanish for the shifted physical Gaussian. -/
import UnifiedTheory.Audit.KFCausalChargedPairPotentialKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPairedSpanMoments
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalChargedPairCoordinates
open KFCausalChargedPairPotentialKernel (widths widths_positive)
open KFCausalPolynomialGaussianIntegrals (weight)
open KFCausalPolynomialGaussianMoments (formula formula_smooth)
open KFCausalQuarticPlaneDomination (potential)

abbrev Coefficients := ℂ × ℂ

def pairedCoordinate (u : Transverse) : ℝ :=
  u 0*u 1-((u 2)^2-(u 3)^2)/4

def polynomial (k : ℕ) : MvPolynomial (Fin 5) (Polynomial ℝ) :=
  let X := fun i : Fin 5 => (MvPolynomial.X i : MvPolynomial (Fin 5) (Polynomial ℝ))
  let C := fun a : ℝ => MvPolynomial.C (Polynomial.C a)
  let V := X 4+MvPolynomial.C Polynomial.X*X 2
  (X 0*X 1-C (1/4)*(X 2^2-X 3^2))^k*(1+C (1/2)*V^2+C (1/4)*V^4)

def moment (α β : ℝ) (k : ℕ) (r : ℂ) : ℝ :=
  formula (polynomial k) (fieldSlope r) (widths α β r)

def momentDensity (α β : ℝ) (k : ℕ) (r : ℂ) (u : Transverse) : ℝ :=
  pairedCoordinate u ^ k * potential (u 4+fieldSlope r*u 2)*weight (widths α β r) u

def mixedCoefficient (c : Coefficients) (r : ℂ) : ℝ :=
  2*(c.1.re*(c.2*r^2).re+c.1.im*(c.2*r^2).im)

def density (α β : ℝ) (c : Coefficients) (r : ℂ) (u : Transverse) : ℝ :=
  ‖c.1+c.2*r^2*(pairedCoordinate u:ℂ)‖^2 *
    potential (u 4+fieldSlope r*u 2)*weight (widths α β r) u

def value (α β : ℝ) (r : ℂ) (c : Coefficients) : ℝ :=
  (Complex.normSq c.1*moment α β 0 r+
    mixedCoefficient c r*moment α β 1 r+
      Complex.normSq (c.2*r^2)*moment α β 2 r)/2

theorem polynomial_eval (k : ℕ) (d : ℝ) (u : Transverse) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom d) u (polynomial k) =
      pairedCoordinate u ^ k*potential (u 4+d*u 2) := by
  simp only [polynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_add, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_one,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X]
  congr 1
  · congr 1
    unfold pairedCoordinate
    ring
  · unfold potential
    ring

theorem moment_integrable (α β : ℝ) (k : ℕ) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    Integrable (momentDensity α β k r) volume := by
  have hi := KFCausalPolynomialGaussianMoments.parameter_polynomial_integrable 5
    (polynomial k) (fieldSlope r) (widths α β r) (widths_positive α β r hA hB hβ)
  simpa only [polynomial_eval, momentDensity] using hi

theorem moment_integral (α β : ℝ) (k : ℕ) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    (∫ u, momentDensity α β k r u) = moment α β k r := by
  have hi := KFCausalPolynomialGaussianMoments.parameter_integral_formula 5
    (polynomial k) (fieldSlope r) (widths α β r) (widths_positive α β r hA hB hβ)
  simpa only [polynomial_eval, momentDensity, moment] using hi

theorem moment_smooth (α β : ℝ) (k : ℕ) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    ContDiffAt ℝ ⊤ (moment α β k) r := by
  have hre : ContDiffAt ℝ ⊤ Complex.re r := Complex.reCLM.contDiff.contDiffAt
  have him : ContDiffAt ℝ ⊤ Complex.im r := Complex.imCLM.contDiff.contDiffAt
  exact formula_smooth 5 (polynomial k) fieldSlope (widths α β) r
    (by unfold fieldSlope; fun_prop)
    (by intro i; fin_cases i <;> dsimp [widths, narrowWidth, wideWidth] <;> fun_prop)
    (widths_positive α β r hA hB hβ)

theorem scalar_norm_expansion (a b : ℂ) (x : ℝ) :
    ‖a+b*(x:ℂ)‖^2 = Complex.normSq a+
      2*(a.re*b.re+a.im*b.im)*x+Complex.normSq b*x^2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem density_expansion (α β : ℝ) (c : Coefficients) (r : ℂ) (u : Transverse) :
    density α β c r u =
      Complex.normSq c.1*momentDensity α β 0 r u+
        mixedCoefficient c r*momentDensity α β 1 r u+
          Complex.normSq (c.2*r^2)*momentDensity α β 2 r u := by
  rw [density, scalar_norm_expansion]
  simp only [momentDensity, mixedCoefficient, pow_zero, pow_one]
  ring

theorem density_integrable (α β : ℝ) (c : Coefficients) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    Integrable (density α β c r) volume := by
  have hi := (((moment_integrable α β 0 r hA hB hβ).const_mul (Complex.normSq c.1)).add
    ((moment_integrable α β 1 r hA hB hβ).const_mul (mixedCoefficient c r))).add
      ((moment_integrable α β 2 r hA hB hβ).const_mul (Complex.normSq (c.2*r^2)))
  exact hi.congr (Filter.Eventually.of_forall (fun u => (density_expansion α β c r u).symm))

theorem value_integral (α β : ℝ) (c : Coefficients) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    value α β r c = (∫ u, density α β c r u)/2 := by
  have hi : Integrable (fun u => Complex.normSq c.1*momentDensity α β 0 r u+
      mixedCoefficient c r*momentDensity α β 1 r u) volume :=
    ((moment_integrable α β 0 r hA hB hβ).const_mul _).add
      ((moment_integrable α β 1 r hA hB hβ).const_mul _)
  simp_rw [density_expansion]
  rw [integral_add hi ((moment_integrable α β 2 r hA hB hβ).const_mul _),
    integral_add ((moment_integrable α β 0 r hA hB hβ).const_mul _)
      ((moment_integrable α β 1 r hA hB hβ).const_mul _)]
  simp_rw [integral_const_mul, moment_integral α β _ r hA hB hβ]
  rfl

theorem value_smooth (α β : ℝ) (r : ℂ) (c : Coefficients)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    ContDiffAt ℝ ⊤ (fun p : ℂ × Coefficients => value α β p.1 p.2) (r,c) := by
  have hre : ContDiff ℝ ⊤ Complex.re := Complex.reCLM.contDiff
  have him : ContDiff ℝ ⊤ Complex.im := Complex.imCLM.contDiff
  have hm (k : ℕ) : ContDiffAt ℝ ⊤ (fun p : ℂ × Coefficients => moment α β k p.1) (r,c) := by
    have he := (moment_smooth α β k r hA hB hβ).comp (r,c)
      (show ContDiffAt ℝ ⊤ (fun p : ℂ × Coefficients => p.1) (r,c) from contDiffAt_fst)
    exact he
  unfold value mixedCoefficient
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
  fun_prop

#print axioms polynomial_eval
#print axioms moment_integrable
#print axioms moment_integral
#print axioms moment_smooth
#print axioms scalar_norm_expansion
#print axioms density_expansion
#print axioms density_integrable
#print axioms value_integral
#print axioms value_smooth
end
end UnifiedTheory.Audit.KFCausalPairedSpanMoments

/- Finite exact Gaussian moments for the four-term span 1,P,P^2,S.
The full Hermitian double sum retains every interference term.
The physical zero-charge corrected quartic is a subfamily. -/
import UnifiedTheory.Audit.KFCausalPairedSpanMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalQuarticSpanMoments
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalChargedPairCoordinates
open KFCausalChargedPairPotentialKernel (widths widths_positive)
open KFCausalPairedSpanMoments (pairedCoordinate)
open KFCausalPolynomialGaussianIntegrals (weight)
open KFCausalPolynomialGaussianMoments (formula formula_smooth)
open KFCausalQuarticPlaneDomination (potential)

abbrev Coefficients := Fin 4 → ℂ
def radialCoordinate (u : Transverse) : ℝ :=
  (u 0)^2+(u 1)^2+((u 2)^2+(u 3)^2)/2
def basis (i : Fin 4) (u : Transverse) : ℝ :=
  ![1,pairedCoordinate u,(pairedCoordinate u)^2,radialCoordinate u] i
def degrees : Fin 4 → ℕ := ![0,2,4,2]
def coefficient (c : Coefficients) (r : ℂ) (i : Fin 4) : ℂ := c i*r^(degrees i)
def profile (r : ℂ) (c : Coefficients) (u : Transverse) : ℂ :=
  ∑ i, coefficient c r i*(basis i u:ℂ)
def basisPolynomial (i : Fin 4) : MvPolynomial (Fin 5) (Polynomial ℝ) :=
  let X := fun j : Fin 5 => (MvPolynomial.X j : MvPolynomial (Fin 5) (Polynomial ℝ))
  let C := fun a : ℝ => MvPolynomial.C (Polynomial.C a)
  let P := X 0*X 1-C (1/4)*(X 2^2-X 3^2)
  ![1,P,P^2,X 0^2+X 1^2+C (1/2)*(X 2^2+X 3^2)] i
def polynomial (i j : Fin 4) : MvPolynomial (Fin 5) (Polynomial ℝ) :=
  basisPolynomial i*basisPolynomial j*KFCausalPairedSpanMoments.polynomial 0
def moment (α β : ℝ) (i j : Fin 4) (r : ℂ) : ℝ :=
  formula (polynomial i j) (fieldSlope r) (widths α β r)
def momentDensity (α β : ℝ) (i j : Fin 4) (r : ℂ) (u : Transverse) : ℝ :=
  basis i u*basis j u*potential (u 4+fieldSlope r*u 2)*weight (widths α β r) u
def crossCoefficient (c : Coefficients) (r : ℂ) (i j : Fin 4) : ℝ :=
  (conj (coefficient c r i)*coefficient c r j).re
def density (α β : ℝ) (c : Coefficients) (r : ℂ) (u : Transverse) : ℝ :=
  ‖profile r c u‖^2*potential (u 4+fieldSlope r*u 2)*weight (widths α β r) u
def value (α β : ℝ) (r : ℂ) (c : Coefficients) : ℝ :=
  (∑ i, ∑ j, crossCoefficient c r i j*moment α β i j r)/2

theorem basisPolynomial_eval (i : Fin 4) (d : ℝ) (u : Transverse) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom d) u (basisPolynomial i) = basis i u := by
  fin_cases i <;> simp [basisPolynomial,basis,pairedCoordinate,radialCoordinate] <;> ring

theorem polynomial_eval (i j : Fin 4) (d : ℝ) (u : Transverse) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom d) u (polynomial i j) =
      basis i u*basis j u*potential (u 4+d*u 2) := by
  simp only [polynomial,MvPolynomial.eval₂_mul,basisPolynomial_eval,
    KFCausalPairedSpanMoments.polynomial_eval,pow_zero,one_mul]

theorem moment_integrable (α β : ℝ) (i j : Fin 4) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    Integrable (momentDensity α β i j r) volume := by
  have hi := KFCausalPolynomialGaussianMoments.parameter_polynomial_integrable 5
    (polynomial i j) (fieldSlope r) (widths α β r) (widths_positive α β r hA hB hβ)
  simpa only [polynomial_eval,momentDensity] using hi

theorem moment_integral (α β : ℝ) (i j : Fin 4) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    (∫ u, momentDensity α β i j r u) = moment α β i j r := by
  have hi := KFCausalPolynomialGaussianMoments.parameter_integral_formula 5
    (polynomial i j) (fieldSlope r) (widths α β r) (widths_positive α β r hA hB hβ)
  simpa only [polynomial_eval,momentDensity,moment] using hi

theorem moment_smooth (α β : ℝ) (i j : Fin 4) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    ContDiffAt ℝ ⊤ (moment α β i j) r := by
  have hre : ContDiffAt ℝ ⊤ Complex.re r := Complex.reCLM.contDiff.contDiffAt
  have him : ContDiffAt ℝ ⊤ Complex.im r := Complex.imCLM.contDiff.contDiffAt
  exact formula_smooth 5 (polynomial i j) fieldSlope (widths α β) r
    (by unfold fieldSlope; fun_prop)
    (by intro k; fin_cases k <;> dsimp [widths,narrowWidth,wideWidth] <;> fun_prop)
    (widths_positive α β r hA hB hβ)

theorem finite_norm_expansion {ι : Type*} [Fintype ι] (a : ι → ℂ) (b : ι → ℝ) :
    ‖∑ i, a i*(b i:ℂ)‖^2 =
      ∑ i, ∑ j, (conj (a i)*a j).re*b i*b j := by
  have hreal (i j : ι) :
      (conj (a i*(b i:ℂ))*(a j*(b j:ℂ))).re = (conj (a i)*a j).re*b i*b j := by
    simp only [map_mul,Complex.conj_ofReal,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im]
    ring
  calc
    _ = (conj (∑ i, a i*(b i:ℂ))*(∑ j, a j*(b j:ℂ))).re := by
      rw [Complex.conj_mul']
      simp only [← Complex.ofReal_pow,Complex.ofReal_re]
    _ = _ := by
      rw [map_sum,Finset.sum_mul]
      simp only [Finset.mul_sum,Complex.re_sum,hreal]

theorem density_expansion (α β : ℝ) (c : Coefficients) (r : ℂ) (u : Transverse) :
    density α β c r u =
      ∑ i, ∑ j, crossCoefficient c r i j*momentDensity α β i j r u := by
  simp only [density,profile,finite_norm_expansion,Finset.sum_mul,crossCoefficient,momentDensity]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem density_integrable (α β : ℝ) (c : Coefficients) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    Integrable (density α β c r) volume := by
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ =>
      (moment_integrable α β i j r hA hB hβ).const_mul (crossCoefficient c r i j)))
  exact hi.congr (Filter.Eventually.of_forall (fun u => (density_expansion α β c r u).symm))

theorem value_integral (α β : ℝ) (c : Coefficients) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    value α β r c = (∫ u, density α β c r u)/2 := by
  simp_rw [density_expansion]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ =>
      (moment_integrable α β i j r hA hB hβ).const_mul (crossCoefficient c r i j)))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ =>
    (moment_integrable α β _ j r hA hB hβ).const_mul _)]
  simp_rw [integral_const_mul,moment_integral α β _ _ r hA hB hβ]
  rfl

theorem value_smooth (α β : ℝ) (r : ℂ) (c : Coefficients)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    ContDiffAt ℝ ⊤ (fun p : ℂ × Coefficients => value α β p.1 p.2) (r,c) := by
  have hre : ContDiff ℝ ⊤ Complex.re := Complex.reCLM.contDiff
  have him : ContDiff ℝ ⊤ Complex.im := Complex.imCLM.contDiff
  have hm (i j : Fin 4) : ContDiffAt ℝ ⊤
      (fun p : ℂ × Coefficients => moment α β i j p.1) (r,c) := by
    have he := (moment_smooth α β i j r hA hB hβ).comp (r,c)
      (show ContDiffAt ℝ ⊤ (fun p : ℂ × Coefficients => p.1) (r,c) from contDiffAt_fst)
    exact he
  unfold value
  apply ContDiffAt.div_const
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  apply ContDiffAt.mul _ (hm i j)
  simp only [crossCoefficient,coefficient,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  fun_prop

#print axioms basisPolynomial_eval
#print axioms polynomial_eval
#print axioms moment_integrable
#print axioms moment_integral
#print axioms moment_smooth
#print axioms finite_norm_expansion
#print axioms density_expansion
#print axioms density_integrable
#print axioms value_integral
#print axioms value_smooth
end
end UnifiedTheory.Audit.KFCausalQuarticSpanMoments

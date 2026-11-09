/- Exact potential-weighted five-dimensional complex Gaussian integral.
The nine polynomial terms retain all mixed moments and are integrated
only after absolute integrability has been established. -/
import UnifiedTheory.Audit.KFCausalComplexGaussianMoments
import UnifiedTheory.Audit.KFCausalQuarticPlaneDomination

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalComplexPotentialGaussian
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalComplexGaussianMoments (value gaussianValue)
open KFCausalQuarticPlaneDomination (potential)

def widths (A B C D : ℂ) : Fin 5 → ℂ := ![A,B,C,A,D]
def powers (m n : ℕ) : Fin 5 → ℕ := ![0,0,m,0,n]
def weight (A B C D : ℂ) (u : Transverse) : ℂ :=
  ∏ i, Complex.exp (-widths A B C D i*(u i:ℂ)^2)
def monomial (A B C D : ℂ) (m n : ℕ) (u : Transverse) : ℂ :=
  (u 2:ℂ)^m*(u 4:ℂ)^n*weight A B C D u

theorem monomial_product (A B C D : ℂ) (m n : ℕ) (u : Transverse) :
    monomial A B C D m n u =
      ∏ i, KFCausalComplexGaussianMoments.moment (widths A B C D i) (powers m n i) (u i) := by
  simp only [KFCausalComplexGaussianMoments.moment,Finset.prod_mul_distrib,
    monomial,powers,Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.prod_univ_zero,pow_zero,one_mul,mul_one,weight]
  rfl

private theorem widths_positive (A B C D : ℂ)
    (hA : 0 < A.re) (hB : 0 < B.re) (hC : 0 < C.re) (hD : 0 < D.re) :
    ∀ i, 0 < (widths A B C D i).re := by
  intro i
  fin_cases i <;> assumption

theorem monomial_integrable (A B C D : ℂ)
    (hA : 0 < A.re) (hB : 0 < B.re) (hC : 0 < C.re) (hD : 0 < D.re) (m n : ℕ) :
    Integrable (monomial A B C D m n) := by
  simp_rw [show monomial A B C D m n = fun u =>
      ∏ i, KFCausalComplexGaussianMoments.moment (widths A B C D i) (powers m n i) (u i)
    from funext (monomial_product A B C D m n)]
  exact Integrable.fintype_prod (fun i => KFCausalComplexGaussianMoments.moment_integrable _
    (widths_positive A B C D hA hB hC hD i) _)

theorem monomial_integral (A B C D : ℂ) (m n : ℕ) :
    (∫ u, monomial A B C D m n u) = value A 0^2*value B 0*value C m*value D n := by
  simp_rw [monomial_product]
  rw [integral_fintype_prod_volume_eq_prod]
  simp only [value,widths,powers,Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.prod_univ_zero,mul_one]
  ring

def degree2 : Fin 9 → ℕ := ![0,0,1,2,0,1,2,3,4]
def degree4 : Fin 9 → ℕ := ![0,2,1,0,4,3,2,1,0]
def coefficient (d : ℝ) : Fin 9 → ℂ :=
  ![1,1/2,(d:ℂ),(d:ℂ)^2/2,1/4,(d:ℂ),3*(d:ℂ)^2/2,(d:ℂ)^3,(d:ℂ)^4/4]
def density (A B C D : ℂ) (d : ℝ) (u : Transverse) : ℂ :=
  (potential (u 4+d*u 2):ℂ)*weight A B C D u

theorem density_decomposition (A B C D : ℂ) (d : ℝ) (u : Transverse) :
    density A B C D d u =
      ∑ i : Fin 9, coefficient d i*monomial A B C D (degree2 i) (degree4 i) u := by
  simp only [density,potential,coefficient,degree2,degree4,Fin.sum_univ_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,monomial]
  push_cast
  ring

theorem density_integrable (A B C D : ℂ)
    (hA : 0 < A.re) (hB : 0 < B.re) (hC : 0 < C.re) (hD : 0 < D.re) (d : ℝ) :
    Integrable (density A B C D d) := by
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    (monomial_integrable A B C D hA hB hC hD (degree2 i) (degree4 i)).const_mul (coefficient d i))
  exact hi.congr (Filter.Eventually.of_forall (fun u => (density_decomposition A B C D d u).symm))

def variance (C D : ℂ) (d : ℝ) : ℂ := 1/(2*D)+(d:ℂ)^2/(2*C)
def formula (A B C D : ℂ) (d : ℝ) : ℂ :=
  gaussianValue A^2*gaussianValue B*gaussianValue C*gaussianValue D*
    (1+variance C D d/2+3*(variance C D d)^2/4)

theorem density_integral (A B C D : ℂ)
    (hA : 0 < A.re) (hB : 0 < B.re) (hC : 0 < C.re) (hD : 0 < D.re) (d : ℝ) :
    (∫ u, density A B C D d u) = formula A B C D d := by
  simp_rw [density_decomposition]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    (monomial_integrable A B C D hA hB hC hD (degree2 i) (degree4 i)).const_mul (coefficient d i))]
  simp_rw [integral_const_mul,monomial_integral]
  simp only [coefficient,degree2,degree4,Fin.sum_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,
    KFCausalComplexGaussianMoments.value_zero A hA,KFCausalComplexGaussianMoments.value_zero B hB,
    KFCausalComplexGaussianMoments.value_zero C hC,KFCausalComplexGaussianMoments.value_zero D hD,
    KFCausalComplexGaussianMoments.value_one C hC,KFCausalComplexGaussianMoments.value_one D hD,
    KFCausalComplexGaussianMoments.value_two C hC,KFCausalComplexGaussianMoments.value_two D hD,
    KFCausalComplexGaussianMoments.value_three C hC,KFCausalComplexGaussianMoments.value_three D hD,
    KFCausalComplexGaussianMoments.value_four C hC,KFCausalComplexGaussianMoments.value_four D hD]
  unfold formula variance
  ring

#print axioms monomial_product
#print axioms monomial_integrable
#print axioms monomial_integral
#print axioms density_decomposition
#print axioms density_integrable
#print axioms density_integral
end
end UnifiedTheory.Audit.KFCausalComplexPotentialGaussian

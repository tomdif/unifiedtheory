/- Exact quartic Gaussian plane integration with two arbitrary complex
linear sources. This retains the mixed source terms and field slope;
no positive-kernel response inequality is asserted. -/
import UnifiedTheory.Audit.KFCausalShiftedComplexGaussianMoments
import UnifiedTheory.Audit.KFCausalComplexPotentialGaussian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalGaussianSourcePlaneKernel
noncomputable section
open MeasureTheory
open KFCausalShiftedComplexGaussianMoments (moment value mass)
open KFCausalComplexPotentialGaussian (degree2 degree4 coefficient)
open KFCausalQuarticPlaneDomination (potential)

def monomial (C D e f : ℂ) (m n : ℕ) (u : Fin 2 → ℝ) : ℂ :=
  ∏ i : Fin 2, moment (![C,D] i) (![e,f] i) (![m,n] i) (u i)

def density (C D e f : ℂ) (L : ℝ) (u : Fin 2 → ℝ) : ℂ :=
  (potential (u 1+L*u 0):ℂ)*
    Complex.exp (-C*(u 0:ℂ)^2+e*(u 0:ℂ))*
    Complex.exp (-D*(u 1:ℂ)^2+f*(u 1:ℂ))

def mean (C D e f : ℂ) (L : ℝ) : ℂ := f/(2*D)+(L:ℂ)*e/(2*C)
def variance (C D : ℂ) (L : ℝ) : ℂ := 1/(2*D)+(L:ℂ)^2/(2*C)
def wick (m s : ℂ) : ℂ := 1+(m^2+s)/2+(m^4+6*m^2*s+3*s^2)/4
def formula (C D e f : ℂ) (L : ℝ) : ℂ :=
  mass C e*mass D f*wick (mean C D e f L) (variance C D L)

theorem monomial_integrable (C D e f : ℂ) (hC : 0 < C.re) (hD : 0 < D.re)
    (m n : ℕ) : Integrable (monomial C D e f m n) := by
  apply Integrable.fintype_prod
  intro i
  apply KFCausalShiftedComplexGaussianMoments.moment_integrable
  fin_cases i <;> assumption

theorem monomial_integral (C D e f : ℂ) (m n : ℕ) :
    (∫ u, monomial C D e f m n u) = value C e m*value D f n := by
  unfold monomial
  rw [integral_fintype_prod_volume_eq_prod]
  simp only [value,Fin.prod_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one]

theorem density_decomposition (C D e f : ℂ) (L : ℝ) (u : Fin 2 → ℝ) :
    density C D e f L u =
      ∑ i : Fin 9, coefficient L i*monomial C D e f (degree2 i) (degree4 i) u := by
  simp only [density,potential,coefficient,degree2,degree4,monomial,moment,
    Fin.sum_univ_succ,Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Fin.prod_univ_zero,add_zero,mul_one]
  push_cast
  ring

theorem density_integrable (C D e f : ℂ) (hC : 0 < C.re) (hD : 0 < D.re)
    (L : ℝ) : Integrable (density C D e f L) := by
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    (monomial_integrable C D e f hC hD (degree2 i) (degree4 i)).const_mul (coefficient L i))
  exact hi.congr (Filter.Eventually.of_forall (fun u => (density_decomposition C D e f L u).symm))

theorem density_integral (C D e f : ℂ) (hC : 0 < C.re) (hD : 0 < D.re)
    (L : ℝ) : (∫ u, density C D e f L u) = formula C D e f L := by
  have hCn : C ≠ 0 := by intro h; simp [h] at hC
  have hDn : D ≠ 0 := by intro h; simp [h] at hD
  simp_rw [density_decomposition]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    (monomial_integrable C D e f hC hD (degree2 i) (degree4 i)).const_mul (coefficient L i))]
  simp_rw [integral_const_mul,monomial_integral]
  simp only [coefficient,degree2,degree4,Fin.sum_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,
    KFCausalShiftedComplexGaussianMoments.value_zero C e hC,
    KFCausalShiftedComplexGaussianMoments.value_zero D f hD,
    KFCausalShiftedComplexGaussianMoments.value_one C e hC,
    KFCausalShiftedComplexGaussianMoments.value_one D f hD,
    KFCausalShiftedComplexGaussianMoments.value_two C e hC,
    KFCausalShiftedComplexGaussianMoments.value_two D f hD,
    KFCausalShiftedComplexGaussianMoments.value_three C e hC,
    KFCausalShiftedComplexGaussianMoments.value_three D f hD,
    KFCausalShiftedComplexGaussianMoments.value_four C e hC,
    KFCausalShiftedComplexGaussianMoments.value_four D f hD]
  unfold formula mean variance wick
  field_simp
  ring

#print axioms monomial_integrable
#print axioms monomial_integral
#print axioms density_decomposition
#print axioms density_integrable
#print axioms density_integral
end
end UnifiedTheory.Audit.KFCausalGaussianSourcePlaneKernel

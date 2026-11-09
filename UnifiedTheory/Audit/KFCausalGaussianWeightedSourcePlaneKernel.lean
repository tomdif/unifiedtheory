/- Exact weighted quartic plane integral with all coherent source moments.
The coefficients are unrestricted here; nonnegativity enters only in the
subsequent energy estimates. All monomials are absolutely integrable. -/
import UnifiedTheory.Audit.KFCausalGaussianSourcePlaneKernel
import UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalGaussianWeightedSourcePlaneKernel
noncomputable section
open MeasureTheory
open KFCausalShiftedComplexGaussianMoments (moment value mass)
open KFCausalComplexPotentialGaussian (degree2 degree4)
open KFCausalGaussianSourcePlaneKernel (monomial monomial_integrable monomial_integral mean variance)
open KFCausalCommonRealGaussianWeightedEnergy (potential)

variable (mass2 quartic vacuum : ℝ)

def coefficient (L : ℝ) : Fin 9 → ℂ :=
  ![(vacuum:ℂ),(mass2:ℂ)/2,(mass2:ℂ)*(L:ℂ),(mass2:ℂ)*(L:ℂ)^2/2,
    (quartic:ℂ)/4,(quartic:ℂ)*(L:ℂ),3*(quartic:ℂ)*(L:ℂ)^2/2,
    (quartic:ℂ)*(L:ℂ)^3,(quartic:ℂ)*(L:ℂ)^4/4]

def density (C D e f : ℂ) (L : ℝ) (u : Fin 2 → ℝ) : ℂ :=
  (potential mass2 quartic vacuum (u 1+L*u 0):ℂ)*
    Complex.exp (-C*(u 0:ℂ)^2+e*(u 0:ℂ))*
    Complex.exp (-D*(u 1:ℂ)^2+f*(u 1:ℂ))

def wick (m s : ℂ) : ℂ := (vacuum:ℂ)+(mass2:ℂ)*(m^2+s)/2+
  (quartic:ℂ)*(m^4+6*m^2*s+3*s^2)/4
def formula (C D e f : ℂ) (L : ℝ) : ℂ :=
  mass C e*mass D f*wick mass2 quartic vacuum (mean C D e f L) (variance C D L)

theorem density_decomposition (C D e f : ℂ) (L : ℝ) (u : Fin 2 → ℝ) :
    density mass2 quartic vacuum C D e f L u =
      ∑ i : Fin 9, coefficient mass2 quartic vacuum L i*monomial C D e f (degree2 i) (degree4 i) u := by
  simp only [density,potential,coefficient,degree2,degree4,monomial,moment,
    Fin.sum_univ_succ,Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Fin.prod_univ_zero,add_zero,mul_one]
  push_cast
  ring

theorem density_integrable (C D e f : ℂ) (hC : 0 < C.re) (hD : 0 < D.re)
    (L : ℝ) : Integrable (density mass2 quartic vacuum C D e f L) := by
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    (monomial_integrable C D e f hC hD (degree2 i) (degree4 i)).const_mul (coefficient mass2 quartic vacuum L i))
  exact hi.congr (Filter.Eventually.of_forall (fun u => (density_decomposition mass2 quartic vacuum C D e f L u).symm))

theorem density_integral (C D e f : ℂ) (hC : 0 < C.re) (hD : 0 < D.re)
    (L : ℝ) : (∫ u, density mass2 quartic vacuum C D e f L u) = formula mass2 quartic vacuum C D e f L := by
  have hCn : C ≠ 0 := by intro h; simp [h] at hC
  have hDn : D ≠ 0 := by intro h; simp [h] at hD
  simp_rw [density_decomposition]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    (monomial_integrable C D e f hC hD (degree2 i) (degree4 i)).const_mul (coefficient mass2 quartic vacuum L i))]
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

#print axioms density_decomposition
#print axioms density_integrable
#print axioms density_integral
end
end UnifiedTheory.Audit.KFCausalGaussianWeightedSourcePlaneKernel

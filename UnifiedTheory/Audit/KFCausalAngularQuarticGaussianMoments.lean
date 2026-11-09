/- Actual real Gaussian moments and polynomial-circle product integrability.
These supply the neutral Gaussian mixture without assuming any Fubini
or desired response identity. -/
import UnifiedTheory.Audit.KFCausalComplexGaussianMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.Nat.Choose.Sum

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularQuarticGaussianMoments
noncomputable section
open MeasureTheory

def gaussian (u : ℝ) : ℝ := Real.exp (-u^2)
def mass : ℝ := Real.sqrt Real.pi

theorem mass_positive : 0 < mass := by unfold mass; positivity

theorem moment_integrable (j : ℕ) : Integrable (fun u : ℝ => u^j*gaussian u) := by
  simpa only [neg_mul,one_mul,gaussian] using
    KFCausalPolynomialGaussianIntegrals.scalar_moment_integrable 1 (by norm_num) j

private theorem moment_re (j : ℕ) :
    (KFCausalComplexGaussianMoments.value 1 j).re=∫ u : ℝ, u^j*gaussian u := by
  have hr : (∫ u : ℝ, KFCausalComplexGaussianMoments.moment 1 j u).re =
      ∫ u : ℝ, (KFCausalComplexGaussianMoments.moment 1 j u).re :=
    (integral_re (KFCausalComplexGaussianMoments.moment_integrable 1 (by norm_num) j)).symm
  unfold KFCausalComplexGaussianMoments.value
  rw [hr]
  apply integral_congr_ae
  filter_upwards [] with u
  have he : (KFCausalComplexGaussianMoments.moment 1 j u)=((u^j*gaussian u:ℝ):ℂ) := by
    unfold KFCausalComplexGaussianMoments.moment gaussian
    simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_exp,Complex.ofReal_neg,neg_one_mul]
  rw [he,Complex.ofReal_re]

theorem moment_values (j : Fin 5) :
    (∫ u : ℝ, u^j.val*gaussian u)=mass*(![1,0,1/2,0,3/4] : Fin 5→ℝ) j := by
  have h0 : (KFCausalComplexGaussianMoments.value 1 0).re=mass := by
    rw [moment_re]
    simp only [gaussian,pow_zero,one_mul,mass,show (fun u:ℝ=>Real.exp (-u^2))=
      (fun u:ℝ=>Real.exp (-1*u^2)) from by funext u; congr 1; ring,integral_gaussian,div_one]
  have h2 := congrArg Complex.re (KFCausalComplexGaussianMoments.recurrence 1 (by norm_num) 0)
  have h4 := congrArg Complex.re (KFCausalComplexGaussianMoments.recurrence 1 (by norm_num) 2)
  norm_num only [mul_one,Complex.mul_re,Complex.mul_im,Complex.re_ofNat,Complex.im_ofNat,
    zero_mul,sub_zero,Nat.cast_zero,Nat.cast_ofNat,zero_add,one_mul,Complex.one_re,
    Complex.one_im,add_zero] at h2 h4
  rw [h0] at h2
  fin_cases j
  · change (∫ u : ℝ, u^0*gaussian u)=mass*1
    simpa only [mul_one] using h0.symm.trans (moment_re 0) |>.symm
  · rw [← moment_re,KFCausalComplexGaussianMoments.value_one 1 (by norm_num)]
    simp
  · rw [← moment_re]
    norm_num
    linarith
  · rw [← moment_re,KFCausalComplexGaussianMoments.value_three 1 (by norm_num)]
    simp
  · rw [← moment_re]
    norm_num
    linarith

private theorem affine_expansion (n : ℕ) (a c u : ℝ) :
    gaussian u*(a+c*u)^n =
      ∑ j ∈ Finset.range (n+1), (c^j*a^(n-j)*(n.choose j:ℝ))*(u^j*gaussian u) := by
  rw [show a+c*u=c*u+a by ring,add_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow]
  ring

theorem affine_integrable (n : ℕ) (a c : ℝ) :
    Integrable (fun u : ℝ => gaussian u*(a+c*u)^n) := by
  simp_rw [affine_expansion]
  exact integrable_finset_sum _ (fun j _ => (moment_integrable j).const_mul _)

private theorem finite_integral (d : Fin 5→ℝ) :
    (∫ u : ℝ, ∑ j : Fin 5, d j*(u^j.val*gaussian u))=
      mass*∑ j : Fin 5, d j*(![1,0,1/2,0,3/4] : Fin 5→ℝ) j := by
  rw [integral_finset_sum Finset.univ (fun j _ => (moment_integrable j.val).const_mul _)]
  simp_rw [integral_const_mul,moment_values]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quartic_integral (a c : ℝ) :
    (∫ u : ℝ, gaussian u*(a+c*u)^4)=mass*(a^4+3*a^2*c^2+3*c^4/4) := by
  let d : Fin 5→ℝ := ![a^4,4*a^3*c,6*a^2*c^2,4*a*c^3,c^4]
  have he (u : ℝ) : gaussian u*(a+c*u)^4=∑ j : Fin 5,d j*(u^j.val*gaussian u) := by
    norm_num [d,Fin.sum_univ_succ]
    ring
  simp_rw [he]
  rw [finite_integral]
  simp only [d,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    mul_zero,zero_add,add_zero,mul_one]
  ring

theorem cubic_integral (a c : ℝ) :
    (∫ u : ℝ, gaussian u*(a+c*u)^3)=mass*(a^3+3*a*c^2/2) := by
  let d : Fin 5→ℝ := ![a^3,3*a^2*c,3*a*c^2,c^3,0]
  have he (u : ℝ) : gaussian u*(a+c*u)^3=∑ j : Fin 5,d j*(u^j.val*gaussian u) := by
    norm_num [d,Fin.sum_univ_succ]
    ring
  simp_rw [he]
  rw [finite_integral]
  simp only [d,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    mul_zero,zero_add,add_zero,mul_one]
  ring

theorem circle_product_integrable (n : ℕ) (a c : ℝ) (f g : ℝ→ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun p : ℝ×ℝ => gaussian p.1*f p.2*(a+g p.2+c*p.1)^n)
      (volume.prod (volume.restrict (Set.Icc 0 (2*Real.pi)))) := by
  have he (p : ℝ×ℝ) : gaussian p.1*f p.2*(a+g p.2+c*p.1)^n=
      ∑ j ∈ Finset.range (n+1),
        (p.1^j*gaussian p.1)*(f p.2*c^j*(a+g p.2)^(n-j)*(n.choose j:ℝ)) := by
    rw [show a+g p.2+c*p.1=c*p.1+(a+g p.2) by ring,add_pow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow]
    ring
  simp_rw [he]
  apply integrable_finset_sum
  intro j _
  exact (moment_integrable j).mul_prod
    ((by fun_prop : Continuous (fun t : ℝ => f t*c^j*(a+g t)^(n-j)*(n.choose j:ℝ))).integrableOn_Icc)

#print axioms mass_positive
#print axioms moment_integrable
#print axioms moment_values
#print axioms affine_integrable
#print axioms quartic_integral
#print axioms cubic_integral
#print axioms circle_product_integrable
end
end UnifiedTheory.Audit.KFCausalAngularQuarticGaussianMoments

/- Actual neutral Gaussian mass-channel moments with the original
common complex source. The frozen generic moment and polynomial L1
suppliers retain the true neutral normalization and variance. -/
import UnifiedTheory.Audit.KFCausalCommonComplexQuarticNeutralIntegral
import UnifiedTheory.Audit.KFCausalAngularMassGaussianSmoothing

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalCommonComplexMassNeutralIntegral
noncomputable section
open MeasureTheory
open KFCausalCommonRealGaussianEnergy (neutralWeight neutralMoment neutral_moment_integrable)
open KFCausalCommonComplexQuarticNeutralIntegral (polynomial_integrable moment_values normalized)
open KFCausalAngularMassGaussianSmoothing (weight weightSlope)

private def coefficient2 (t : ℝ) : Fin 5→ℝ := ![t^2,2*t,1,0,0]
private def coefficient1 (t : ℝ) : Fin 5→ℝ := ![t,1,0,0,0]

private theorem quadratic_expand (t x : ℝ) : (x+t)^2=∑j:Fin 5,coefficient2 t j*x^j.val := by
  simp [coefficient2,Fin.sum_univ_succ]
  ring
private theorem linear_expand (t x : ℝ) : (x+t)^1=∑j:Fin 5,coefficient1 t j*x^j.val := by
  simp [coefficient1,Fin.sum_univ_succ]
  ring

private theorem finite_moments (beta A : ℝ) (hbeta : 0<beta) (c : Fin 5→ℝ) :
    (∫x:ℝ,(∑j:Fin 5,c j*x^j.val)*neutralWeight beta A x)=
      ∑j:Fin 5,c j*neutralMoment beta A j := by
  simp only [Finset.sum_mul,mul_assoc]
  rw [integral_finset_sum Finset.univ (fun (j : Fin 5) _ =>
    (neutral_moment_integrable beta A hbeta j).const_mul (c j))]
  simp only [integral_const_mul,neutralMoment]

theorem quadratic_integrable (beta A t : ℝ) (hbeta : 0<beta) :
    Integrable (fun x:ℝ=>(x+t)^2*neutralWeight beta A x) := by
  apply (polynomial_integrable beta A hbeta ((Polynomial.X+Polynomial.C t : Polynomial ℝ)^2)).congr
  filter_upwards [] with x
  simp only [Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]

theorem quadratic_integral (beta A t : ℝ) (hbeta : 0<beta) :
    (∫x:ℝ,(x+t)^2*neutralWeight beta A x)=
      neutralMoment beta A 0*weight (1/(4*beta)) (A/(2*beta)+t) := by
  simp_rw [quadratic_expand]
  rw [finite_moments beta A hbeta]
  simp_rw [moment_values beta A hbeta]
  simp only [coefficient2,normalized,Fin.sum_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,zero_mul,weight,KFCausalAngularQuarticGaussianSmoothing.weight]
  ring

theorem linear_integral (beta A t : ℝ) (hbeta : 0<beta) :
    (∫x:ℝ,2*(x+t)^1*neutralWeight beta A x)=
      neutralMoment beta A 0*weightSlope (1/(4*beta)) (A/(2*beta)+t) := by
  simp only [mul_assoc,integral_const_mul]
  simp_rw [linear_expand]
  rw [finite_moments beta A hbeta]
  simp_rw [moment_values beta A hbeta]
  simp only [coefficient1,normalized,Fin.sum_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,zero_mul,weightSlope,KFCausalAngularQuarticGaussianSmoothing.weight]
  ring


#print axioms quadratic_integrable
#print axioms quadratic_integral
#print axioms linear_integral
end
end UnifiedTheory.Audit.KFCausalCommonComplexMassNeutralIntegral

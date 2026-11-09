/- Exact neutral Gaussian moments for the common complex-source quartic
channel. The real source shifts the mean, while the Gaussian mass and
variance are obtained from actual convergent integrals. -/
import UnifiedTheory.Audit.KFCausalChargedQuarticAngularLoss
import UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedEnergy

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonComplexQuarticNeutralIntegral
noncomputable section
open MeasureTheory
open KFCausalCommonRealGaussianEnergy (neutralWeight neutralMoment neutral_moment_integrable)
open KFCausalAngularQuarticGaussianSmoothing (weight weightSlope)

private theorem moment_complex (beta A : ℝ) (j : ℕ) :
    ((neutralMoment beta A j:ℝ):ℂ)=KFCausalShiftedComplexGaussianMoments.value
      ((2*beta:ℝ):ℂ) ((2*A:ℝ):ℂ) j := by
  rw [neutralMoment,← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold neutralWeight KFCausalShiftedComplexGaussianMoments.moment
  push_cast
  congr 2
  ring

theorem polynomial_integrable (beta A : ℝ) (hbeta : 0<beta) (P : Polynomial ℝ) :
    Integrable (fun x : ℝ => P.eval x*neutralWeight beta A x) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add,add_mul] using hP.add hQ
  | monomial n a => simpa only [Polynomial.eval_monomial,mul_assoc] using
      (neutral_moment_integrable beta A hbeta n).const_mul a

theorem mass_positive (beta A : ℝ) (hbeta : 0<beta) : 0<neutralMoment beta A 0 := by
  have hi := neutral_moment_integrable beta A hbeta 0
  have hp : ∀x:ℝ,0<x^0*neutralWeight beta A x := fun x => by
    simp only [pow_zero,one_mul,neutralWeight]
    exact Real.exp_pos _
  exact integral_pos_iff_support_of_nonneg (fun x => (hp x).le) hi |>.mpr (by
    have he : Function.support (fun x : ℝ => x^0*neutralWeight beta A x)=Set.univ := by
      ext x
      simp only [Function.mem_support,Set.mem_univ,iff_true]
      exact ne_of_gt (hp x)
    rw [he]
    simp)

def normalized (beta A : ℝ) : Fin 5→ℝ :=
  ![1,A/(2*beta),(A/(2*beta))^2+1/(4*beta),
    (A/(2*beta))^3+3*(A/(2*beta))*(1/(4*beta)),
    weight (1/(4*beta)) (A/(2*beta))]

theorem moment_values (beta A : ℝ) (hbeta : 0<beta) (j : Fin 5) :
    neutralMoment beta A j=neutralMoment beta A 0*normalized beta A j := by
  have hb : 0<(((2*beta:ℝ):ℂ)).re := by simp only [Complex.ofReal_re]; positivity
  have hm : KFCausalShiftedComplexGaussianMoments.mass ((2*beta:ℝ):ℂ) ((2*A:ℝ):ℂ)=
      ((neutralMoment beta A 0:ℝ):ℂ) := by
    rw [moment_complex,KFCausalShiftedComplexGaussianMoments.value_zero _ _ hb]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul,moment_complex]
  fin_cases j <;> simp only [normalized,weight,
    KFCausalShiftedComplexGaussianMoments.value_zero _ _ hb,
    KFCausalShiftedComplexGaussianMoments.value_one _ _ hb,
    KFCausalShiftedComplexGaussianMoments.value_two _ _ hb,
    KFCausalShiftedComplexGaussianMoments.value_three _ _ hb,
    KFCausalShiftedComplexGaussianMoments.value_four _ _ hb,hm]
  all_goals push_cast
  all_goals field_simp
  all_goals ring

private def coefficient4 (t : ℝ) : Fin 5→ℝ := ![t^4,4*t^3,6*t^2,4*t,1]
private def coefficient3 (t : ℝ) : Fin 5→ℝ := ![t^3,3*t^2,3*t,1,0]

private theorem quartic_expand (t x : ℝ) : (x+t)^4=∑j:Fin 5,coefficient4 t j*x^j.val := by
  simp [coefficient4,Fin.sum_univ_succ]
  ring
private theorem cubic_expand (t x : ℝ) : (x+t)^3=∑j:Fin 5,coefficient3 t j*x^j.val := by
  simp [coefficient3,Fin.sum_univ_succ]
  ring

private theorem finite_moments (beta A : ℝ) (hbeta : 0<beta) (c : Fin 5→ℝ) :
    (∫x:ℝ,(∑j:Fin 5,c j*x^j.val)*neutralWeight beta A x)=
      ∑j:Fin 5,c j*neutralMoment beta A j := by
  simp only [Finset.sum_mul,mul_assoc]
  rw [integral_finset_sum Finset.univ (fun (j : Fin 5) _ =>
    (neutral_moment_integrable beta A hbeta j).const_mul (c j))]
  simp only [integral_const_mul,neutralMoment]

theorem quartic_integrable (beta A t : ℝ) (hbeta : 0<beta) :
    Integrable (fun x:ℝ=>(x+t)^4*neutralWeight beta A x) := by
  apply (polynomial_integrable beta A hbeta ((Polynomial.X+Polynomial.C t : Polynomial ℝ)^4)).congr
  filter_upwards [] with x
  simp only [Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]

theorem quartic_integral (beta A t : ℝ) (hbeta : 0<beta) :
    (∫x:ℝ,(x+t)^4*neutralWeight beta A x)=
      neutralMoment beta A 0*weight (1/(4*beta)) (A/(2*beta)+t) := by
  simp_rw [quartic_expand]
  rw [finite_moments beta A hbeta]
  simp_rw [moment_values beta A hbeta]
  simp only [coefficient4,normalized,Fin.sum_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,weight]
  ring

theorem cubic_integral (beta A t : ℝ) (hbeta : 0<beta) :
    (∫x:ℝ,4*(x+t)^3*neutralWeight beta A x)=
      neutralMoment beta A 0*weightSlope (1/(4*beta)) (A/(2*beta)+t) := by
  simp only [mul_assoc,integral_const_mul]
  simp_rw [cubic_expand]
  rw [finite_moments beta A hbeta]
  simp_rw [moment_values beta A hbeta]
  simp only [coefficient3,normalized,Fin.sum_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,weight,weightSlope]
  ring

#print axioms polynomial_integrable
#print axioms mass_positive
#print axioms moment_values
#print axioms quartic_integrable
#print axioms quartic_integral
#print axioms cubic_integral
end
end UnifiedTheory.Audit.KFCausalCommonComplexQuarticNeutralIntegral

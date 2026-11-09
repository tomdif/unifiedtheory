/- Neutral Gaussian smoothing of the literal circle loss. All product
integrability and Fubini identities are derived, including zero variance.
The same proved circle constant works for every nonnegative variance. -/
import UnifiedTheory.Audit.KFCausalAngularQuarticGaussianMoments
import UnifiedTheory.Audit.KFCausalAngularMassCircleLoss

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularMassGaussianSmoothing
noncomputable section
open MeasureTheory Set
open KFCausalAngularMassCircle
open KFCausalAngularQuarticGaussianMoments

def weight (sigma x : ℝ) : ℝ := x^2+sigma
def weightSlope (_sigma x : ℝ) : ℝ := 2*x

def smoothEnergy (sigma z mu l : ℝ) : ℝ :=
  ∫ theta in 0..(2*Real.pi), Real.exp (-z*Real.cos theta)*weight sigma (mu+l*Real.cos theta)
def smoothFieldSlope (sigma z mu l : ℝ) : ℝ :=
  ∫ theta in 0..(2*Real.pi), Real.exp (-z*Real.cos theta)*Real.cos theta*
    weightSlope sigma (mu+l*Real.cos theta)
def smoothTilt (sigma z mu l : ℝ) : ℝ :=
  ∫ theta in 0..(2*Real.pi), (-z*Real.cos theta)*Real.exp (-z*Real.cos theta)*
    weight sigma (mu+l*Real.cos theta)
def smoothDefect (sigma z mu l : ℝ) : ℝ :=
  2*smoothTilt sigma z mu l-l*smoothFieldSlope sigma z mu l

private theorem finite_integral (d : Fin 5→ℝ) :
    (∫ u : ℝ, ∑ j : Fin 5, d j*(u^j.val*gaussian u))=
      mass*∑ j : Fin 5, d j*(![1,0,1/2,0,3/4] : Fin 5→ℝ) j := by
  rw [integral_finset_sum Finset.univ (fun j _ => (moment_integrable j.val).const_mul _)]
  simp_rw [integral_const_mul,moment_values]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem quadratic_integral (a c : ℝ) :
    (∫ u : ℝ, gaussian u*(a+c*u)^2)=mass*(a^2+c^2/2) := by
  let d : Fin 5→ℝ := ![a^2,2*a*c,c^2,0,0]
  have he (u : ℝ) : gaussian u*(a+c*u)^2=∑ j : Fin 5,d j*(u^j.val*gaussian u) := by
    norm_num [d,Fin.sum_univ_succ]
    ring
  simp_rw [he]
  rw [finite_integral]
  simp only [d,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    mul_zero,zero_mul,zero_add,add_zero,mul_one]
  ring

private theorem linear_integral (a c : ℝ) :
    (∫ u : ℝ, gaussian u*(a+c*u)^1)=mass*a := by
  let d : Fin 5→ℝ := ![a,c,0,0,0]
  have he (u : ℝ) : gaussian u*(a+c*u)^1=∑ j : Fin 5,d j*(u^j.val*gaussian u) := by
    norm_num [d,Fin.sum_univ_succ]
    ring
  simp_rw [he]
  rw [finite_integral]
  simp only [d,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    mul_zero,zero_mul,add_zero,mul_one]

private theorem compact_integral_eq (f : ℝ→ℝ) :
    (∫ theta in Icc 0 (2*Real.pi), f theta)=∫ theta in 0..(2*Real.pi), f theta := by
  rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi)]

private theorem outer_integrable (n : ℕ) (a c : ℝ) (f g : ℝ→ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun u : ℝ => gaussian u*
      ∫ theta in 0..(2*Real.pi), f theta*(a+g theta+c*u)^n) := by
  have hh := (circle_product_integrable n a c f g hf hg).integral_prod_left
  have he (u : ℝ) :
      (∫ theta in Icc 0 (2*Real.pi), gaussian u*f theta*(a+g theta+c*u)^n)=
      gaussian u*∫ theta in 0..(2*Real.pi), f theta*(a+g theta+c*u)^n := by
    simp only [mul_assoc,integral_const_mul,compact_integral_eq]
  simpa only [he] using hh

private theorem mixture_swap (n : ℕ) (a c : ℝ) (f g : ℝ→ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ u : ℝ, gaussian u*∫ theta in 0..(2*Real.pi), f theta*(a+g theta+c*u)^n)=
      ∫ theta in 0..(2*Real.pi), f theta*(∫ u : ℝ, gaussian u*(a+g theta+c*u)^n) := by
  have hh := integral_integral_swap
    (f := fun u theta : ℝ => gaussian u*f theta*(a+g theta+c*u)^n)
    (circle_product_integrable n a c f g hf hg)
  have he1 (u : ℝ) :
      (∫ theta in Icc 0 (2*Real.pi), gaussian u*f theta*(a+g theta+c*u)^n)=
      gaussian u*∫ theta in 0..(2*Real.pi), f theta*(a+g theta+c*u)^n := by
    simp only [mul_assoc,integral_const_mul,compact_integral_eq]
  have he2 (theta : ℝ) :
      (∫ u : ℝ, gaussian u*f theta*(a+g theta+c*u)^n)=
      f theta*(∫ u : ℝ, gaussian u*(a+g theta+c*u)^n) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    ring
  simpa only [he1,he2,compact_integral_eq] using hh

private theorem energy_reorder (z mu l c u : ℝ) :
    energy z (mu+c*u) l=
      ∫ theta in 0..(2*Real.pi), Real.exp (-z*Real.cos theta)*(mu+l*Real.cos theta+c*u)^2 := by
  apply intervalIntegral.integral_congr
  intro theta _
  unfold integrand
  ring

private theorem field_reorder (z mu l c u : ℝ) :
    fieldSlope z (mu+c*u) l=
      ∫ theta in 0..(2*Real.pi), (Real.exp (-z*Real.cos theta)*(2*Real.cos theta))*
        (mu+l*Real.cos theta+c*u)^1 := by
  apply intervalIntegral.integral_congr
  intro theta _
  unfold fieldIntegrand
  ring

private theorem tilt_reorder (z mu l c u : ℝ) :
    tilt z (mu+c*u) l=
      ∫ theta in 0..(2*Real.pi), ((-z*Real.cos theta)*Real.exp (-z*Real.cos theta))*
        (mu+l*Real.cos theta+c*u)^2 := by
  apply intervalIntegral.integral_congr
  intro theta _
  unfold integrand
  ring

theorem mixture_integrable (sigma z mu l : ℝ) :
    Integrable (fun u : ℝ => gaussian u*energy z (mu+Real.sqrt (2*sigma)*u) l) ∧
    Integrable (fun u : ℝ => gaussian u*fieldSlope z (mu+Real.sqrt (2*sigma)*u) l) ∧
    Integrable (fun u : ℝ => gaussian u*tilt z (mu+Real.sqrt (2*sigma)*u) l) := by
  constructor
  · simp_rw [energy_reorder]
    exact outer_integrable 2 mu _ _ _ (by fun_prop) (by fun_prop)
  constructor
  · simp_rw [field_reorder]
    exact outer_integrable 1 mu _ _ _ (by fun_prop) (by fun_prop)
  · simp_rw [tilt_reorder]
    exact outer_integrable 2 mu _ _ _ (by fun_prop) (by fun_prop)

theorem energy_mixture (sigma z mu l : ℝ) (hsigma : 0≤sigma) :
    (∫ u : ℝ, gaussian u*energy z (mu+Real.sqrt (2*sigma)*u) l)=
      mass*smoothEnergy sigma z mu l := by
  simp_rw [energy_reorder]
  rw [mixture_swap 2 mu _ _ _ (by fun_prop) (by fun_prop)]
  simp_rw [quadratic_integral]
  unfold smoothEnergy
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro theta _
  have hs : (Real.sqrt (2*sigma))^2=2*sigma := Real.sq_sqrt (by positivity)
  rw [hs]
  unfold weight
  ring

theorem field_mixture (sigma z mu l : ℝ) (_hsigma : 0≤sigma) :
    (∫ u : ℝ, gaussian u*fieldSlope z (mu+Real.sqrt (2*sigma)*u) l)=
      mass*smoothFieldSlope sigma z mu l := by
  simp_rw [field_reorder]
  rw [mixture_swap 1 mu _ _ _ (by fun_prop) (by fun_prop)]
  simp_rw [linear_integral]
  unfold smoothFieldSlope
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro theta _
  unfold weightSlope
  ring

theorem tilt_mixture (sigma z mu l : ℝ) (hsigma : 0≤sigma) :
    (∫ u : ℝ, gaussian u*tilt z (mu+Real.sqrt (2*sigma)*u) l)=
      mass*smoothTilt sigma z mu l := by
  simp_rw [tilt_reorder]
  rw [mixture_swap 2 mu _ _ _ (by fun_prop) (by fun_prop)]
  simp_rw [quadratic_integral]
  unfold smoothTilt
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro theta _
  have hs : (Real.sqrt (2*sigma))^2=2*sigma := Real.sq_sqrt (by positivity)
  rw [hs]
  unfold weight
  ring

theorem defect_mixture_integrable (sigma z mu l : ℝ) :
    Integrable (fun u : ℝ => gaussian u*defect z (mu+Real.sqrt (2*sigma)*u) l) := by
  have hi := mixture_integrable sigma z mu l
  have he (u : ℝ) : gaussian u*defect z (mu+Real.sqrt (2*sigma)*u) l=
      2*(gaussian u*tilt z (mu+Real.sqrt (2*sigma)*u) l)-
        l*(gaussian u*fieldSlope z (mu+Real.sqrt (2*sigma)*u) l) := by
    rw [defect_eq]
    ring
  simp_rw [he]
  exact (hi.2.2.const_mul 2).sub (hi.2.1.const_mul l)

theorem defect_mixture (sigma z mu l : ℝ) (hsigma : 0≤sigma) :
    (∫ u : ℝ, gaussian u*defect z (mu+Real.sqrt (2*sigma)*u) l)=
      mass*smoothDefect sigma z mu l := by
  have hi := mixture_integrable sigma z mu l
  have he (u : ℝ) : gaussian u*defect z (mu+Real.sqrt (2*sigma)*u) l=
      2*(gaussian u*tilt z (mu+Real.sqrt (2*sigma)*u) l)-
        l*(gaussian u*fieldSlope z (mu+Real.sqrt (2*sigma)*u) l) := by
    rw [defect_eq]
    ring
  simp_rw [he]
  rw [integral_sub (hi.2.2.const_mul 2) (hi.2.1.const_mul l)]
  simp only [integral_const_mul,tilt_mixture sigma z mu l hsigma,field_mixture sigma z mu l hsigma]
  unfold smoothDefect
  ring

theorem global_smoothed_loss : ∃ C : ℝ, 0≤C ∧ ∀ sigma z mu l : ℝ, 0≤sigma →
    0≤smoothDefect sigma z mu l+C*smoothEnergy sigma z mu l := by
  obtain ⟨C,hC,hbound⟩ := KFCausalAngularMassCircleLoss.global_loss
  refine ⟨C,hC,?_⟩
  intro sigma z mu l hsigma
  have hi := mixture_integrable sigma z mu l
  have hd := defect_mixture_integrable sigma z mu l
  have hn : 0≤∫ u : ℝ, gaussian u*(defect z (mu+Real.sqrt (2*sigma)*u) l+
      C*energy z (mu+Real.sqrt (2*sigma)*u) l) :=
    integral_nonneg (fun u => mul_nonneg (Real.exp_pos _).le (hbound _ _ _))
  have he (u : ℝ) : gaussian u*(defect z (mu+Real.sqrt (2*sigma)*u) l+
      C*energy z (mu+Real.sqrt (2*sigma)*u) l)=
      gaussian u*defect z (mu+Real.sqrt (2*sigma)*u) l+
      C*(gaussian u*energy z (mu+Real.sqrt (2*sigma)*u) l) := by ring
  simp_rw [he] at hn
  rw [integral_add hd (hi.1.const_mul C),integral_const_mul,
    defect_mixture sigma z mu l hsigma,energy_mixture sigma z mu l hsigma] at hn
  nlinarith [mass_positive]

#print axioms mixture_integrable
#print axioms energy_mixture
#print axioms field_mixture
#print axioms tilt_mixture
#print axioms defect_mixture_integrable
#print axioms defect_mixture
#print axioms global_smoothed_loss
end
end UnifiedTheory.Audit.KFCausalAngularMassGaussianSmoothing

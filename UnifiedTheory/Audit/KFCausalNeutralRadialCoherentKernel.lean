/- An exact coherent neutral slice of the positive joint representation.
The quartic Gaussian marginal is evaluated before its radial behavior is
studied. No claim about the full clock response follows from this slice. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralHolomorphic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalNeutralRadialCoherentKernel
noncomputable section
open MeasureTheory
open KFCausalQuarticPlaneDomination (potential)
open KFCausalComplexGaussianMoments (moment value gaussianValue)
open KFCausalReciprocalNeutralHolomorphic (weightedProfile)
open KFCausalNeutralExponentialProfiles (exponentialProfile)

def mass : ℝ := ∫ x : ℝ, Real.exp (-2*x^2)
def quartic (m : ℝ) : ℝ := m^4/4+7*m^2/8+75/64
def source : ℂ := 4+(200/3:ℂ)*Complex.I
def profile : ℂ → ℂ := weightedProfile 1 (exponentialProfile source 1 1)
def slice (v x : ℝ) : ℝ := potential (x+v)*‖profile ((x:ℂ)+(v/100:ℝ)*Complex.I)‖^2
def marginal (v : ℝ) : ℝ := Real.exp (v^2/5000-4*v/3)*quartic (2+v)

theorem real_moment (n : ℕ) :
    ((∫ x : ℝ, x^n*Real.exp (-2*x^2):ℝ):ℂ) = value 2 n := by
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [moment,Complex.ofReal_exp]

theorem mass_positive : 0 < mass := by
  unfold mass
  rw [integral_gaussian]
  positivity

theorem quartic_integrable (m : ℝ) :
    Integrable (fun x : ℝ => potential (x+m)*Real.exp (-2*x^2)) := by
  have hi (n : ℕ) := KFCausalPolynomialGaussianIntegrals.scalar_moment_integrable 2 (by norm_num) n
  have he (x : ℝ) : potential (x+m)*Real.exp (-2*x^2) =
      (1+m^2/2+m^4/4)*(x^0*Real.exp (-2*x^2))+
      (m+m^3)*(x^1*Real.exp (-2*x^2))+
      (1/2+3*m^2/2)*(x^2*Real.exp (-2*x^2))+
      m*(x^3*Real.exp (-2*x^2))+(1/4)*(x^4*Real.exp (-2*x^2)) := by
    unfold potential
    ring
  simp_rw [he]
  exact ((((hi 0).const_mul _).add ((hi 1).const_mul _)).add ((hi 2).const_mul _)).add
    ((hi 3).const_mul _) |>.add ((hi 4).const_mul _)

theorem quartic_integral (m : ℝ) :
    (∫ x : ℝ, potential (x+m)*Real.exp (-2*x^2)) = mass*quartic m := by
  have hi (n : ℕ) := KFCausalPolynomialGaussianIntegrals.scalar_moment_integrable 2 (by norm_num) n
  have h0 : ((mass:ℝ):ℂ) = gaussianValue 2 := by
    simpa only [mass,pow_zero,one_mul] using
      (real_moment 0).trans (KFCausalComplexGaussianMoments.value_zero 2 (by norm_num))
  have h1 : (∫ x : ℝ, x^1*Real.exp (-2*x^2)) = 0 := by
    apply Complex.ofReal_injective
    rw [real_moment,KFCausalComplexGaussianMoments.value_one 2 (by norm_num)]
    rfl
  have h2 : (∫ x : ℝ, x^2*Real.exp (-2*x^2)) = mass/4 := by
    apply Complex.ofReal_injective
    rw [real_moment,KFCausalComplexGaussianMoments.value_two 2 (by norm_num),← h0]
    push_cast
    ring
  have h3 : (∫ x : ℝ, x^3*Real.exp (-2*x^2)) = 0 := by
    apply Complex.ofReal_injective
    rw [real_moment,KFCausalComplexGaussianMoments.value_three 2 (by norm_num)]
    rfl
  have h4 : (∫ x : ℝ, x^4*Real.exp (-2*x^2)) = 3*mass/16 := by
    apply Complex.ofReal_injective
    rw [real_moment,KFCausalComplexGaussianMoments.value_four 2 (by norm_num),← h0]
    push_cast
    ring
  have he (x : ℝ) : potential (x+m)*Real.exp (-2*x^2) =
      (1+m^2/2+m^4/4)*(x^0*Real.exp (-2*x^2))+
      (m+m^3)*(x^1*Real.exp (-2*x^2))+
      (1/2+3*m^2/2)*(x^2*Real.exp (-2*x^2))+
      m*(x^3*Real.exp (-2*x^2))+(1/4)*(x^4*Real.exp (-2*x^2)) := by
    unfold potential
    ring
  simp_rw [he]
  have i0 := (hi 0).const_mul (1+m^2/2+m^4/4)
  have i1 := (hi 1).const_mul (m+m^3)
  have i2 := (hi 2).const_mul (1/2+3*m^2/2)
  have i3 := (hi 3).const_mul m
  have i4 := (hi 4).const_mul (1/4:ℝ)
  have hs0 := integral_add i0 i1
  have hs1 := integral_add (i0.add i1) i2
  have hs2 := integral_add ((i0.add i1).add i2) i3
  have hs3 := integral_add (((i0.add i1).add i2).add i3) i4
  simp only [Pi.add_apply] at hs0 hs1 hs2 hs3
  rw [hs3,hs2,hs1,hs0]
  simp only [integral_const_mul,h1,h2,h3,h4,pow_zero,one_mul]
  unfold mass quartic
  ring

theorem profile_norm (v x : ℝ) :
    ‖profile ((x:ℂ)+(v/100:ℝ)*Complex.I)‖^2 =
      Real.exp 8*Real.exp (v^2/5000-4*v/3)*Real.exp (-2*(x-2)^2) := by
  simp only [profile,weightedProfile,exponentialProfile,Polynomial.eval_one,
    mul_one,one_mul,← Complex.exp_add,Complex.norm_exp,← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  simp [source,Complex.mul_re,Complex.mul_im,pow_two]
  ring

theorem slice_shift (v x : ℝ) :
    slice v (x+2) = (Real.exp 8*Real.exp (v^2/5000-4*v/3))*
      (potential (x+(2+v))*Real.exp (-2*x^2)) := by
  rw [slice,profile_norm]
  rw [show x+2-2=x by ring,show x+2+v=x+(2+v) by ring]
  ring

theorem slice_integrable (v : ℝ) : Integrable (slice v) := by
  have hi := (quartic_integrable (2+v)).const_mul
    (Real.exp 8*Real.exp (v^2/5000-4*v/3))
  have he : Integrable (fun x : ℝ => slice v (x+2)) := by
    simpa only [slice_shift] using hi
  simpa only [add_assoc,neg_add_cancel,add_zero] using he.comp_add_right (-2)

theorem slice_integral (v : ℝ) :
    (∫ x, slice v x) = Real.exp 8*mass*marginal v := by
  rw [← integral_add_right_eq_self (slice v) 2]
  simp_rw [slice_shift]
  rw [integral_const_mul,quartic_integral]
  unfold marginal
  ring

#print axioms real_moment
#print axioms mass_positive
#print axioms quartic_integrable
#print axioms quartic_integral
#print axioms profile_norm
#print axioms slice_shift
#print axioms slice_integrable
#print axioms slice_integral
end
end UnifiedTheory.Audit.KFCausalNeutralRadialCoherentKernel

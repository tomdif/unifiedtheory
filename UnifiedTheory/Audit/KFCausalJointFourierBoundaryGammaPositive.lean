/- A positive square certificate for the Gamma(shape 3/2) normal-boundary
form, including the actual clock coefficient. No global trace, localization,
or full response bound is asserted here. -/
import UnifiedTheory.Audit.KFCausalJointFourierBoundaryGammaForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointFourierBoundaryGammaPositive
noncomputable section
open MeasureTheory Set
open KFCausalJointFourierBoundaryGammaForm

def loweringPair (z0 z1 z2 : ℂ) : ℂ :=
  star z0*(z1-2*z2)+3*star z1*z2

def scaledForm (M ρ : ℝ) (z0 z1 z2 : ℂ) : ℝ :=
  (M^2+1/4)*gammaNorm z0 z1 z2-
    ρ*((((M:ℂ)+Complex.I/2)*loweringPair z0 z1 z2).re)

def centralSquare (M ρ : ℝ) (z0 z1 z2 : ℂ) : ℝ :=
  gammaNorm ((M:ℂ)*z0-(ρ:ℂ)*(z1/4-z2/2))
    ((M:ℂ)*z1-(ρ:ℂ)*(z0/6+z2/2))
    ((M:ℂ)*z2-(ρ:ℂ)*(-z0/15+z1/10))

def endpointRemainder (ρ : ℝ) (z0 z1 z2 : ℂ) : ℝ :=
  9/40*Complex.normSq (z0+((2/27:ℂ)-10*(ρ:ℂ)*Complex.I/9)*z1+
    ((-5/27:ℂ)+20*(ρ:ℂ)*Complex.I/9)*z2)+
  305/1296*Complex.normSq (z1+((298/305:ℂ)-192*(ρ:ℂ)*Complex.I/61)*z2)+
  2099/7320*Complex.normSq z2

def scaledDensity (M ρ : ℝ) (z0 z1 z2 : ℂ) (x : ℝ) : ℝ :=
  (M^2+1/4)*Complex.normSq (normalPolynomial z0 z1 z2 x)-
    ρ*((((M:ℂ)+Complex.I/2)*star (normalPolynomial z0 z1 z2 x)*
      deriv (normalPolynomial z0 z1 z2) x).re)

def normalDensity (M ρ : ℝ) (z0 z1 z2 : ℂ) (x : ℝ) : ℝ :=
  Complex.normSq (normalPolynomial z0 z1 z2 x)-
    ρ*((((M:ℂ)-Complex.I/2)⁻¹*star (normalPolynomial z0 z1 z2 x)*
      deriv (normalPolynomial z0 z1 z2) x).re)

theorem endpoint_square_identity (M ρ : ℝ) (hρ : ρ^2 = 1/3) (z0 z1 z2 : ℂ) :
    scaledForm M ρ z0 z1 z2 = centralSquare M ρ z0 z1 z2+endpointRemainder ρ z0 z1 z2 := by
  simp only [scaledForm,centralSquare,endpointRemainder,gammaNorm,loweringPair,
    Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im]
  norm_num
  ring_nf
  rw [hρ]
  ring

theorem endpoint_nonnegative (M ρ : ℝ) (hρ : ρ^2 = 1/3) (z0 z1 z2 : ℂ) :
    0 ≤ scaledForm M ρ z0 z1 z2 := by
  rw [endpoint_square_identity M ρ hρ]
  apply add_nonneg
  · exact gammaNorm_nonneg _ _ _
  · unfold endpointRemainder
    exact add_nonneg (add_nonneg
      (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
      (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)))
      (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))

theorem scaledForm_nonnegative (M ρ : ℝ) (hρ : |ρ| ≤ 1/Real.sqrt 3)
    (z0 z1 z2 : ℂ) : 0 ≤ scaledForm M ρ z0 z1 z2 := by
  have hs : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hp : (1/Real.sqrt (3:ℝ))^2 = 1/3 := by rw [div_pow,hs2]; norm_num
  have hm : (-1/Real.sqrt (3:ℝ))^2 = 1/3 := by rw [div_pow,hs2]; norm_num
  have hplus := endpoint_nonnegative M _ hp z0 z1 z2
  have hminus := endpoint_nonnegative M _ hm z0 z1 z2
  have hlo := (abs_le.mp hρ).1
  have hhi := (abs_le.mp hρ).2
  have h1 : 0 ≤ (1+ρ*Real.sqrt 3)/2 := by
    have hh := mul_le_mul_of_nonneg_right hlo hs.le
    field_simp at hh
    nlinarith
  have h2 : 0 ≤ (1-ρ*Real.sqrt 3)/2 := by
    have hh := mul_le_mul_of_nonneg_right hhi hs.le
    field_simp at hh
    nlinarith
  have he : scaledForm M ρ z0 z1 z2 =
      ((1+ρ*Real.sqrt 3)/2)*scaledForm M (1/Real.sqrt 3) z0 z1 z2+
      ((1-ρ*Real.sqrt 3)/2)*scaledForm M (-1/Real.sqrt 3) z0 z1 z2 := by
    unfold scaledForm
    field_simp
    ring
  rw [he]
  exact add_nonneg (mul_nonneg h1 hplus) (mul_nonneg h2 hminus)

theorem lowering_pair_coefficients (z0 z1 z2 : ℂ) :
    gammaPair z0 z1 z2 (z1-2*z2) (2*z2) 0 = loweringPair z0 z1 z2 := by
  unfold gammaPair loweringPair
  ring

private theorem scaled_density_jet (M ρ : ℝ) (z0 z1 z2 : ℂ) (x : ℝ) :
    weight x*scaledDensity M ρ z0 z1 z2 x =
      (M^2+1/4)*(weight x*Complex.normSq (normalPolynomial z0 z1 z2 x))-
      ρ*(weight x*(star (normalPolynomial z0 z1 z2 x)*
        normalPolynomial ((((M:ℂ)+Complex.I/2)*(z1-2*z2)))
          ((((M:ℂ)+Complex.I/2)*(2*z2))) 0 x).re) := by
  have he : ((M:ℂ)+Complex.I/2)*star (normalPolynomial z0 z1 z2 x)*
      deriv (normalPolynomial z0 z1 z2) x =
      star (normalPolynomial z0 z1 z2 x)*
        normalPolynomial ((((M:ℂ)+Complex.I/2)*(z1-2*z2)))
          ((((M:ℂ)+Complex.I/2)*(2*z2))) 0 x := by
    rw [(normalPolynomial_derivative z0 z1 z2 x).deriv]
    unfold normalPolynomial
    ring
  unfold scaledDensity
  rw [he]
  ring

theorem scaled_density_integrable (M ρ : ℝ) (z0 z1 z2 : ℂ) :
    IntegrableOn (fun x => weight x*scaledDensity M ρ z0 z1 z2 x) (Ioi 0) := by
  simp_rw [scaled_density_jet]
  exact ((normal_norm_integrable z0 z1 z2).const_mul _).sub
    ((normal_pair_integrable z0 z1 z2 _ _ _).const_mul _)

theorem scaled_density_integral (M ρ : ℝ) (z0 z1 z2 : ℂ) :
    ∫ x in Ioi (0:ℝ), weight x*scaledDensity M ρ z0 z1 z2 x =
      scaledForm M ρ z0 z1 z2*Real.Gamma (3/2) := by
  simp_rw [scaled_density_jet]
  rw [integral_sub ((normal_norm_integrable z0 z1 z2).const_mul _)
      ((normal_pair_integrable z0 z1 z2 _ _ _).const_mul _),
    integral_const_mul,integral_const_mul,normal_norm_integral,normal_pair_integral]
  have hp : gammaPair z0 z1 z2
      ((((M:ℂ)+Complex.I/2)*(z1-2*z2))) ((((M:ℂ)+Complex.I/2)*(2*z2))) 0 =
      ((M:ℂ)+Complex.I/2)*loweringPair z0 z1 z2 := by
    unfold gammaPair loweringPair
    ring
  rw [hp]
  unfold scaledForm
  ring

theorem normal_density_scaling (M ρ : ℝ) (z0 z1 z2 : ℂ) (x : ℝ) :
    scaledDensity M ρ z0 z1 z2 x = (M^2+1/4)*normalDensity M ρ z0 z1 z2 x := by
  have hd : M^2+1/4 ≠ 0 := ne_of_gt (by positivity : 0 < M^2+1/4)
  have hc : ((M^2+1/4:ℝ):ℂ)*((M:ℂ)-Complex.I/2)⁻¹ = (M:ℂ)+Complex.I/2 := by
    apply Complex.ext <;>
      simp only [Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,
        Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        Complex.div_re,Complex.div_im,Complex.normSq_apply]
    all_goals norm_num
    all_goals field_simp [hd]
  have he : ((M^2+1/4:ℝ):ℂ)*
      (((M:ℂ)-Complex.I/2)⁻¹*star (normalPolynomial z0 z1 z2 x)*
        deriv (normalPolynomial z0 z1 z2) x) =
      ((M:ℂ)+Complex.I/2)*star (normalPolynomial z0 z1 z2 x)*
        deriv (normalPolynomial z0 z1 z2) x := by
    rw [← hc]
    ring
  have hr := congrArg Complex.re he
  rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hr
  unfold scaledDensity normalDensity
  rw [← hr]
  ring

private theorem normal_density_eq_div (M ρ : ℝ) (z0 z1 z2 : ℂ) (x : ℝ) :
    weight x*normalDensity M ρ z0 z1 z2 x =
      (weight x*scaledDensity M ρ z0 z1 z2 x)/(M^2+1/4) := by
  rw [normal_density_scaling]
  field_simp

theorem normal_density_integrable (M ρ : ℝ) (z0 z1 z2 : ℂ) :
    IntegrableOn (fun x => weight x*normalDensity M ρ z0 z1 z2 x) (Ioi 0) := by
  simp_rw [normal_density_eq_div]
  exact (scaled_density_integrable M ρ z0 z1 z2).div_const _

theorem normal_boundary_nonnegative (M ρ : ℝ) (hρ : |ρ| ≤ 1/Real.sqrt 3)
    (z0 z1 z2 : ℂ) :
    0 ≤ ∫ x in Ioi (0:ℝ), weight x*normalDensity M ρ z0 z1 z2 x := by
  simp_rw [normal_density_eq_div]
  rw [integral_div,scaled_density_integral]
  exact div_nonneg (mul_nonneg (scaledForm_nonnegative M ρ hρ z0 z1 z2)
    (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 3/2)).le) (by positivity)

theorem actual_clock_boundary_nonnegative (ε y s M : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (z0 z1 z2 : ℂ) :
    0 ≤ ∫ x in Ioi (0:ℝ), weight x*normalDensity M
      ((KFCausalNeutralPlaneNormalizedGeometry.realNumerator
        (KFCausalNeutralPlaneNormalizedGeometry.fraction ε s)
        (KFCausalClockFloorRelativeShift.scale ε y s)-
          2*(KFCausalClockFloorRelativeShift.scale ε y s).im^2)/
        (2*(KFCausalClockFloorRelativeShift.scale ε y s).re*
          (KFCausalClockFloorRelativeShift.scale ε y s).im)) z0 z1 z2 x := by
  exact normal_boundary_nonnegative M _
    (KFCausalJointFourierBoundaryClockRatio.actual_boundary_ratio_bound ε y s hε hy) z0 z1 z2

#print axioms endpoint_square_identity
#print axioms endpoint_nonnegative
#print axioms scaledForm_nonnegative
#print axioms lowering_pair_coefficients
#print axioms scaled_density_integrable
#print axioms scaled_density_integral
#print axioms normal_density_scaling
#print axioms normal_density_integrable
#print axioms normal_boundary_nonnegative
#print axioms actual_clock_boundary_nonnegative
end
end UnifiedTheory.Audit.KFCausalJointFourierBoundaryGammaPositive

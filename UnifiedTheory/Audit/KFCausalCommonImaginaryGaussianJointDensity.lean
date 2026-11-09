/- The original common-purely-imaginary-source weighted density retains
the exact neutral tilt, all coherent charged widths and the actual Joint
measure. Absolute integrability is derived before neutral integration. -/
import UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedJointEnergy
import UnifiedTheory.Audit.KFCausalOriginalCommonRealGaussianEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianJointDensity
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalReciprocalNeutralPositiveForm (profileSum positiveDensity)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalReciprocalNeutralKernel (neutral)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalChargedEvenMomentFamily (packet)
open KFCausalChargedEvenMomentImaginaryBound (gamma)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalCommonRealGaussianEnergy (neutralWeight)
open KFCausalCommonRealGaussianWeightedEnergy (potential energy)

open KFCausalCommonRealGaussianWeightedJointEnergy (potential_upper)

variable (mass2 quartic vacuum : ℝ)

def density (n : ℕ) (α β D : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (z : Joint) : ℝ :=
  potential mass2 quartic vacuum (z.1.2 1+fieldSlope r*z.1.2 0)*
    Real.exp (-2*β*(z.1.2 1)^2+8*β*r.im^2*(z.1.2 0)^2)*
    ‖profileSum n w c (fun _ => exponentialProfile ((D:ℂ)*Complex.I) 1 1)
      (chart α r (z.1.1^2+(z.1.2 0)^2) z.2)
      (neutral r (z.1.2 0) (z.1.2 1))‖^2

theorem density_nonnegative (n : ℕ) (α β D : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (c : Fin n → ℂ) (z : Joint)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    0 ≤ density mass2 quartic vacuum n α β D w r c z := by
  unfold density
  exact mul_nonneg (mul_nonneg
    (KFCausalCommonRealGaussianWeightedEnergy.potential_nonnegative mass2 quartic vacuum _ hm hq hv)
    (Real.exp_pos _).le) (sq_nonneg _)

theorem profile_factor (n : ℕ) (α D : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (u v x Y : ℝ) :
    profileSum n w c (fun _ => exponentialProfile ((D:ℂ)*Complex.I) 1 1)
      (chart α r (u^2+v^2) Y) (neutral r v x) =
      Complex.exp (((D:ℂ)*Complex.I)*neutral r v x)*
        packet 0 (gamma α r) w (fun i => c i*(w i:ℂ)) ((u,v),Y) := by
  rw [KFCausalChargedEvenMomentFamily.packet_expansion]
  simp only [profileSum,KFCausalReciprocalWedgeLaplace.laplaceSum,exponentialProfile,
    Polynomial.eval_one,pow_zero,one_mul,mul_one,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : chart α r (u^2+v^2) Y =
      gamma α r*((u:ℂ)^2+(v:ℂ)^2)+conj (gamma α r)*(Y:ℂ) := by
    simp [chart,KFCausalReciprocalWedgeGeometry.gamma,gamma]
  rw [he]
  ring

theorem density_factor (n : ℕ) (α β D : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (c : Fin n → ℂ) (z : Joint) :
    density mass2 quartic vacuum n α β D w r c z =
      potential mass2 quartic vacuum (z.1.2 1+fieldSlope r*z.1.2 0)*
        neutralWeight β 0 (z.1.2 1)*
        Real.exp ((8*β*r.im^2)*(z.1.2 0)^2-(4*D*r.im)*(z.1.2 0))*
        ‖packet 0 (gamma α r) w (fun i => c i*(w i:ℂ)) ((z.1.1,z.1.2 0),z.2)‖^2 := by
  unfold density
  rw [profile_factor,norm_mul,mul_pow,Complex.norm_exp,← Real.exp_nat_mul]
  have he : 2*(((D:ℂ)*Complex.I)*neutral r (z.1.2 0) (z.1.2 1)).re=
      -(4*D*r.im)*(z.1.2 0) := by
    simp [neutral,Complex.mul_re,Complex.mul_im]
    ring
  norm_num only [Nat.cast_ofNat] at *
  rw [he]
  unfold neutralWeight
  simp only [mul_zero,zero_mul,add_zero]
  rw [show -2*β*(z.1.2 1)^2+8*β*r.im^2*(z.1.2 0)^2 =
      (-2*β*(z.1.2 1)^2)+((8*β*r.im^2)*(z.1.2 0)^2) by ring,
    Real.exp_add,Real.exp_sub]
  rw [show -(4*D*r.im)*(z.1.2 0) = -((4*D*r.im)*(z.1.2 0)) by ring,Real.exp_neg]
  ring

private theorem density_continuous (n : ℕ) (α β D : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (c : Fin n → ℂ) : Continuous (density mass2 quartic vacuum n α β D w r c) := by
  have he : density mass2 quartic vacuum n α β D w r c = fun z : Joint =>
      potential mass2 quartic vacuum (z.1.2 1+fieldSlope r*z.1.2 0)*
        neutralWeight β 0 (z.1.2 1)*Real.exp ((8*β*r.im^2)*(z.1.2 0)^2-(4*D*r.im)*(z.1.2 0))*
        ‖packet 0 (gamma α r) w (fun i => c i*(w i:ℂ)) ((z.1.1,z.1.2 0),z.2)‖^2 :=
    funext (density_factor mass2 quartic vacuum n α β D w r c)
  rw [he]
  unfold potential neutralWeight packet KFCausalChargedFourierPolynomialGram.atom
  fun_prop

theorem density_integrable (n : ℕ) (α β D : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (c : Fin n → ℂ) (hβ : 0 < β)
    (hd : ∀ i, 8*β*r.im^2 < 2*(gamma α r).re*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    Integrable (density mass2 quartic vacuum n α β D w r c) jointMeasure := by
  have hre : 2*(gamma α r).re=α*KFCausalReciprocalGaussianCoordinates.area r := by
    simp [gamma,KFCausalReciprocalGaussianCoordinates.area,pow_two,Complex.mul_re,Complex.mul_im]
    ring
  have hf := KFCausalGaussianSourceJointKernel.family_integrable n α β w r
    (fun _ => ((D:ℂ)*Complex.I)) c hβ (fun i => by have hdi := hd i; rw [hre] at hdi; nlinarith)
  apply (hf.const_mul (mass2+quartic+vacuum)).mono'
    (density_continuous mass2 quartic vacuum n α β D w r c).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (density_nonnegative mass2 quartic vacuum n α β D w r c z hm hq hv)]
  have he := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (potential_upper mass2 quartic vacuum (z.1.2 1+fieldSlope r*z.1.2 0) hm hq hv) (Real.exp_pos
      (-2*β*(z.1.2 1)^2+8*β*r.im^2*(z.1.2 0)^2)).le)
    (sq_nonneg (‖profileSum n w c (fun _ => exponentialProfile ((D:ℂ)*Complex.I) 1 1)
      (chart α r (z.1.1^2+(z.1.2 0)^2) z.2)
      (neutral r (z.1.2 0) (z.1.2 1))‖))
  simpa only [density,positiveDensity,KFCausalReciprocalNeutralLaplace.weight,mul_assoc] using he

theorem joint_iterated (n : ℕ) (α β D : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (c : Fin n → ℂ) (hβ : 0 < β)
    (hd : ∀ i, 8*β*r.im^2 < 2*(gamma α r).re*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (∫ z, density mass2 quartic vacuum n α β D w r c z ∂jointMeasure)=
      ∫ Y in Set.Ioi (0:ℝ), ∫ u : ℝ, ∫ v : ℝ,
        KFCausalCommonRealGaussianWeightedEnergy.neutralLine mass2 quartic vacuum β 0 (fieldSlope r) v*
        Real.exp ((8*β*r.im^2)*v^2-(4*D*r.im)*v)*
        ‖packet 0 (gamma α r) w (fun i => c i*(w i:ℂ)) ((u,v),Y)‖^2 := by
  rw [KFCausalJointNeutralFourierIntegral.joint_integral_iterated _
    (density_integrable mass2 quartic vacuum n α β D w r c hβ hd hm hq hv)]
  simp only [density_factor,Matrix.cons_val_zero,Matrix.cons_val_one,integral_mul_const,
    KFCausalCommonRealGaussianWeightedEnergy.neutralLine]

#print axioms density_nonnegative
#print axioms profile_factor
#print axioms density_factor
#print axioms density_integrable
#print axioms joint_iterated
end
end UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianJointDensity

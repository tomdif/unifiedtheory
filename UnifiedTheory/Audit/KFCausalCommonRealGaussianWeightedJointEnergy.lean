/- The weighted common-real-source energy is attached to the literal
original Joint measure and profile sum. Integrability follows from actual
unit-potential domination before Fubini. This does not yet identify the
weighted original Hilbert or clock response. -/
import UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedEnergy
import UnifiedTheory.Audit.KFCausalOriginalCommonRealGaussianEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedJointEnergy
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

variable (mass2 quartic vacuum : ℝ)

def density (n : ℕ) (α β B : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (z : Joint) : ℝ :=
  potential mass2 quartic vacuum (z.1.2 1+fieldSlope r*z.1.2 0)*
    Real.exp (-2*β*(z.1.2 1)^2+8*β*r.im^2*(z.1.2 0)^2)*
    ‖profileSum n w c (fun _ => exponentialProfile (B:ℂ) 1 1)
      (chart α r (z.1.1^2+(z.1.2 0)^2) z.2)
      (neutral r (z.1.2 0) (z.1.2 1))‖^2

theorem potential_upper (x : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    potential mass2 quartic vacuum x ≤
      (mass2+quartic+vacuum)*KFCausalQuarticPlaneDomination.potential x := by
  unfold potential KFCausalQuarticPlaneDomination.potential
  nlinarith [mul_nonneg hm (pow_nonneg (sq_nonneg x) 2),
    mul_nonneg hv (pow_nonneg (sq_nonneg x) 2),
    mul_nonneg hq (sq_nonneg x),mul_nonneg hv (sq_nonneg x)]

theorem density_nonnegative (n : ℕ) (α β B : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (c : Fin n → ℂ) (z : Joint)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    0 ≤ density mass2 quartic vacuum n α β B w r c z := by
  unfold density
  exact mul_nonneg (mul_nonneg
    (KFCausalCommonRealGaussianWeightedEnergy.potential_nonnegative mass2 quartic vacuum _ hm hq hv)
    (Real.exp_pos _).le) (sq_nonneg _)

theorem density_factor (n : ℕ) (α β B : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (c : Fin n → ℂ) (z : Joint) :
    density mass2 quartic vacuum n α β B w r c z =
      potential mass2 quartic vacuum (z.1.2 1+fieldSlope r*z.1.2 0)*
        neutralWeight β B (z.1.2 1)*Real.exp ((8*β*r.im^2)*(z.1.2 0)^2)*
        ‖packet 0 (gamma α r) w (fun i => c i*(w i:ℂ)) ((z.1.1,z.1.2 0),z.2)‖^2 := by
  unfold density
  rw [KFCausalOriginalCommonRealGaussianEnergy.profile_factor,norm_mul,mul_pow,
    Complex.norm_exp,← Real.exp_nat_mul]
  have he : 2*((B:ℂ)*neutral r (z.1.2 0) (z.1.2 1)).re=2*B*(z.1.2 1) := by
    simp [neutral,Complex.mul_re]
    ring
  norm_num only [Nat.cast_ofNat] at *
  rw [he]
  unfold neutralWeight
  rw [show -2*β*(z.1.2 1)^2+8*β*r.im^2*(z.1.2 0)^2 =
      (-2*β*(z.1.2 1)^2)+((8*β*r.im^2)*(z.1.2 0)^2) by ring,
    Real.exp_add,Real.exp_add]
  ring

private theorem density_continuous (n : ℕ) (α β B : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (c : Fin n → ℂ) : Continuous (density mass2 quartic vacuum n α β B w r c) := by
  have he : density mass2 quartic vacuum n α β B w r c = fun z : Joint =>
      potential mass2 quartic vacuum (z.1.2 1+fieldSlope r*z.1.2 0)*
        neutralWeight β B (z.1.2 1)*Real.exp ((8*β*r.im^2)*(z.1.2 0)^2)*
        ‖packet 0 (gamma α r) w (fun i => c i*(w i:ℂ)) ((z.1.1,z.1.2 0),z.2)‖^2 :=
    funext (density_factor mass2 quartic vacuum n α β B w r c)
  rw [he]
  unfold potential neutralWeight packet KFCausalChargedFourierPolynomialGram.atom
  fun_prop

theorem density_integrable (n : ℕ) (α β B : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (c : Fin n → ℂ) (hβ : 0 < β)
    (hd : ∀ i, 8*β*r.im^2 < 2*(gamma α r).re*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    Integrable (density mass2 quartic vacuum n α β B w r c) jointMeasure := by
  have hre : 2*(gamma α r).re=α*KFCausalReciprocalGaussianCoordinates.area r := by
    simp [gamma,KFCausalReciprocalGaussianCoordinates.area,pow_two,Complex.mul_re,Complex.mul_im]
    ring
  have hf := KFCausalGaussianSourceJointKernel.family_integrable n α β w r
    (fun _ => (B:ℂ)) c hβ (fun i => by have hdi := hd i; rw [hre] at hdi; nlinarith)
  apply (hf.const_mul (mass2+quartic+vacuum)).mono'
    (density_continuous mass2 quartic vacuum n α β B w r c).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (density_nonnegative mass2 quartic vacuum n α β B w r c z hm hq hv)]
  have he := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (potential_upper mass2 quartic vacuum (z.1.2 1+fieldSlope r*z.1.2 0) hm hq hv) (Real.exp_pos
      (-2*β*(z.1.2 1)^2+8*β*r.im^2*(z.1.2 0)^2)).le)
    (sq_nonneg (‖profileSum n w c (fun _ => exponentialProfile (B:ℂ) 1 1)
      (chart α r (z.1.1^2+(z.1.2 0)^2) z.2)
      (neutral r (z.1.2 0) (z.1.2 1))‖))
  simpa only [density,positiveDensity,KFCausalReciprocalNeutralLaplace.weight,mul_assoc] using he

theorem joint_integral_eq_energy (n : ℕ) (α β B : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (c : Fin n → ℂ) (hβ : 0 < β) (hp : 0 < (gamma α r).re)
    (hw : ∀ i, 0 < w i) (hd : ∀ i, 8*β*r.im^2 < 2*(gamma α r).re*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (∫ z, density mass2 quartic vacuum n α β B w r c z ∂jointMeasure) =
      energy mass2 quartic vacuum β B (fieldSlope r) (gamma α r)
        (8*β*r.im^2) w (fun i => c i*(w i:ℂ)) := by
  have hi := density_integrable mass2 quartic vacuum n α β B w r c hβ hd hm hq hv
  rw [KFCausalJointNeutralFourierIntegral.joint_integral_iterated _ hi]
  rw [show energy mass2 quartic vacuum β B (fieldSlope r) (gamma α r)
      (8*β*r.im^2) w (fun i => c i*(w i:ℂ)) =
      ∫ Y in Set.Ioi (0:ℝ), ∫ u : ℝ, ∫ v : ℝ,
        KFCausalCommonRealGaussianWeightedEnergy.density mass2 quartic vacuum β B (fieldSlope r)
          (gamma α r) (8*β*r.im^2) w (fun i => c i*(w i:ℂ)) ((u,v),Y) from
    KFCausalChargedProductFubini.integral_order _
      (KFCausalCommonRealGaussianWeightedEnergy.density_integrable mass2 quartic vacuum β B
        (fieldSlope r) (gamma α r) (8*β*r.im^2) w (fun i => c i*(w i:ℂ))
        hβ hp hw hd hm hq hv)]
  simp only [density_factor,Matrix.cons_val_zero,Matrix.cons_val_one,integral_mul_const,
    KFCausalCommonRealGaussianWeightedEnergy.density,KFCausalCommonRealGaussianWeightedEnergy.neutralLine]

#print axioms potential_upper
#print axioms density_nonnegative
#print axioms density_factor
#print axioms density_integrable
#print axioms joint_integral_eq_energy
end
end UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedJointEnergy

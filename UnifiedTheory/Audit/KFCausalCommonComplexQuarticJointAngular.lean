/- Literal common-complex-source Joint quartic density and its linked
field/tilt terms inherit the charged angular estimate. Every full-Joint
integrability and neutral marginal identity is proved before Fubini. -/
import UnifiedTheory.Audit.KFCausalChargedQuarticUniversalAngularLoss
import UnifiedTheory.Audit.KFCausalCommonComplexQuarticNeutralIntegral
import UnifiedTheory.Audit.KFCausalJointChargedNeutralReordering
import UnifiedTheory.Audit.KFCausalOriginalCommonRealGaussianEnergy

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonComplexQuarticJointAngular
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalReciprocalNeutralPositiveForm (profileSum)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalReciprocalNeutralKernel (neutral)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalChargedEvenMomentFamily (packet)
open KFCausalChargedEvenMomentImaginaryBound (gamma)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalCommonRealGaussianEnergy (neutralWeight neutralMoment neutral_moment_integrable)
open KFCausalAngularQuarticGaussianSmoothing (weight weightSlope)

variable (n : ℕ) (alpha beta A D : ℝ) (w : Fin n→ℝ) (r : ℂ) (c : Fin n→ℂ)

def source : ℂ := (A:ℂ)+(D:ℂ)*Complex.I
def jointBase (z : Joint) : ℝ :=
  Real.exp (-2*beta*(z.1.2 1)^2+8*beta*r.im^2*(z.1.2 0)^2)*
    ‖profileSum n w c (fun _=>exponentialProfile (source A D) 1 1)
      (chart alpha r (z.1.1^2+(z.1.2 0)^2) z.2)
      (neutral r (z.1.2 0) (z.1.2 1))‖^2

def channel (L : ℝ) (j k : ℕ) (z : Joint) : ℝ :=
  (z.1.2 0)^j*(z.1.2 1+L*z.1.2 0)^k*jointBase n alpha beta A D w r c z

def energyDensity (z : Joint) : ℝ := channel n alpha beta A D w r c (fieldSlope r) 0 4 z
def fieldDensity (z : Joint) : ℝ := 4*channel n alpha beta A D w r c (fieldSlope r) 1 3 z
def tiltDensity (z : Joint) : ℝ :=
  (16*beta*r.im^2*(z.1.2 0)^2-4*D*r.im*(z.1.2 0))*energyDensity n alpha beta A D w r c z

private theorem profile_factor (u v x Y : ℝ) :
    profileSum n w c (fun _=>exponentialProfile (source A D) 1 1)
      (chart alpha r (u^2+v^2) Y) (neutral r v x)=
      Complex.exp (source A D*neutral r v x)*
        packet 0 (gamma alpha r) w (fun i=>c i*(w i:ℂ)) ((u,v),Y) := by
  rw [KFCausalChargedEvenMomentFamily.packet_expansion]
  simp only [profileSum,KFCausalReciprocalWedgeLaplace.laplaceSum,exponentialProfile,
    Polynomial.eval_one,pow_zero,one_mul,mul_one,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : chart alpha r (u^2+v^2) Y=
      gamma alpha r*((u:ℂ)^2+(v:ℂ)^2)+conj (gamma alpha r)*(Y:ℂ) := by
    simp [chart,KFCausalReciprocalWedgeGeometry.gamma,gamma]
  rw [he]
  ring

theorem jointBase_factor (z : Joint) : jointBase n alpha beta A D w r c z=
    neutralWeight beta A (z.1.2 1)*KFCausalChargedQuarticAngularLoss.base (gamma alpha r)
      (8*beta*r.im^2) (4*D*r.im) w (fun i=>c i*(w i:ℂ)) ((z.1.1,z.1.2 0),z.2) := by
  unfold jointBase
  rw [profile_factor,norm_mul,mul_pow,Complex.norm_exp,←Real.exp_nat_mul]
  have he : 2*(source A D*neutral r (z.1.2 0) (z.1.2 1)).re=
      2*A*(z.1.2 1)-4*D*r.im*(z.1.2 0) := by
    simp [source,neutral,Complex.mul_re,Complex.mul_im]
    ring
  norm_num only [Nat.cast_ofNat] at *
  rw [he]
  unfold neutralWeight KFCausalChargedQuarticAngularLoss.base
  rw [←mul_assoc,←Real.exp_add,←mul_assoc,←Real.exp_add]
  congr 2
  ring

variable (hbeta : 0<beta) (hp : 0<(gamma alpha r).re) (hw : ∀i,0<w i)
  (hd : ∀i,8*beta*r.im^2<2*(gamma alpha r).re*w i)
include hbeta hp hw hd

theorem monomial_integrable (j k : ℕ) :
    Integrable (fun z:Joint=>(z.1.2 1)^j*(z.1.2 0)^k*jointBase n alpha beta A D w r c z)
      jointMeasure := by
  have hi := (KFCausalChargedQuarticAngularLoss.monomial_integrable k (gamma alpha r)
    (8*beta*r.im^2) (4*D*r.im) w (fun i=>c i*(w i:ℂ)) hp hw hd).mul_prod
    (neutral_moment_integrable beta A hbeta j)
  rw [←KFCausalJointChargedNeutralReordering.integrable_iff]
  apply hi.congr
  filter_upwards [] with z
  rw [jointBase_factor]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

omit hbeta hp hw hd in
private theorem binomial_channel (L v x : ℝ) (j k : ℕ) :
    v^j*(x+L*v)^k=∑a∈Finset.range (k+1),
      (L^(k-a)*(k.choose a:ℝ))*(x^a*v^(j+(k-a))) := by
  rw [add_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_pow,pow_add]
  ring

theorem channel_integrable (L : ℝ) (j k : ℕ) :
    Integrable (channel n alpha beta A D w r c L j k) jointMeasure := by
  have hi := integrable_finset_sum (Finset.range (k+1)) (fun a _=>
    (monomial_integrable n alpha beta A D w r c hbeta hp hw hd a (j+(k-a))).const_mul
      (L^(k-a)*(k.choose a:ℝ)))
  apply hi.congr
  filter_upwards [] with z
  unfold channel
  rw [binomial_channel,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem densities_integrable :
    Integrable (energyDensity n alpha beta A D w r c) jointMeasure ∧
    Integrable (fieldDensity n alpha beta A D w r c) jointMeasure ∧
    Integrable (tiltDensity n alpha beta A D w r c) jointMeasure := by
  refine ⟨channel_integrable n alpha beta A D w r c hbeta hp hw hd (fieldSlope r) 0 4,
    (channel_integrable n alpha beta A D w r c hbeta hp hw hd (fieldSlope r) 1 3).const_mul 4,?_⟩
  apply (((channel_integrable n alpha beta A D w r c hbeta hp hw hd (fieldSlope r) 2 4).const_mul
    (16*beta*r.im^2)).sub ((channel_integrable n alpha beta A D w r c hbeta hp hw hd
      (fieldSlope r) 1 4).const_mul (4*D*r.im))).congr
  filter_upwards [] with z
  simp only [Pi.sub_apply,tiltDensity,energyDensity,channel,pow_zero,one_mul,pow_one]
  ring

omit hp hw hd in
theorem energy_marginal (z : Charged) :
    (∫x:ℝ,energyDensity n alpha beta A D w r c ((z.1.1,![z.1.2,x]),z.2))=
      neutralMoment beta A 0*KFCausalChargedQuarticAngularLoss.energyDensity (1/(4*beta))
        (8*beta*r.im^2) (4*D*r.im) (A/(2*beta)) (fieldSlope r) (gamma alpha r)
        w (fun i=>c i*(w i:ℂ)) z := by
  have he (x:ℝ) : energyDensity n alpha beta A D w r c ((z.1.1,![z.1.2,x]),z.2)=
      ((x+fieldSlope r*z.1.2)^4*neutralWeight beta A x)*
        KFCausalChargedQuarticAngularLoss.base (gamma alpha r)
          (8*beta*r.im^2) (4*D*r.im) w (fun i=>c i*(w i:ℂ)) z := by
    simp only [energyDensity,channel,jointBase_factor,Matrix.cons_val_zero,
      Matrix.cons_val_one,pow_zero,one_mul]
    ring
  simp_rw [he]
  rw [integral_mul_const,KFCausalCommonComplexQuarticNeutralIntegral.quartic_integral beta A _ hbeta]
  unfold KFCausalChargedQuarticAngularLoss.energyDensity
  ring

omit hp hw hd in
theorem field_marginal (z : Charged) :
    (∫x:ℝ,fieldDensity n alpha beta A D w r c ((z.1.1,![z.1.2,x]),z.2))=
      neutralMoment beta A 0*KFCausalChargedQuarticAngularLoss.fieldDensity (1/(4*beta))
        (8*beta*r.im^2) (4*D*r.im) (A/(2*beta)) (fieldSlope r) (gamma alpha r)
        w (fun i=>c i*(w i:ℂ)) z := by
  have he (x:ℝ) : fieldDensity n alpha beta A D w r c ((z.1.1,![z.1.2,x]),z.2)=
      (4*(x+fieldSlope r*z.1.2)^3*neutralWeight beta A x)*
        (z.1.2*KFCausalChargedQuarticAngularLoss.base (gamma alpha r)
          (8*beta*r.im^2) (4*D*r.im) w (fun i=>c i*(w i:ℂ)) z) := by
    simp only [fieldDensity,channel,jointBase_factor,Matrix.cons_val_zero,Matrix.cons_val_one,pow_one]
    ring
  simp_rw [he]
  rw [integral_mul_const,KFCausalCommonComplexQuarticNeutralIntegral.cubic_integral beta A _ hbeta]
  unfold KFCausalChargedQuarticAngularLoss.fieldDensity
  ring

omit hp hw hd in
theorem tilt_marginal (z : Charged) :
    (∫x:ℝ,tiltDensity n alpha beta A D w r c ((z.1.1,![z.1.2,x]),z.2))=
      neutralMoment beta A 0*KFCausalChargedQuarticAngularLoss.tiltDensity (1/(4*beta))
        (8*beta*r.im^2) (4*D*r.im) (A/(2*beta)) (fieldSlope r) (gamma alpha r)
        w (fun i=>c i*(w i:ℂ)) z := by
  simp only [tiltDensity,Matrix.cons_val_zero,integral_const_mul]
  rw [energy_marginal n alpha beta A D w r c hbeta]
  unfold KFCausalChargedQuarticAngularLoss.tiltDensity
  ring

theorem joint_integrals :
    (∫z,energyDensity n alpha beta A D w r c z ∂jointMeasure)=
      neutralMoment beta A 0*KFCausalChargedQuarticAngularLoss.energy (1/(4*beta))
        (8*beta*r.im^2) (4*D*r.im) (A/(2*beta)) (fieldSlope r) (gamma alpha r) w (fun i=>c i*(w i:ℂ)) ∧
    (∫z,fieldDensity n alpha beta A D w r c z ∂jointMeasure)=
      neutralMoment beta A 0*KFCausalChargedQuarticAngularLoss.fieldSlope (1/(4*beta))
        (8*beta*r.im^2) (4*D*r.im) (A/(2*beta)) (fieldSlope r) (gamma alpha r) w (fun i=>c i*(w i:ℂ)) ∧
    (∫z,tiltDensity n alpha beta A D w r c z ∂jointMeasure)=
      neutralMoment beta A 0*KFCausalChargedQuarticAngularLoss.tilt (1/(4*beta))
        (8*beta*r.im^2) (4*D*r.im) (A/(2*beta)) (fieldSlope r) (gamma alpha r) w (fun i=>c i*(w i:ℂ)) := by
  obtain ⟨he,hf,ht⟩ := densities_integrable n alpha beta A D w r c hbeta hp hw hd
  constructor
  · rw [KFCausalJointChargedNeutralReordering.integral_order _ he]
    simp only [energy_marginal n alpha beta A D w r c hbeta,integral_const_mul,
      KFCausalChargedQuarticAngularLoss.energy]
  constructor
  · rw [KFCausalJointChargedNeutralReordering.integral_order _ hf]
    simp only [field_marginal n alpha beta A D w r c hbeta,integral_const_mul,
      KFCausalChargedQuarticAngularLoss.fieldSlope]
  · rw [KFCausalJointChargedNeutralReordering.integral_order _ ht]
    simp only [tilt_marginal n alpha beta A D w r c hbeta,integral_const_mul,
      KFCausalChargedQuarticAngularLoss.tilt]

omit n alpha beta A D w r c hbeta hp hw hd in
theorem global_loss : ∃ C:ℝ,0≤C ∧ ∀ (n:ℕ) (alpha beta A D:ℝ) (w:Fin n→ℝ) (r:ℂ) (c:Fin n→ℂ),
    0<beta→0<(gamma alpha r).re→(∀i,0<w i)→(∀i,8*beta*r.im^2<2*(gamma alpha r).re*w i)→
    0≤2*(∫z,tiltDensity n alpha beta A D w r c z ∂jointMeasure)-
      fieldSlope r*(∫z,fieldDensity n alpha beta A D w r c z ∂jointMeasure)+
      C*(∫z,energyDensity n alpha beta A D w r c z ∂jointMeasure) := by
  obtain ⟨C,hC,hbound⟩ := KFCausalChargedQuarticUniversalAngularLoss.global_loss
  refine ⟨C,hC,?_⟩
  intro n alpha beta A D w r c hbeta hp hw hd
  obtain ⟨he,hf,ht⟩ := joint_integrals n alpha beta A D w r c hbeta hp hw hd
  rw [he,hf,ht]
  have hb := hbound n (1/(4*beta)) (8*beta*r.im^2) (4*D*r.im) (A/(2*beta))
    (fieldSlope r) (gamma alpha r) w (fun i=>c i*(w i:ℂ)) (by positivity) (by positivity) hp hw hd
  have hh := mul_nonneg (KFCausalCommonComplexQuarticNeutralIntegral.mass_positive beta A hbeta).le hb
  convert hh using 1
  ring

#print axioms jointBase_factor
#print axioms monomial_integrable
#print axioms channel_integrable
#print axioms densities_integrable
#print axioms energy_marginal
#print axioms field_marginal
#print axioms tilt_marginal
#print axioms joint_integrals
#print axioms global_loss
end
end UnifiedTheory.Audit.KFCausalCommonComplexQuarticJointAngular

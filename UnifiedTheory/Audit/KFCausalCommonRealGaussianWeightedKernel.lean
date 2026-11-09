/- Exact weighted finite kernel for the literal common-real-source Joint
energy. Every coherent cross term is retained; absolute integrability
precedes the integral identities and local derivatives. -/
import UnifiedTheory.Audit.KFCausalGaussianWeightedSourceKernelDerivative
import UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedJointEnergy
import UnifiedTheory.Audit.KFCausalCommonRealGaussianOriginalField

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedKernel
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate BigOperators
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalCommonRealGaussianEnergy (neutralWeight)
open KFCausalCommonRealGaussianWeightedEnergy (potential energy neutralLine density)
open KFCausalChargedEvenMomentFamily (packet)
open KFCausalChargedCoolingWidthPositive (widthSum)
open KFCausalChargedCoolingFixedV (widthSum_re)
open KFCausalChargedEvenMomentImaginaryBound (gamma)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalGaussianWeightedSourceKernelDerivative (kernel slope familyForm)
variable (mass2 quartic vacuum : ℝ)

def pairDensity (β B L : ℝ) (S H : ℂ) (z : Joint) : ℂ :=
  (Complex.exp (-S*(z.1.1:ℂ)^2)*
    KFCausalGaussianWeightedSourcePlaneKernel.density mass2 quartic vacuum H (2*(β:ℂ)) 0 (2*(B:ℂ)) L z.1.2)*
      Complex.exp (-conj S*(z.2:ℂ))

theorem pair_integrable (β B L : ℝ) (S H : ℂ)
    (hβ : 0 < β) (hS : 0 < S.re) (hH : 0 < H.re) :
    Integrable (pairDensity mass2 quartic vacuum β B L S H) jointMeasure := by
  have hg : Integrable (fun u : ℝ => Complex.exp (-S*(u:ℂ)^2)) := by
    have hi := KFCausalComplexGaussianMoments.moment_integrable S hS 0
    change Integrable (fun u => KFCausalComplexGaussianMoments.moment S 0 u) at hi
    simpa only [KFCausalComplexGaussianMoments.moment,pow_zero,one_mul] using hi
  exact (hg.mul_prod (KFCausalGaussianWeightedSourcePlaneKernel.density_integrable mass2 quartic vacuum H
    (2*(β:ℂ)) 0 (2*(B:ℂ)) hH (by simpa using mul_pos (by norm_num : (0:ℝ)<2) hβ) L)).mul_prod
      (KFCausalReciprocalWedgeLaplace.laplace_integrable (conj S) (by simpa using hS))

theorem pair_integral (β B L : ℝ) (S H : ℂ)
    (hβ : 0 < β) (hS : 0 < S.re) (hH : 0 < H.re) :
    (∫ z, pairDensity mass2 quartic vacuum β B L S H z ∂jointMeasure) =
      kernel mass2 quartic vacuum S (conj S) H 0 (2*(B:ℂ)) β L := by
  unfold pairDensity jointMeasure
  rw [integral_prod_mul (fun z : ℝ × (Fin 2 → ℝ) => Complex.exp (-S*(z.1:ℂ)^2)*
      KFCausalGaussianWeightedSourcePlaneKernel.density mass2 quartic vacuum H (2*(β:ℂ)) 0 (2*(B:ℂ)) L z.2)
      (fun Y : ℝ => Complex.exp (-conj S*(Y:ℂ))),
    Measure.volume_eq_prod ℝ (Fin 2 → ℝ),
    integral_prod_mul (fun u : ℝ => Complex.exp (-S*(u:ℂ)^2))
      (KFCausalGaussianWeightedSourcePlaneKernel.density mass2 quartic vacuum H (2*(β:ℂ)) 0 (2*(B:ℂ)) L),
    KFCausalReciprocalWedgeLaplace.laplace_integral (conj S) (by simpa using hS)]
  have hg := KFCausalComplexGaussianMoments.value_zero S hS
  simp only [KFCausalComplexGaussianMoments.value,KFCausalComplexGaussianMoments.moment,
    pow_zero,one_mul] at hg
  rw [hg,KFCausalGaussianWeightedSourcePlaneKernel.density_integral mass2 quartic vacuum _ _ _ _ hH
    (by simpa using mul_pos (by norm_num : (0:ℝ)<2) hβ)]
  unfold kernel KFCausalGaussianSourceKernelDerivative.prefactor
    KFCausalGaussianWeightedSourcePlaneKernel.formula
  ring

theorem pair_factor (β B L d : ℝ) (S : ℂ) (z : Joint) :
    pairDensity mass2 quartic vacuum β B L S (S-(d:ℂ)) z =
      ((potential mass2 quartic vacuum (z.1.2 1+L*z.1.2 0)*neutralWeight β B (z.1.2 1)*
        Real.exp (d*(z.1.2 0)^2):ℝ):ℂ)*
      KFCausalChargedFourierGaussianMoments.density S (conj S) 0 0
        z.1.1 (z.1.2 0) z.2 := by
  rw [KFCausalChargedFourierGaussianMoments.density_expansion]
  simp only [pow_zero,one_mul,zero_mul,add_zero]
  unfold pairDensity KFCausalGaussianWeightedSourcePlaneKernel.density neutralWeight
  simp only [Complex.ofReal_mul,Complex.ofReal_exp,zero_mul,add_zero]
  have he : -S*(z.1.1:ℂ)^2+(-(S-(d:ℂ))*(z.1.2 0:ℂ)^2)+
      (-(2*(β:ℂ))*(z.1.2 1:ℂ)^2+2*(B:ℂ)*(z.1.2 1:ℂ))-
      conj S*(z.2:ℂ) =
      ((-2*β*(z.1.2 1)^2+2*B*(z.1.2 1):ℝ):ℂ)+
      ((d*(z.1.2 0)^2:ℝ):ℂ)+
      (-S*((z.1.1:ℂ)^2+(z.1.2 0:ℂ)^2)-conj S*(z.2:ℂ)) := by
    push_cast
    ring
  have hh := congrArg Complex.exp he
  push_cast at hh ⊢
  simp only [sub_eq_add_neg,Complex.exp_add,neg_mul] at hh ⊢
  linear_combination (potential mass2 quartic vacuum (z.1.2 1+L*z.1.2 0):ℂ)*hh

variable {ι : Type*} [Fintype ι]

def normDensity (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) (z : Joint) : ℝ :=
  (potential mass2 quartic vacuum (z.1.2 1+L*z.1.2 0)*neutralWeight β B (z.1.2 1)*Real.exp (d*(z.1.2 0)^2))*
    ‖packet 0 p w c ((z.1.1,z.1.2 0),z.2)‖^2

def familyKernel (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, (c i*conj (c j))*kernel mass2 quartic vacuum (widthSum p (w i) (w j))
    (conj (widthSum p (w i) (w j))) (widthSum p (w i) (w j)-(d:ℂ)) 0 (2*(B:ℂ)) β L

def familyFieldSlope (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, (c i*conj (c j))*slope mass2 quartic vacuum (widthSum p (w i) (w j))
    (conj (widthSum p (w i) (w j))) (widthSum p (w i) (w j)-(d:ℂ))
    0 (2*(B:ℂ)) 0 0 0 0 β L 1

omit [Fintype ι] in
private theorem floors (p : ℂ) (d : ℝ) (w : ι → ℝ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) (i j : ι) :
    0 < (widthSum p (w i) (w j)).re ∧ 0 < (widthSum p (w i) (w j)-(d:ℂ)).re := by
  rw [Complex.sub_re,Complex.ofReal_re,widthSum_re]
  constructor
  · exact mul_pos hp (add_pos (hw i) (hw j))
  · nlinarith [hd i,hd j]

theorem norm_density_expansion (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ)
    (c : ι → ℂ) (z : Joint) :
    (normDensity mass2 quartic vacuum β B L p d w c z:ℂ) =
      ∑ i, ∑ j, (c i*conj (c j))*pairDensity mass2 quartic vacuum β B L
        (widthSum p (w i) (w j)) (widthSum p (w i) (w j)-(d:ℂ)) z := by
  unfold normDensity
  rw [Complex.ofReal_mul,KFCausalChargedEvenMomentFamily.packet_square]
  simp only [Finset.mul_sum,mul_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [pair_factor]
  have he : conj (widthSum p (w i) (w j))=widthSum (conj p) (w i) (w j) := by
    simp [widthSum]
  rw [he]
  ring

omit [Fintype ι] in
private theorem cross_integrable (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i)
    (hd : ∀ i, d < 2*p.re*w i) (i j : ι) :
    Integrable (fun z => (c i*conj (c j))*pairDensity mass2 quartic vacuum β B L
      (widthSum p (w i) (w j)) (widthSum p (w i) (w j)-(d:ℂ)) z) jointMeasure := by
  have hf := floors p d w hp hw hd i j
  exact (pair_integrable mass2 quartic vacuum β B L _ _ hβ hf.1 hf.2).const_mul _

theorem norm_density_integrable (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    Integrable (normDensity mass2 quartic vacuum β B L p d w c) jointMeasure := by
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => cross_integrable mass2 quartic vacuum β B L p d w c hβ hp hw hd i j))
  have hc : Integrable (fun z => (normDensity mass2 quartic vacuum β B L p d w c z:ℂ)) jointMeasure :=
    hi.congr (Eventually.of_forall (fun z => (norm_density_expansion mass2 quartic vacuum β B L p d w c z).symm))
  simpa only [Complex.ofReal_re] using hc.re

theorem norm_density_integral (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    (∫ z, (normDensity mass2 quartic vacuum β B L p d w c z:ℂ) ∂jointMeasure) = familyKernel mass2 quartic vacuum β B L p d w c := by
  simp_rw [norm_density_expansion]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => cross_integrable mass2 quartic vacuum β B L p d w c hβ hp hw hd i j))]
  unfold familyKernel
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum Finset.univ (fun j _ => cross_integrable mass2 quartic vacuum β B L p d w c hβ hp hw hd i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  have hf := floors p d w hp hw hd i j
  rw [pair_integral mass2 quartic vacuum β B L _ _ hβ hf.1 hf.2]

theorem norm_integral_eq_energy (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (∫ z, normDensity mass2 quartic vacuum β B L p d w c z ∂jointMeasure) = energy mass2 quartic vacuum β B L p d w c := by
  rw [KFCausalJointNeutralFourierIntegral.joint_integral_iterated _
    (norm_density_integrable mass2 quartic vacuum β B L p d w c hβ hp hw hd)]
  rw [show energy mass2 quartic vacuum β B L p d w c = ∫ Y in Set.Ioi (0:ℝ), ∫ u : ℝ, ∫ v : ℝ,
      density mass2 quartic vacuum β B L p d w c ((u,v),Y) from
    KFCausalChargedProductFubini.integral_order _
      (KFCausalCommonRealGaussianWeightedEnergy.density_integrable mass2 quartic vacuum β B L p d w c hβ hp hw hd hm hq hv)]
  simp only [normDensity,Matrix.cons_val_zero,Matrix.cons_val_one,integral_mul_const,density,neutralLine]

theorem energy_cast_eq_family (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (energy mass2 quartic vacuum β B L p d w c:ℂ)=familyKernel mass2 quartic vacuum β B L p d w c := by
  have h := norm_density_integral mass2 quartic vacuum β B L p d w c hβ hp hw hd
  rwa [integral_complex_ofReal,norm_integral_eq_energy mass2 quartic vacuum β B L p d w c hβ hp hw hd hm hq hv] at h

theorem family_field_derivative (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    HasDerivAt (fun t => familyKernel mass2 quartic vacuum β B t p d w c) (familyFieldSlope mass2 quartic vacuum β B L p d w c) L := by
  unfold familyKernel familyFieldSlope
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  have hf := floors p d w hp hw hd i j
  have hn : conj (widthSum p (w i) (w j)) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.conj_re,Complex.zero_re] at hr
    linarith [hf.1]
  exact (KFCausalGaussianWeightedSourceKernelDerivative.kernel_derivative mass2 quartic vacuum
    (hasDerivAt_const L _) (hasDerivAt_const L _) (hasDerivAt_const L _)
    (hasDerivAt_const L _) (hasDerivAt_id L) hf.1 hf.2 hn (2*(B:ℂ)) β).const_mul _

theorem actual_field_derivative (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    HasDerivAt (fun t => energy mass2 quartic vacuum β B t p d w c) (familyFieldSlope mass2 quartic vacuum β B L p d w c).re L := by
  have he : (fun t => energy mass2 quartic vacuum β B t p d w c) = fun t => (familyKernel mass2 quartic vacuum β B t p d w c).re := by
    funext t
    exact congrArg Complex.re (energy_cast_eq_family mass2 quartic vacuum β B t p d w c hβ hp hw hd hm hq hv)
  rw [he]
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt L (family_field_derivative mass2 quartic vacuum β B L p d w c hp hw hd)

theorem field_slope_bounds (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    0 ≤ L*(familyFieldSlope mass2 quartic vacuum β B L p d w c).re ∧
      L*(familyFieldSlope mass2 quartic vacuum β B L p d w c).re ≤ 4*energy mass2 quartic vacuum β B L p d w c := by
  have hb := KFCausalCommonRealGaussianWeightedEnergy.field_derivative_bounds mass2 quartic vacuum β B L p d w c hβ hp hw hd hm hq hv
  rwa [(actual_field_derivative mass2 quartic vacuum β B L p d w c hβ hp hw hd hm hq hv).deriv] at hb

theorem familyForm_eq_kernel (n : ℕ) (α β : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (B : ℝ) (c : Fin n → ℂ) :
    familyForm mass2 quartic vacuum n α β w r (fun _ => (B:ℂ)) c =
      familyKernel mass2 quartic vacuum β B (fieldSlope r) (gamma α r)
        (8*β*r.im^2) w (fun i => c i*(w i:ℂ)) := by
  unfold familyForm familyKernel KFCausalGaussianWeightedSourceKernelDerivative.pairKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [KFCausalReciprocalCrossGeometry.C,KFCausalCommonRealGaussianOriginalField.charged_width]
  simp only [KFCausalGaussianSourceJointKernel.sourceV,KFCausalGaussianSourceJointKernel.sourceX,
    Complex.conj_ofReal,sub_self,mul_zero,map_mul]
  rw [show (B:ℂ)+(B:ℂ)=2*(B:ℂ) by ring]
  ring

theorem joint_integral_eq_family (n : ℕ) (α β B : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (c : Fin n → ℂ) (hβ : 0 < β) (hp : 0 < (gamma α r).re)
    (hw : ∀ i, 0 < w i) (hd : ∀ i, 8*β*r.im^2 < 2*(gamma α r).re*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (((∫ z, KFCausalCommonRealGaussianWeightedJointEnergy.density mass2 quartic vacuum
      n α β B w r c z ∂jointMeasure):ℝ):ℂ)=
      familyForm mass2 quartic vacuum n α β w r (fun _ => (B:ℂ)) c := by
  rw [KFCausalCommonRealGaussianWeightedJointEnergy.joint_integral_eq_energy
    mass2 quartic vacuum n α β B w r c hβ hp hw hd hm hq hv,familyForm_eq_kernel]
  exact energy_cast_eq_family mass2 quartic vacuum β B (fieldSlope r) (gamma α r)
    (8*β*r.im^2) w (fun i => c i*(w i:ℂ)) hβ hp hw hd hm hq hv

def originalFieldSlope (n : ℕ) (α β : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (B : ℝ) (c : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))*
    slope mass2 quartic vacuum (KFCausalReciprocalCrossGeometry.B α (w i) (w j) r)
      (conj (KFCausalReciprocalCrossGeometry.B α (w i) (w j) r))
      (KFCausalReciprocalCrossGeometry.C α β (w i) (w j) r)
      0 (2*(B:ℂ)) 0 0 0 0 β (fieldSlope r) 1

theorem original_field_eq (n : ℕ) (α β : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (B : ℝ) (c : Fin n → ℂ) :
    originalFieldSlope mass2 quartic vacuum n α β w r B c =
      familyFieldSlope mass2 quartic vacuum β B (fieldSlope r)
        (gamma α r) (8*β*r.im^2) w (fun i => c i*(w i:ℂ)) := by
  unfold originalFieldSlope familyFieldSlope
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [KFCausalReciprocalCrossGeometry.C,KFCausalCommonRealGaussianOriginalField.charged_width]
  simp only [map_mul,Complex.conj_ofReal]
  ring

theorem original_field_bounds (n : ℕ) (α β : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (B : ℝ) (c : Fin n → ℂ) (hβ : 0 < β)
    (hp : 0 < (gamma α r).re) (hw : ∀ i, 0 < w i)
    (hd : ∀ i, 8*β*r.im^2 < 2*(gamma α r).re*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    0 ≤ fieldSlope r*(originalFieldSlope mass2 quartic vacuum n α β w r B c).re ∧
    fieldSlope r*(originalFieldSlope mass2 quartic vacuum n α β w r B c).re ≤
      4*(∫ z, KFCausalCommonRealGaussianWeightedJointEnergy.density mass2 quartic vacuum
        n α β B w r c z ∂jointMeasure) := by
  rw [KFCausalCommonRealGaussianWeightedJointEnergy.joint_integral_eq_energy
    mass2 quartic vacuum n α β B w r c hβ hp hw hd hm hq hv,original_field_eq]
  exact field_slope_bounds mass2 quartic vacuum β B (fieldSlope r) (gamma α r)
    (8*β*r.im^2) w (fun i => c i*(w i:ℂ)) hβ hp hw hd hm hq hv

#print axioms pair_integrable
#print axioms pair_integral
#print axioms pair_factor
#print axioms norm_density_expansion
#print axioms norm_density_integrable
#print axioms norm_density_integral
#print axioms norm_integral_eq_energy
#print axioms energy_cast_eq_family
#print axioms family_field_derivative
#print axioms actual_field_derivative
#print axioms field_slope_bounds
#print axioms familyForm_eq_kernel
#print axioms joint_integral_eq_family
#print axioms original_field_eq
#print axioms original_field_bounds
end
end UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedKernel


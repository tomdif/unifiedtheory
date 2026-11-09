/- The original raw quartic Joint energy equals the weighted physical
Wick kernel with couplings (0,4,0). Its actual clock response is identified
by two independently justified derivatives, retaining every cross term. -/
import UnifiedTheory.Audit.KFCausalFiniteChannelJointClockDerivative
import UnifiedTheory.Audit.KFCausalCommonComplexQuarticActualBound
import UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedTransport

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace UnifiedTheory.Audit.KFCausalCommonComplexQuarticClockKernel
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate BigOperators
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalCommonRealGaussianEnergy (neutralWeight)
open KFCausalCommonRealGaussianWeightedEnergy (potential)
open KFCausalChargedEvenMomentFamily (packet)
open KFCausalChargedCoolingWidthPositive (widthSum)
open KFCausalChargedCoolingFixedV (widthSum_re)
open KFCausalChargedEvenMomentImaginaryBound (gamma)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalGaussianWeightedSourceKernelDerivative (kernel slope familyForm familySlope)
open KFCausalCommonComplexQuarticJointAngular (source energyDensity)
open KFCausalClockFloorRelativeShift (scale scale_smooth)
private def pairDensity (β A q L : ℝ) (S H : ℂ) (z : Joint) : ℂ :=
  (Complex.exp (-S*(z.1.1:ℂ)^2)*
    KFCausalGaussianWeightedSourcePlaneKernel.density 0 4 0 H (2*(β:ℂ)) (-(q:ℂ)) ((2*A:ℝ):ℂ) L z.1.2)*
      Complex.exp (-conj S*(z.2:ℂ))

private theorem pair_integrable (β A q L : ℝ) (S H : ℂ)
    (hβ : 0 < β) (hS : 0 < S.re) (hH : 0 < H.re) :
    Integrable (pairDensity β A q L S H) jointMeasure := by
  have hg : Integrable (fun u : ℝ => Complex.exp (-S*(u:ℂ)^2)) := by
    have hi := KFCausalComplexGaussianMoments.moment_integrable S hS 0
    change Integrable (fun u => KFCausalComplexGaussianMoments.moment S 0 u) at hi
    simpa only [KFCausalComplexGaussianMoments.moment,pow_zero,one_mul] using hi
  exact (hg.mul_prod (KFCausalGaussianWeightedSourcePlaneKernel.density_integrable 0 4 0 H
    (2*(β:ℂ)) (-(q:ℂ)) ((2*A:ℝ):ℂ) hH (by simpa using mul_pos (by norm_num : (0:ℝ)<2) hβ) L)).mul_prod
      (KFCausalReciprocalWedgeLaplace.laplace_integrable (conj S) (by simpa using hS))

private theorem pair_integral (β A q L : ℝ) (S H : ℂ)
    (hβ : 0 < β) (hS : 0 < S.re) (hH : 0 < H.re) :
    (∫ z, pairDensity β A q L S H z ∂jointMeasure) =
      kernel 0 4 0 S (conj S) H (-(q:ℂ)) ((2*A:ℝ):ℂ) β L := by
  unfold pairDensity jointMeasure
  rw [integral_prod_mul (fun z : ℝ × (Fin 2 → ℝ) => Complex.exp (-S*(z.1:ℂ)^2)*
      KFCausalGaussianWeightedSourcePlaneKernel.density 0 4 0 H (2*(β:ℂ)) (-(q:ℂ)) ((2*A:ℝ):ℂ) L z.2)
      (fun Y : ℝ => Complex.exp (-conj S*(Y:ℂ))),
    Measure.volume_eq_prod ℝ (Fin 2 → ℝ),
    integral_prod_mul (fun u : ℝ => Complex.exp (-S*(u:ℂ)^2))
      (KFCausalGaussianWeightedSourcePlaneKernel.density 0 4 0 H (2*(β:ℂ)) (-(q:ℂ)) ((2*A:ℝ):ℂ) L),
    KFCausalReciprocalWedgeLaplace.laplace_integral (conj S) (by simpa using hS)]
  have hg := KFCausalComplexGaussianMoments.value_zero S hS
  simp only [KFCausalComplexGaussianMoments.value,KFCausalComplexGaussianMoments.moment,
    pow_zero,one_mul] at hg
  rw [hg,KFCausalGaussianWeightedSourcePlaneKernel.density_integral 0 4 0 _ _ _ _ hH
    (by simpa using mul_pos (by norm_num : (0:ℝ)<2) hβ)]
  unfold kernel KFCausalGaussianSourceKernelDerivative.prefactor
    KFCausalGaussianWeightedSourcePlaneKernel.formula
  ring

private theorem pair_factor (β A q L d : ℝ) (S : ℂ) (z : Joint) :
    pairDensity β A q L S (S-(d:ℂ)) z =
      ((potential 0 4 0 (z.1.2 1+L*z.1.2 0)*neutralWeight β A (z.1.2 1)*
        Real.exp (d*(z.1.2 0)^2-q*(z.1.2 0)):ℝ):ℂ)*
      KFCausalChargedFourierGaussianMoments.density S (conj S) 0 0
        z.1.1 (z.1.2 0) z.2 := by
  rw [KFCausalChargedFourierGaussianMoments.density_expansion]
  simp only [pow_zero,one_mul,zero_mul,add_zero]
  unfold pairDensity KFCausalGaussianWeightedSourcePlaneKernel.density neutralWeight
  simp only [Complex.ofReal_mul,Complex.ofReal_exp]
  have he : -S*(z.1.1:ℂ)^2+(-(S-(d:ℂ))*(z.1.2 0:ℂ)^2-(q:ℂ)*(z.1.2 0:ℂ))+
      (-(2*(β:ℂ))*(z.1.2 1:ℂ)^2+((2*A:ℝ):ℂ)*(z.1.2 1:ℂ))-conj S*(z.2:ℂ) =
      ((-2*β*(z.1.2 1)^2+2*A*(z.1.2 1):ℝ):ℂ)+
      ((d*(z.1.2 0)^2-q*(z.1.2 0):ℝ):ℂ)+
      (-S*((z.1.1:ℂ)^2+(z.1.2 0:ℂ)^2)-conj S*(z.2:ℂ)) := by
    push_cast
    ring
  have hh := congrArg Complex.exp he
  push_cast at hh ⊢
  simp only [sub_eq_add_neg,Complex.exp_add,neg_mul] at hh ⊢
  linear_combination (potential 0 4 0 (z.1.2 1+L*z.1.2 0):ℂ)*hh

variable {ι : Type*} [Fintype ι]

private def normDensity (β A q L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) (z : Joint) : ℝ :=
  (potential 0 4 0 (z.1.2 1+L*z.1.2 0)*neutralWeight β A (z.1.2 1)*Real.exp (d*(z.1.2 0)^2-q*(z.1.2 0)))*
    ‖packet 0 p w c ((z.1.1,z.1.2 0),z.2)‖^2

private def familyKernel (β A q L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, (c i*conj (c j))*kernel 0 4 0 (widthSum p (w i) (w j))
    (conj (widthSum p (w i) (w j))) (widthSum p (w i) (w j)-(d:ℂ)) (-(q:ℂ)) ((2*A:ℝ):ℂ) β L

omit [Fintype ι] in
private theorem floors (p : ℂ) (d : ℝ) (w : ι → ℝ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) (i j : ι) :
    0 < (widthSum p (w i) (w j)).re ∧ 0 < (widthSum p (w i) (w j)-(d:ℂ)).re := by
  rw [Complex.sub_re,Complex.ofReal_re,widthSum_re]
  constructor
  · exact mul_pos hp (add_pos (hw i) (hw j))
  · nlinarith [hd i,hd j]

private theorem norm_density_expansion (β A q L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ)
    (c : ι → ℂ) (z : Joint) :
    (normDensity β A q L p d w c z:ℂ) =
      ∑ i, ∑ j, (c i*conj (c j))*pairDensity β A q L
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
private theorem cross_integrable (β A q L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i)
    (hd : ∀ i, d < 2*p.re*w i) (i j : ι) :
    Integrable (fun z => (c i*conj (c j))*pairDensity β A q L
      (widthSum p (w i) (w j)) (widthSum p (w i) (w j)-(d:ℂ)) z) jointMeasure := by
  have hf := floors p d w hp hw hd i j
  exact (pair_integrable β A q L _ _ hβ hf.1 hf.2).const_mul _

private theorem norm_density_integrable (β A q L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    Integrable (normDensity β A q L p d w c) jointMeasure := by
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => cross_integrable β A q L p d w c hβ hp hw hd i j))
  have hc : Integrable (fun z => (normDensity β A q L p d w c z:ℂ)) jointMeasure :=
    hi.congr (Eventually.of_forall (fun z => (norm_density_expansion β A q L p d w c z).symm))
  simpa only [Complex.ofReal_re] using hc.re

private theorem norm_density_integral (β A q L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    (∫ z, (normDensity β A q L p d w c z:ℂ) ∂jointMeasure) = familyKernel β A q L p d w c := by
  simp_rw [norm_density_expansion]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => cross_integrable β A q L p d w c hβ hp hw hd i j))]
  unfold familyKernel
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum Finset.univ (fun j _ => cross_integrable β A q L p d w c hβ hp hw hd i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  have hf := floors p d w hp hw hd i j
  rw [pair_integral β A q L _ _ hβ hf.1 hf.2]

private theorem familyForm_eq_kernel (n : ℕ) (α β A D : ℝ) (w : Fin n→ℝ)
    (r : ℂ) (c : Fin n→ℂ) :
    familyForm 0 4 0 n α β w r (fun _=>source A D) c=
      familyKernel β A (4*D*r.im) (fieldSlope r) (gamma α r) (8*β*r.im^2)
        w (fun i=>c i*(w i:ℂ)) := by
  have hv : KFCausalGaussianSourceJointKernel.sourceV r (source A D) (source A D)=
      -((4*D*r.im:ℝ):ℂ) := by
    simp only [KFCausalGaussianSourceJointKernel.sourceV,source,map_add,map_mul,
      Complex.conj_ofReal,Complex.conj_I]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hx : KFCausalGaussianSourceJointKernel.sourceX (source A D) (source A D)=((2*A:ℝ):ℂ) := by
    simp [KFCausalGaussianSourceJointKernel.sourceX,source]
    ring
  unfold familyForm familyKernel KFCausalGaussianWeightedSourceKernelDerivative.pairKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [KFCausalReciprocalCrossGeometry.C,KFCausalCommonRealGaussianOriginalField.charged_width,hv,hx]
  simp only [map_mul,Complex.conj_ofReal]
  ring

private theorem joint_integral_eq_family (n : ℕ) (α β A D : ℝ) (w : Fin n→ℝ)
    (r : ℂ) (c : Fin n→ℂ) (hβ : 0<β) (hp : 0<(gamma α r).re)
    (hw : ∀i,0<w i) (hd : ∀i,8*β*r.im^2<2*(gamma α r).re*w i) :
    (((∫z,energyDensity n α β A D w r c z ∂jointMeasure):ℝ):ℂ)=
      familyForm 0 4 0 n α β w r (fun _=>source A D) c := by
  have he : energyDensity n α β A D w r c=
      normDensity β A (4*D*r.im) (fieldSlope r) (gamma α r) (8*β*r.im^2)
        w (fun i=>c i*(w i:ℂ)) := by
    funext z
    simp only [energyDensity,KFCausalCommonComplexQuarticJointAngular.channel,
      KFCausalCommonComplexQuarticJointAngular.jointBase_factor,pow_zero,one_mul,
      KFCausalChargedQuarticAngularLoss.base,normDensity,potential]
    ring
  rw [he,familyForm_eq_kernel,←integral_complex_ofReal]
  exact norm_density_integral β A (4*D*r.im) (fieldSlope r) (gamma α r) (8*β*r.im^2)
    w (fun i=>c i*(w i:ℂ)) hβ hp hw hd

private theorem actual_geometry (n : ℕ) (α β ε y s : ℝ) (w : Fin n→ℝ)
    (hα : 0<α) (hβ : 0<β) (hwidth : 32*β≤α) (hε : 0<ε)
    (hy : |y|≤Real.pi*ε/3) (hw : ∀i,1≤w i) :
    0<(gamma α (scale ε y s)).re ∧
    (∀i,8*β*(scale ε y s).im^2<2*(gamma α (scale ε y s)).re*w i) ∧
    (∀i,0<(w i*α)*KFCausalReciprocalGaussianCoordinates.area (scale ε y s)-8*β*(scale ε y s).im^2) := by
  have ha := KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy
  have hA := KFCausalClockFloorExactScaleRegion.square_re_half_le ε y s hε hy
  have hr : |(scale ε y s).im|<(scale ε y s).re := by
    nlinarith [sq_abs (scale ε y s).im,abs_nonneg (scale ε y s).im]
  have hp := KFCausalChargedCoolingFixedV.actual_gamma_re_positive α _ hα hr
  have hf (i : Fin n) : 0<(w i*α)*KFCausalReciprocalGaussianCoordinates.area (scale ε y s)-8*β*(scale ε y s).im^2 := by
    have hreg := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy
    obtain ⟨hc,ha'⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hreg
    exact (KFCausalJointFourierDilationQuartic.width_floors α _ (w i) β (hw i) ha' hc).2
  refine ⟨hp,?_,hf⟩
  intro i
  have he : 2*(gamma α (scale ε y s)).re=α*KFCausalReciprocalGaussianCoordinates.area (scale ε y s) := by
    simp [gamma,KFCausalReciprocalGaussianCoordinates.area,pow_two,Complex.mul_re,Complex.mul_im]
    ring
  rw [he]
  nlinarith [hf i]

theorem actual_energy_eq_family (n : ℕ) (α β ε y s A D : ℝ) (w : Fin n→ℝ)
    (c : Fin n→ℂ) (hα : 0<α) (hβ : 0<β) (hwidth : 32*β≤α) (hε : 0<ε)
    (hy : |y|≤Real.pi*ε/3) (hw : ∀i,1≤w i) :
    (∫p:Joint,energyDensity n α β A D w (scale ε y s) c p ∂jointMeasure)=
      (familyForm 0 4 0 n α β w (scale ε y s) (fun _=>source A D) c).re := by
  have hg := actual_geometry n α β ε y s w hα hβ hwidth hε hy hw
  exact congrArg Complex.re (joint_integral_eq_family n α β A D w (scale ε y s) c hβ hg.1
    (fun i=>lt_of_lt_of_le (by norm_num) (hw i)) hg.2.1)

theorem actual_response_eq_familySlope (n : ℕ) (α β ε y s A D : ℝ) (w : Fin n→ℝ)
    (c : Fin n→ℂ) (hα : 0<α) (hβ : 0<β) (hwidth : 32*β≤α) (hε : 0<ε)
    (hy : |y|≤Real.pi*ε/3) (hw : ∀i,1≤w i) :
    (∫p:Joint,KFCausalJointNeutralFourierOuterDensity.spatialFieldResponse n α β w
      (fun _=>source A D) c (fun _=>1) (scale ε y s) (deriv (scale ε y) s)
      p.1.1 (p.1.2 0) p.2 2 (p.1.2 1) ∂jointMeasure)=
      (familySlope 0 4 0 n α β w (scale ε y s) (deriv (scale ε y) s) (fun _=>source A D) c).re := by
  have hwp : ∀i,0<w i := fun i=>lt_of_lt_of_le (by norm_num) (hw i)
  have he : (fun t=>∫p:Joint,KFCausalJointFourierDilationRepresentation.fieldDensity n α β w
      (fun _=>source A D) c (fun _=>1) (scale ε y t) 0 0 2 p ∂jointMeasure)=
      fun t=>(familyForm 0 4 0 n α β w (scale ε y t) (fun _=>source A D) c).re := by
    funext t
    simp_rw [KFCausalCommonComplexQuarticJointResponse.original_energy_density]
    have hg := actual_geometry n α β ε y t w hα hβ hwidth hε hy hw
    exact congrArg Complex.re (joint_integral_eq_family n α β A D w (scale ε y t) c hβ hg.1 hwp hg.2.1)
  have hj := KFCausalFiniteChannelJointClockDerivative.spatial_integral_derivative n α β ε y w
    (fun _=>source A D) c (fun _=>1) hα hβ hwidth hε hy hw 2 s
  rw [he] at hj
  have hg := actual_geometry n α β ε y s w hα hβ hwidth hε hy hw
  have hf (i j : Fin n) := KFCausalGaussianSourceJointKernel.pair_floors α β (w i) (w j)
    (scale ε y s) hβ (hg.2.2 i) (hg.2.2 j)
  have hk := KFCausalGaussianWeightedSourceKernelDerivative.familyForm_derivative 0 4 0
    (((scale_smooth ε y hε hy).differentiable (by norm_num)).differentiableAt.hasDerivAt)
    n α β w (fun _=>source A D) c (fun i j=>(hf i j).1) (fun i j=>(hf i j).2)
  exact hj.unique (Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hk)

#print axioms actual_energy_eq_family
#print axioms actual_response_eq_familySlope
end
end UnifiedTheory.Audit.KFCausalCommonComplexQuarticClockKernel

/- The exact arbitrary-field-slope kernel is attached to the actual full
coherent common-real-source norm before its field derivative is identified. -/
import UnifiedTheory.Audit.KFCausalCommonRealGaussianFieldKernel
import UnifiedTheory.Audit.KFCausalCommonRealGaussianMonotonicity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonRealGaussianFieldFamily
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate BigOperators
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalCommonRealGaussianEnergy (neutralWeight neutralLine density energy)
open KFCausalChargedEvenMomentFamily (packet)
open KFCausalChargedCoolingWidthPositive (widthSum)
open KFCausalChargedCoolingFixedV (widthSum_re)
open KFCausalCommonRealGaussianFieldKernel
open KFCausalGaussianSourceKernelDerivative (kernel slope)
open KFCausalQuarticPlaneDomination (potential)
variable {ι : Type*} [Fintype ι]

def normDensity (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) (z : Joint) : ℝ :=
  (potential (z.1.2 1+L*z.1.2 0)*neutralWeight β B (z.1.2 1)*Real.exp (d*(z.1.2 0)^2))*
    ‖packet 0 p w c ((z.1.1,z.1.2 0),z.2)‖^2

def familyKernel (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, (c i*conj (c j))*kernel (widthSum p (w i) (w j))
    (conj (widthSum p (w i) (w j))) (widthSum p (w i) (w j)-(d:ℂ)) 0 (2*(B:ℂ)) β L

def familyFieldSlope (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, (c i*conj (c j))*slope (widthSum p (w i) (w j))
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
    (normDensity β B L p d w c z:ℂ) =
      ∑ i, ∑ j, (c i*conj (c j))*pairDensity β B L
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
    Integrable (fun z => (c i*conj (c j))*pairDensity β B L
      (widthSum p (w i) (w j)) (widthSum p (w i) (w j)-(d:ℂ)) z) jointMeasure := by
  have hf := floors p d w hp hw hd i j
  exact (pair_integrable β B L _ _ hβ hf.1 hf.2).const_mul _

theorem norm_density_integrable (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    Integrable (normDensity β B L p d w c) jointMeasure := by
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => cross_integrable β B L p d w c hβ hp hw hd i j))
  have hc : Integrable (fun z => (normDensity β B L p d w c z:ℂ)) jointMeasure :=
    hi.congr (Eventually.of_forall (fun z => (norm_density_expansion β B L p d w c z).symm))
  simpa only [Complex.ofReal_re] using hc.re

theorem norm_density_integral (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    (∫ z, (normDensity β B L p d w c z:ℂ) ∂jointMeasure) = familyKernel β B L p d w c := by
  simp_rw [norm_density_expansion]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => cross_integrable β B L p d w c hβ hp hw hd i j))]
  unfold familyKernel
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum Finset.univ (fun j _ => cross_integrable β B L p d w c hβ hp hw hd i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  have hf := floors p d w hp hw hd i j
  rw [pair_integral β B L _ _ hβ hf.1 hf.2]

theorem norm_integral_eq_energy (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    (∫ z, normDensity β B L p d w c z ∂jointMeasure) = energy β B L p d w c := by
  rw [KFCausalJointNeutralFourierIntegral.joint_integral_iterated _
    (norm_density_integrable β B L p d w c hβ hp hw hd)]
  rw [show energy β B L p d w c = ∫ Y in Set.Ioi (0:ℝ), ∫ u : ℝ, ∫ v : ℝ,
      density β B L p d w c ((u,v),Y) from
    KFCausalChargedProductFubini.integral_order _
      (KFCausalCommonRealGaussianEnergy.density_integrable β B L p d w c hβ hp hw hd)]
  simp only [normDensity,Matrix.cons_val_zero,Matrix.cons_val_one,integral_mul_const,density,neutralLine]

theorem energy_cast_eq_family (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    (energy β B L p d w c:ℂ)=familyKernel β B L p d w c := by
  have h := norm_density_integral β B L p d w c hβ hp hw hd
  rwa [integral_complex_ofReal,norm_integral_eq_energy β B L p d w c hβ hp hw hd] at h

theorem family_field_derivative (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    HasDerivAt (fun t => familyKernel β B t p d w c) (familyFieldSlope β B L p d w c) L := by
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
  exact (KFCausalGaussianSourceKernelDerivative.kernel_derivative
    (hasDerivAt_const L _) (hasDerivAt_const L _) (hasDerivAt_const L _)
    (hasDerivAt_const L _) (hasDerivAt_id L) hf.1 hf.2 hn (2*(B:ℂ)) β).const_mul _

theorem actual_field_derivative (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    HasDerivAt (fun t => energy β B t p d w c) (familyFieldSlope β B L p d w c).re L := by
  have he : (fun t => energy β B t p d w c) = fun t => (familyKernel β B t p d w c).re := by
    funext t
    exact congrArg Complex.re (energy_cast_eq_family β B t p d w c hβ hp hw hd)
  rw [he]
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt L (family_field_derivative β B L p d w c hp hw hd)

theorem field_slope_bounds (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    0 ≤ L*(familyFieldSlope β B L p d w c).re ∧
      L*(familyFieldSlope β B L p d w c).re ≤ 4*energy β B L p d w c := by
  have hb := KFCausalCommonRealGaussianMonotonicity.field_derivative_bounds β B L p d w c hβ hp hw hd
  rwa [(actual_field_derivative β B L p d w c hβ hp hw hd).deriv] at hb

#print axioms norm_density_expansion
#print axioms norm_density_integrable
#print axioms norm_density_integral
#print axioms norm_integral_eq_energy
#print axioms energy_cast_eq_family
#print axioms family_field_derivative
#print axioms actual_field_derivative
#print axioms field_slope_bounds
end
end UnifiedTheory.Audit.KFCausalCommonRealGaussianFieldFamily

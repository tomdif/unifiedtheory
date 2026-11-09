/- Exact arbitrary-field-slope kernel for the actual common-real-source
quartic norm. Integrability and the full coherent density identity are derived. -/
import UnifiedTheory.Audit.KFCausalCommonRealGaussianEnergy
import UnifiedTheory.Audit.KFCausalGaussianSourceKernelDerivative
import UnifiedTheory.Audit.KFCausalChargedProductFubini

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonRealGaussianFieldKernel
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate BigOperators
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalCommonRealGaussianEnergy (neutralWeight energy)
open KFCausalChargedEvenMomentFamily (packet)
open KFCausalGaussianSourceKernelDerivative (kernel slope)
open KFCausalChargedCoolingWidthPositive (widthSum)
open KFCausalChargedCoolingFixedV (widthSum_re)
open KFCausalQuarticPlaneDomination (potential)

def pairDensity (β B L : ℝ) (S H : ℂ) (z : Joint) : ℂ :=
  (Complex.exp (-S*(z.1.1:ℂ)^2)*
    KFCausalGaussianSourcePlaneKernel.density H (2*(β:ℂ)) 0 (2*(B:ℂ)) L z.1.2)*
      Complex.exp (-conj S*(z.2:ℂ))

theorem pair_integrable (β B L : ℝ) (S H : ℂ)
    (hβ : 0 < β) (hS : 0 < S.re) (hH : 0 < H.re) :
    Integrable (pairDensity β B L S H) jointMeasure := by
  have hg : Integrable (fun u : ℝ => Complex.exp (-S*(u:ℂ)^2)) := by
    have hi := KFCausalComplexGaussianMoments.moment_integrable S hS 0
    change Integrable (fun u => KFCausalComplexGaussianMoments.moment S 0 u) at hi
    simpa only [KFCausalComplexGaussianMoments.moment,pow_zero,one_mul] using hi
  exact (hg.mul_prod (KFCausalGaussianSourcePlaneKernel.density_integrable H
    (2*(β:ℂ)) 0 (2*(B:ℂ)) hH (by simpa using mul_pos (by norm_num : (0:ℝ)<2) hβ) L)).mul_prod
      (KFCausalReciprocalWedgeLaplace.laplace_integrable (conj S) (by simpa using hS))

theorem pair_integral (β B L : ℝ) (S H : ℂ)
    (hβ : 0 < β) (hS : 0 < S.re) (hH : 0 < H.re) :
    (∫ z, pairDensity β B L S H z ∂jointMeasure) =
      kernel S (conj S) H 0 (2*(B:ℂ)) β L := by
  unfold pairDensity jointMeasure
  rw [integral_prod_mul (fun z : ℝ × (Fin 2 → ℝ) => Complex.exp (-S*(z.1:ℂ)^2)*
      KFCausalGaussianSourcePlaneKernel.density H (2*(β:ℂ)) 0 (2*(B:ℂ)) L z.2)
      (fun Y : ℝ => Complex.exp (-conj S*(Y:ℂ))),
    Measure.volume_eq_prod ℝ (Fin 2 → ℝ),
    integral_prod_mul (fun u : ℝ => Complex.exp (-S*(u:ℂ)^2))
      (KFCausalGaussianSourcePlaneKernel.density H (2*(β:ℂ)) 0 (2*(B:ℂ)) L),
    KFCausalReciprocalWedgeLaplace.laplace_integral (conj S) (by simpa using hS)]
  have hg := KFCausalComplexGaussianMoments.value_zero S hS
  simp only [KFCausalComplexGaussianMoments.value,KFCausalComplexGaussianMoments.moment,
    pow_zero,one_mul] at hg
  rw [hg,KFCausalGaussianSourcePlaneKernel.density_integral _ _ _ _ hH
    (by simpa using mul_pos (by norm_num : (0:ℝ)<2) hβ)]
  unfold kernel KFCausalGaussianSourceKernelDerivative.prefactor
    KFCausalGaussianSourcePlaneKernel.formula
  ring

theorem pair_factor (β B L d : ℝ) (S : ℂ) (z : Joint) :
    pairDensity β B L S (S-(d:ℂ)) z =
      ((potential (z.1.2 1+L*z.1.2 0)*neutralWeight β B (z.1.2 1)*
        Real.exp (d*(z.1.2 0)^2):ℝ):ℂ)*
      KFCausalChargedFourierGaussianMoments.density S (conj S) 0 0
        z.1.1 (z.1.2 0) z.2 := by
  rw [KFCausalChargedFourierGaussianMoments.density_expansion]
  simp only [pow_zero,one_mul,zero_mul,add_zero]
  unfold pairDensity KFCausalGaussianSourcePlaneKernel.density neutralWeight
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
  linear_combination (potential (z.1.2 1+L*z.1.2 0):ℂ)*hh

#print axioms pair_integrable
#print axioms pair_integral
#print axioms pair_factor
end
end UnifiedTheory.Audit.KFCausalCommonRealGaussianFieldKernel

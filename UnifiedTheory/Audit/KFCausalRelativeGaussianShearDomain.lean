/- Bounded relative complex scale and physical quadratic moments suffice
for the actual shear graph of a C1 Gaussian profile. This handles the
clock-dependent transverse packet without a clock-derivative L2 premise. -/
import UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalRelativeGaussianShearDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments (widths)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalShearPolynomialMoments
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential

variable (r : ℝ → ℂ) (hr : Continuous r) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ s, ‖r s‖ ≤ M)
variable (f : Configuration → ℂ) (hf : MemLp f 2 volume)
variable (hq : ∀ i : Fin 5, MemLp (fun x => (x.2 i:ℂ)^2*f x) 2 volume)
include hr hM hb hf hq

theorem direction_memLp (i : Fin 5) :
    MemLp (fun x => direction (r x.1) x.2 i*f x) 2 volume := by
  by_cases hi : i=4
  · subst i
    convert clock_mul_memLp r hr M hM hb _
      ((linear_memLp f hf hq 2).add (linear_memLp f hf hq 3)) using 1
    funext x
    simp only [direction,ite_true,Pi.add_apply]
    ring
  · convert (clock_mul_memLp r hr M hM hb _ (linear_memLp f hf hq i)).const_mul (1/2:ℂ) using 1
    funext x
    simp only [direction,if_neg hi]
    ring

theorem position_direction_memLp (i : Fin 5) :
    MemLp (fun x => position (r x.1) x.2 i*direction (r x.1) x.2 i*f x) 2 volume := by
  by_cases hi : i=4
  · subst i
    have h1 := clock_mul_memLp r hr M hM hb _
      ((mixed_memLp f hf hq 4 2).add (mixed_memLp f hf hq 4 3))
    have h2 := clock_mul_memLp r hr M hM hb _
      (((hq 2).add ((mixed_memLp f hf hq 2 3).const_mul (2:ℂ))).add (hq 3))
    have h3 := clock_mul_memLp r hr M hM hb _ h2
    convert h1.add ((h3.sub h2).const_mul (2:ℂ)) using 1
    funext x
    simp only [position,direction,ite_true,Pi.add_apply,Pi.sub_apply]
    ring
  · convert (clock_mul_memLp r hr M hM hb _
      (clock_mul_memLp r hr M hM hb _ (hq i))).const_mul (1/2:ℂ) using 1
    funext x
    simp only [position,direction,if_neg hi]
    ring

theorem slope_memLp (α β : ℝ) (b : Fin 5 → ℂ) :
    MemLp (fun x => KFCausalRelativeGaussianDifferential.slope r α β b x*f x) 2 volume := by
  simp only [KFCausalRelativeGaussianDifferential.slope,Finset.sum_mul]
  apply memLp_finset_sum
  intro i _
  convert ((direction_memLp r hr M hM hb f hf hq i).const_mul (b i)).sub
    ((position_direction_memLp r hr M hM hb f hf hq i).const_mul (2*(widths α β i:ℂ))) using 1
  funext x
  simp only [Pi.sub_apply]
  ring

omit hf hq
theorem profile_shear_memLp (A : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hs : ContDiff ℝ 1 r)
    (α β : ℝ) (b : Fin 5 → ℂ) (hp : MemLp (profile A r α β b) 2 volume)
    (hq' : ∀ i : Fin 5, MemLp (fun x => (x.2 i:ℂ)^2*profile A r α β b x) 2 volume) :
    MemLp (shearDerivative (profile A r α β b)) 2 volume := by
  rw [funext (profile_shear A r hA hs α β b)]
  exact (slope_memLp r hr M hM hb _ hp hq' α β b).add hp

theorem profile_graph (h : ℝ) (hh : h ≠ 0) (A : ℝ → ℂ) (hA : ContDiff ℝ 1 A)
    (hs : ContDiff ℝ 1 r) (α β : ℝ) (b : Fin 5 → ℂ)
    (hp : MemLp (profile A r α β b) 2 volume)
    (hq' : ∀ i : Fin 5, MemLp (fun x => (x.2 i:ℂ)^2*profile A r α β b x) 2 volume) :
    (hp.toLp (profile A r α β b),(-Complex.I*(h:ℂ)) •
      (profile_shear_memLp r hr M hM hb A hA hs α β b hp hq').toLp
        (shearDerivative (profile A r α β b))) ∈ (shearMomentum h).graph :=
  KFCausalShearMaximalDifferential.graph_of_shear_differential h hh _
    (profile_smooth A r hA hs α β b) hp (profile_shear_memLp r hr M hM hb A hA hs α β b hp hq')

#print axioms direction_memLp
#print axioms position_direction_memLp
#print axioms slope_memLp
#print axioms profile_shear_memLp
#print axioms profile_graph
end
end UnifiedTheory.Audit.KFCausalRelativeGaussianShearDomain

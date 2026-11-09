/- Transverse diagonal Gaussian products and their first coordinate moments.
These estimates concern the actual physical Gaussian, with independent
positive charged and neutral widths. -/
import UnifiedTheory.Audit.KFCausalChargeGaussianIdentities

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalChargeGaussianProducts (pi_product_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalGaussianSliceDomain

theorem scalar_moment_memLp (b : ℝ) (hb : 0 < b) :
    MemLp (fun x : ℝ => (x:ℂ)*gaussian (b:ℂ) x) 2 volume := by
  have hc : Continuous (fun x : ℝ => (x:ℂ)*gaussian (b:ℂ) x) := by
    exact Complex.continuous_ofReal.mul (gaussian_continuous _)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hi := integrable_rpow_mul_exp_neg_mul_sq (by positivity : 0 < 2*b)
    (by norm_num : (-1:ℝ) < 2)
  simpa only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    gaussian_norm_square,Complex.ofReal_re,Real.rpow_two] using hi

def widths (α β : ℝ) : Fin 5 → ℝ := ![α,α,α,α,β]

theorem widths_positive (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (i : Fin 5) :
    0 < widths α β i := by
  fin_cases i <;> first | exact hα | exact hβ

theorem physicalGaussian_product (α β : ℝ) (x : Transverse) :
    physicalGaussian α β x = ∏ i : Fin 5, gaussian (widths α β i:ℂ) (x i) := by
  simp only [physicalGaussian,widths,Fin.sum_univ_succ,Fin.prod_univ_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,Fin.prod_univ_zero,
    mul_one,add_zero,gaussian]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem physicalGaussian_continuous (α β : ℝ) : Continuous (physicalGaussian α β) := by
  unfold physicalGaussian
  fun_prop

theorem physicalGaussian_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    MemLp (physicalGaussian α β) 2 volume := by
  have he : physicalGaussian α β = fun x : Transverse =>
      ∏ i : Fin 5, gaussian (widths α β i:ℂ) (x i) := funext (physicalGaussian_product α β)
  rw [he]
  exact pi_product_memLp 5 _ (fun _ => gaussian_continuous _)
    (fun i => (gaussian_memLp_iff _).mpr (widths_positive α β hα hβ i))

theorem physicalGaussian_coordinate_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (i : Fin 5) : MemLp (fun x : Transverse => (x i:ℂ)*physicalGaussian α β x) 2 volume := by
  let f : Fin 5 → ℝ → ℂ := fun j t =>
    (if j=i then (t:ℂ) else 1)*gaussian (widths α β j:ℂ) t
  have hc : ∀ j, Continuous (f j) := by
    intro j
    by_cases h : j=i
    · simpa only [f,if_pos h] using Complex.continuous_ofReal.mul (gaussian_continuous (widths α β j:ℂ))
    · simpa only [f,if_neg h,one_mul] using gaussian_continuous (widths α β j:ℂ)
  have hm : ∀ j, MemLp (f j) 2 volume := by
    intro j
    by_cases h : j=i
    · simpa only [f,if_pos h] using scalar_moment_memLp (widths α β j) (widths_positive α β hα hβ j)
    · simpa only [f,if_neg h,one_mul] using
        (gaussian_memLp_iff (widths α β j:ℂ)).mpr (widths_positive α β hα hβ j)
  have he : (fun x : Transverse => (x i:ℂ)*physicalGaussian α β x) =
      fun x : Transverse => ∏ j, f j (x j) := by
    funext x
    simp only [f,Finset.prod_mul_distrib,physicalGaussian_product]
    simp
  rw [he]
  exact pi_product_memLp 5 f hc hm

#print axioms scalar_moment_memLp
#print axioms widths_positive
#print axioms physicalGaussian_product
#print axioms physicalGaussian_continuous
#print axioms physicalGaussian_memLp
#print axioms physicalGaussian_coordinate_memLp

end
end UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments

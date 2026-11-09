/- Quadratic transverse moments of the sourced Gaussian packets used by
actual energy states. These supply the variable-velocity shear derivative,
whose coefficients are linear functions of position. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalGaussianQuadraticMoments
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments
open UnifiedTheory.Audit.KFCausalGaussianSliceDomain
open UnifiedTheory.Audit.KFCausalChargeGaussianProducts (pi_product_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMoments
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (sourceConstant)

theorem scalar_quadratic_memLp (b : ℝ) (hb : 0 < b) :
    MemLp (fun x : ℝ => (x:ℂ)^2*gaussian (b:ℂ) x) 2 volume := by
  have hc : Continuous (fun x : ℝ => (x:ℂ)^2*gaussian (b:ℂ) x) := by
    exact (Complex.continuous_ofReal.pow 2).mul (gaussian_continuous _)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hi := integrable_rpow_mul_exp_neg_mul_sq (by positivity : 0 < 2*b)
    (by norm_num : (-1:ℝ) < (4:ℝ))
  have he (x : ℝ) : ‖(x:ℂ)^2*gaussian (b:ℂ) x‖^2 = x^4*Real.exp (-(2*b)*x^2) := by
    simp only [norm_mul,mul_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      sq_abs,gaussian_norm_square,Complex.ofReal_re]
    ring
  simpa only [he,show (4:ℝ) = ((4:ℕ):ℝ) from rfl,Real.rpow_natCast] using hi

theorem gaussian_quadratic_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (i : Fin 5) :
    MemLp (fun x : Transverse => (x i:ℂ)^2*physicalGaussian α β x) 2 volume := by
  let f : Fin 5 → ℝ → ℂ := fun j t =>
    (if j=i then (t:ℂ)^2 else 1)*gaussian (widths α β j:ℂ) t
  have hc : ∀ j, Continuous (f j) := by
    intro j
    by_cases h : j=i
    · simpa only [f,if_pos h] using (Complex.continuous_ofReal.pow 2).mul (gaussian_continuous (widths α β j:ℂ))
    · simpa only [f,if_neg h,one_mul] using gaussian_continuous (widths α β j:ℂ)
  have hm : ∀ j, MemLp (f j) 2 volume := by
    intro j
    by_cases h : j=i
    · simpa only [f,if_pos h] using scalar_quadratic_memLp (widths α β j) (widths_positive α β hα hβ j)
    · simpa only [f,if_neg h,one_mul] using
        (gaussian_memLp_iff (widths α β j:ℂ)).mpr (widths_positive α β hα hβ j)
  have he : (fun x : Transverse => (x i:ℂ)^2*physicalGaussian α β x) =
      fun x : Transverse => ∏ j, f j (x j) := by
    funext x
    simp only [f,Finset.prod_mul_distrib,physicalGaussian_product]
    simp
  rw [he]
  exact pi_product_memLp 5 f hc hm

theorem sourced_quadratic_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (i : Fin 5) :
    MemLp (fun x : Transverse => (x i:ℂ)^2*sourcedPacket α β b x) 2 volume := by
  have hc : Continuous (fun x : Transverse => (x i:ℂ)^2*sourcedPacket α β b x) :=
    ((Complex.continuous_ofReal.comp (continuous_apply i)).pow 2).mul (sourcedPacket_continuous α β b)
  apply ((gaussian_quadratic_memLp (α/2) (β/2) (by positivity) (by positivity) i).const_mul
    (Real.exp (sourceConstant α β b/2):ℂ)).of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  have h := mul_le_mul_of_nonneg_left (sourcedPacket_bound α β hα hβ hw b x) (norm_nonneg ((x i:ℂ)^2))
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_left_comm] using h

theorem sourced_mixed_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (i j : Fin 5) :
    MemLp (fun x : Transverse => (x i:ℂ)*(x j:ℂ)*sourcedPacket α β b x) 2 volume := by
  have hc : Continuous (fun x : Transverse => (x i:ℂ)*(x j:ℂ)*sourcedPacket α β b x) :=
    ((Complex.continuous_ofReal.comp (continuous_apply i)).mul
      (Complex.continuous_ofReal.comp (continuous_apply j))).mul (sourcedPacket_continuous α β b)
  apply ((sourced_quadratic_memLp α β hα hβ hw b i).add
    (sourced_quadratic_memLp α β hα hβ hw b j)).of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  change ‖(x i:ℂ)*(x j:ℂ)*sourcedPacket α β b x‖ ≤
    ‖(x i:ℂ)^2*sourcedPacket α β b x+(x j:ℂ)^2*sourcedPacket α β b x‖
  rw [← add_mul]
  have he : ((x i:ℂ)^2+(x j:ℂ)^2) = ((x i^2+x j^2:ℝ):ℂ) := by push_cast; rfl
  rw [he]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (sq_nonneg (x i)) (sq_nonneg (x j)))]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  nlinarith [sq_nonneg (|x i|-|x j|),sq_abs (x i),sq_abs (x j)]

#print axioms scalar_quadratic_memLp
#print axioms gaussian_quadratic_memLp
#print axioms sourced_quadratic_memLp
#print axioms sourced_mixed_memLp
end
end UnifiedTheory.Audit.KFCausalGaussianQuadraticMoments

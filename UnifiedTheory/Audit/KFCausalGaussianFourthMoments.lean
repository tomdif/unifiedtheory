/- Fourth coordinate moments of the physical Gaussian and of the proved
imaginary-shear envelope. Their L2 estimates use eighth scalar Gaussian
moments, not an extra moment assumption on the actual path. -/
import UnifiedTheory.Audit.KFCausalShearRadius

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace UnifiedTheory.Audit.KFCausalGaussianFourthMoments
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments
open UnifiedTheory.Audit.KFCausalGaussianSliceDomain
open UnifiedTheory.Audit.KFCausalChargeGaussianProducts (pi_product_memLp)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds
open UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative (configuration_product_memLp)
open UnifiedTheory.Audit.KFCausalShearRadius

theorem scalar_fourth_memLp (b : ℝ) (hb : 0 < b) :
    MemLp (fun x : ℝ => (x:ℂ)^4*gaussian (b:ℂ) x) 2 volume := by
  have hc : Continuous (fun x : ℝ => (x:ℂ)^4*gaussian (b:ℂ) x) :=
    (Complex.continuous_ofReal.pow 4).mul (gaussian_continuous _)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hi := integrable_rpow_mul_exp_neg_mul_sq (by positivity : 0 < 2*b)
    (by norm_num : (-1:ℝ) < (8:ℝ))
  have he (x : ℝ) : ‖(x:ℂ)^4*gaussian (b:ℂ) x‖^2 = x^8*Real.exp (-(2*b)*x^2) := by
    simp only [norm_mul,mul_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      gaussian_norm_square,Complex.ofReal_re]
    rw [← pow_mul,show 4*2=2*4 from rfl,pow_mul,sq_abs]
    ring
  simpa only [he,show (8:ℝ) = ((8:ℕ):ℝ) from rfl,Real.rpow_natCast] using hi

theorem gaussian_fourth_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (i : Fin 5) :
    MemLp (fun x : Transverse => (x i:ℂ)^4*physicalGaussian α β x) 2 volume := by
  let f : Fin 5 → ℝ → ℂ := fun j t =>
    (if j=i then (t:ℂ)^4 else 1)*gaussian (widths α β j:ℂ) t
  have hc : ∀ j, Continuous (f j) := by
    intro j
    by_cases h : j=i
    · simpa only [f,if_pos h] using (Complex.continuous_ofReal.pow 4).mul (gaussian_continuous (widths α β j:ℂ))
    · simpa only [f,if_neg h,one_mul] using gaussian_continuous (widths α β j:ℂ)
  have hm : ∀ j, MemLp (f j) 2 volume := by
    intro j
    by_cases h : j=i
    · simpa only [f,if_pos h] using scalar_fourth_memLp (widths α β j) (widths_positive α β hα hβ j)
    · simpa only [f,if_neg h,one_mul] using
        (gaussian_memLp_iff (widths α β j:ℂ)).mpr (widths_positive α β hα hβ j)
  have he : (fun x : Transverse => (x i:ℂ)^4*physicalGaussian α β x) =
      fun x : Transverse => ∏ j, f j (x j) := by
    funext x
    simp only [f,Finset.prod_mul_distrib,physicalGaussian_product]
    simp
  rw [he]
  exact pi_product_memLp 5 f hc hm

theorem envelope_fourth_memLp (A : ℝ → ℂ) (hA : MemLp A 2 volume) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (b : Fin 5 → ℂ) (i : Fin 5) :
    MemLp (fun x : Configuration => (x.2 i:ℂ)^4*envelope A α β b x) 2 volume := by
  convert (configuration_product_memLp A _ hA
    (gaussian_fourth_memLp _ _ (width_positive α β hα hβ) (width_positive α β hα hβ) i)).const_mul
      (constant α β b:ℂ) using 1
  funext x
  unfold envelope
  ring

theorem radius_memLp (f : Configuration → ℂ) (hf : MemLp f 2 volume)
    (hq : ∀ i : Fin 5, MemLp (fun x => (x.2 i:ℂ)^2*f x) 2 volume) :
    MemLp (fun x => (radius x.2:ℂ)*f x) 2 volume := by
  have hm := hf.add (memLp_finset_sum Finset.univ (fun i _ => hq i))
  convert hm using 1
  funext x
  simp [radius,add_mul,Finset.sum_mul,Complex.ofReal_sum]

theorem fourth_memLp (f : Configuration → ℂ) (hf : MemLp f 2 volume)
    (hq : ∀ i : Fin 5, MemLp (fun x => (x.2 i:ℂ)^4*f x) 2 volume) :
    MemLp (fun x => (fourth x.2:ℂ)*f x) 2 volume := by
  have hm := hf.add (memLp_finset_sum Finset.univ (fun i _ => hq i))
  convert hm using 1
  funext x
  simp [fourth,add_mul,Finset.sum_mul,Complex.ofReal_sum]

theorem radius_square_memLp (f : Configuration → ℂ) (hf : MemLp f 2 volume)
    (hq : ∀ i : Fin 5, MemLp (fun x => (x.2 i:ℂ)^4*f x) 2 volume) :
    MemLp (fun x => ((radius x.2)^2:ℝ)*f x) 2 volume := by
  have hc : Continuous (fun x : Configuration => (((radius x.2)^2:ℝ):ℂ)) := by
    unfold radius
    fun_prop
  apply ((fourth_memLp f hf hq).const_mul (10:ℂ)).of_le
    (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with x
  have hfour : 0 ≤ fourth x.2 := by unfold fourth; positivity
  simpa only [Pi.mul_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (radius x.2)),
    abs_of_nonneg hfour,Complex.norm_ofNat,mul_assoc] using
      mul_le_mul_of_nonneg_right (radius_square_le_fourth x.2) (norm_nonneg (f x))

#print axioms scalar_fourth_memLp
#print axioms gaussian_fourth_memLp
#print axioms envelope_fourth_memLp
#print axioms radius_memLp
#print axioms fourth_memLp
#print axioms radius_square_memLp
end
end UnifiedTheory.Audit.KFCausalGaussianFourthMoments

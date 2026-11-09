/- The partial Fourier integral of a continuous joint L1/L2 function is
measurable and belongs to joint L2. Slice integrability and the exact norm
identity follow from Fubini and the actual L2 Fourier isometry. No product
factorization or assumed integrability of the transform is required. -/
import UnifiedTheory.Audit.KFCausalPartialFourier
import UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalPartialFourierSlices
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalL2FourierIntegral
open UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy (toLp_square_integral)

variable (n m : ℕ)

def leftIntegral (f : Block n × Block m → ℂ) (w : Block n × Block m) : ℂ :=
  (𝓕 (fun x : Block n => f (x,w.2))) w.1

theorem leftIntegral_measurable (f : Block n × Block m → ℂ) (hc : Continuous f) :
    AEStronglyMeasurable (leftIntegral n m f) volume := by
  have hcont : Continuous (fun u : (Block n × Block m) × Block n =>
      (Real.fourierChar (-inner ℝ u.2 u.1.1):ℂ)*f (u.2,u.1.2)) := by
    fun_prop
  have hm : AEStronglyMeasurable (fun u : (Block n × Block m) × Block n =>
      (Real.fourierChar (-inner ℝ u.2 u.1.1):ℂ)*f (u.2,u.1.2))
      ((volume : Measure (Block n × Block m)).prod (volume : Measure (Block n))) := hcont.aestronglyMeasurable
  exact hm.integral_prod_right'

theorem slice_memLp (f : Block n × Block m → ℂ) (hf : MemLp f 2) :
    ∀ᵐ y ∂(volume : Measure (Block m)), MemLp (fun x : Block n => f (x,y)) 2 := by
  have hi := (memLp_two_iff_integrable_sq_norm hf.1).mp hf
  rw [Measure.volume_eq_prod (Block n) (Block m)] at hi hf
  filter_upwards [hi.prod_left_ae,hf.1.prodMk_right] with y hy hm
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hy

theorem fourier_square (f : Block n → ℂ) (h1 : Integrable f) (h2 : MemLp f 2) :
    (∫ x : Block n, ‖(𝓕 f) x‖^2) = ∫ x : Block n, ‖f x‖^2 := by
  rw [← toLp_square_integral _ (integralFourier_memLp f h1 h2),← fourier_toLp_eq f h1 h2,
    LinearIsometryEquiv.norm_map,toLp_square_integral]

theorem slice_plancherel (f : Block n × Block m → ℂ) (h1 : Integrable f) (h2 : MemLp f 2) :
    ∀ᵐ y ∂(volume : Measure (Block m)),
      (∫ x : Block n, ‖leftIntegral n m f (x,y)‖^2) = ∫ x : Block n, ‖f (x,y)‖^2 := by
  rw [Measure.volume_eq_prod (Block n) (Block m)] at h1
  filter_upwards [h1.prod_left_ae,slice_memLp n m f h2] with y hy hm
  exact fourier_square n _ hy hm

theorem leftIntegral_memLp (f : Block n × Block m → ℂ) (hc : Continuous f)
    (h1 : Integrable f) (h2 : MemLp f 2) : MemLp (leftIntegral n m f) 2 := by
  have hm := leftIntegral_measurable n m f hc
  have hi := (memLp_two_iff_integrable_sq_norm h2.1).mp h2
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  rw [Measure.volume_eq_prod (Block n) (Block m)] at hi h1 hm ⊢
  apply (integrable_prod_iff' (hm.norm.pow 2)).mpr
  constructor
  · filter_upwards [h1.prod_left_ae,slice_memLp n m f h2] with y hy hs
    have ht := integralFourier_memLp _ hy hs
    exact (memLp_two_iff_integrable_sq_norm ht.1).mp ht
  · apply hi.integral_norm_prod_right.congr
    filter_upwards [slice_plancherel n m f h1 h2] with y hy
    simp only [Pi.pow_apply,Real.norm_eq_abs,abs_sq]
    exact hy.symm

theorem leftIntegral_square (f : Block n × Block m → ℂ) (hc : Continuous f)
    (h1 : Integrable f) (h2 : MemLp f 2) :
    (∫ w : Block n × Block m, ‖leftIntegral n m f w‖^2) =
      ∫ w : Block n × Block m, ‖f w‖^2 := by
  have ht := leftIntegral_memLp n m f hc h1 h2
  have hi := (memLp_two_iff_integrable_sq_norm h2.1).mp h2
  have hj := (memLp_two_iff_integrable_sq_norm ht.1).mp ht
  rw [Measure.volume_eq_prod (Block n) (Block m)] at hi hj ⊢
  rw [integral_prod_symm _ hj,integral_prod_symm _ hi]
  exact integral_congr_ae (slice_plancherel n m f h1 h2)

#print axioms leftIntegral_measurable
#print axioms slice_memLp
#print axioms fourier_square
#print axioms slice_plancherel
#print axioms leftIntegral_memLp
#print axioms leftIntegral_square

end
end UnifiedTheory.Audit.KFCausalPartialFourierSlices

/- Identification of the actual partial Fourier unitary for joint L2
functions whose slices are L1. No joint L1 or continuity is required. -/
import UnifiedTheory.Audit.KFCausalPartialFourierIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalPartialFourierIntegrableSlices
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalPartialFourier
open UnifiedTheory.Audit.KFCausalPartialFourierSlices
open UnifiedTheory.Audit.KFCausalPartialFourierIntegral (product_pairing fourier_pairing)
open UnifiedTheory.Audit.KFCausalL2FourierIntegral (integralFourier_memLp)
open UnifiedTheory.Audit.KFCausalEuclideanTensorDensity (zero_of_orthogonal_products)

variable (n m : ℕ)

theorem integral_measurable (f : Block n × Block m → ℂ) (hf : Measurable f) :
    AEStronglyMeasurable (leftIntegral n m f) volume := by
  have hm : Measurable (fun u : (Block n × Block m) × Block n =>
      (Real.fourierChar (-inner ℝ u.2 u.1.1) : ℂ) * f (u.2,u.1.2)) := by
    apply Measurable.mul
    · fun_prop
    · exact hf.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  exact hm.aestronglyMeasurable.integral_prod_right'

theorem integral_memLp (f : Block n × Block m → ℂ) (hm : Measurable f)
    (h1 : ∀ᵐ y ∂(volume : Measure (Block m)), Integrable (fun x => f (x,y)))
    (h2 : MemLp f 2) : MemLp (leftIntegral n m f) 2 := by
  have ht := integral_measurable n m f hm
  have hi := (memLp_two_iff_integrable_sq_norm h2.1).mp h2
  have hs := slice_memLp n m f h2
  apply (memLp_two_iff_integrable_sq_norm ht).mpr
  rw [Measure.volume_eq_prod (Block n) (Block m)] at hi ht ⊢
  apply (integrable_prod_iff' (ht.norm.pow 2)).mpr
  constructor
  · filter_upwards [h1,hs] with y hy hz
    exact (memLp_two_iff_integrable_sq_norm (integralFourier_memLp _ hy hz).1).mp
      (integralFourier_memLp _ hy hz)
  · apply hi.integral_norm_prod_right.congr
    filter_upwards [h1,hs] with y hy hz
    simp only [Pi.pow_apply,Real.norm_eq_abs,abs_sq]
    exact (fourier_square n (fun x => f (x,y)) hy hz).symm

theorem unitary_toLp_eq (f : Block n × Block m → ℂ) (hm : Measurable f)
    (h1 : ∀ᵐ y ∂(volume : Measure (Block m)), Integrable (fun x => f (x,y)))
    (h2 : MemLp f 2) :
    leftFourier n m (h2.toLp f) =
      (integral_memLp n m f hm h1 h2).toLp (leftIntegral n m f) := by
  have hp (a : BlockHilbert n) (b : BlockHilbert m) :
      inner ℂ (productState volume volume ((Lp.fourierTransformₗᵢ (Block n) ℂ) a) b)
          ((integral_memLp n m f hm h1 h2).toLp (leftIntegral n m f)) =
        inner ℂ (productState volume volume a b) (h2.toLp f) := by
    rw [product_pairing,product_pairing]
    apply integral_congr_ae
    filter_upwards [h1,slice_memLp n m f h2] with y hy hs
    exact congrArg (fun z : ℂ => (starRingEnd ℂ) (b y)*z)
      (fourier_pairing n (fun x => f (x,y)) hy hs a)
  apply sub_eq_zero.mp
  apply zero_of_orthogonal_products n m
  intro a b
  rw [inner_sub_right,sub_eq_zero]
  let a' := (Lp.fourierTransformₗᵢ (Block n) ℂ).symm a
  have he : (Lp.fourierTransformₗᵢ (Block n) ℂ) a' = a :=
    (Lp.fourierTransformₗᵢ (Block n) ℂ).apply_symm_apply a
  have hu := (leftFourier n m).inner_map_map (productState volume volume a' b) (h2.toLp f)
  rw [leftFourier_product,he] at hu
  have hv := hp a' b
  rw [he] at hv
  exact hu.trans hv.symm

theorem unitary_toLp_coe (f : Block n × Block m → ℂ) (hm : Measurable f)
    (h1 : ∀ᵐ y ∂(volume : Measure (Block m)), Integrable (fun x => f (x,y)))
    (h2 : MemLp f 2) :
    leftFourier n m (h2.toLp f) =ᵐ[volume] leftIntegral n m f := by
  rw [unitary_toLp_eq n m f hm h1 h2]
  exact (integral_memLp n m f hm h1 h2).coeFn_toLp

#print axioms integral_measurable
#print axioms integral_memLp
#print axioms unitary_toLp_eq
#print axioms unitary_toLp_coe

end
end UnifiedTheory.Audit.KFCausalPartialFourierIntegrableSlices

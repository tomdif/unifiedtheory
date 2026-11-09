/- The actual partial L2 Fourier unitary agrees with the partial Fourier
integral on every continuous joint L1/L2 function. The transformed function's
joint L2 membership is proved, and testing against all product L2 vectors
identifies the unitary using the established tensor-density theorem. -/
import UnifiedTheory.Audit.KFCausalPartialFourierSlices

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalPartialFourierIntegral
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalEuclideanTensorDensity (zero_of_orthogonal_products)
open UnifiedTheory.Audit.KFCausalPartialFourier
open UnifiedTheory.Audit.KFCausalPartialFourierSlices
open UnifiedTheory.Audit.KFCausalL2FourierIntegral (fourier_toLp_coe)

variable (n m : ℕ)

theorem product_pairing (f : Block n × Block m → ℂ) (hf : MemLp f 2)
    (a : BlockHilbert n) (b : BlockHilbert m) :
    inner ℂ (productState volume volume a b) (hf.toLp f) =
      ∫ y : Block m, (starRingEnd ℂ) (b y)*(∫ x : Block n, (starRingEnd ℂ) (a x)*f (x,y)) := by
  have hi : Integrable (fun w : Block n × Block m => (starRingEnd ℂ) (a w.1*b w.2)*f w) := by
    apply (L2.integrable_inner (𝕜 := ℂ) (productState volume volume a b) (hf.toLp f)).congr
    filter_upwards [productState_coe volume volume a b,hf.coeFn_toLp] with w hp hf'
    rw [hp,hf',RCLike.inner_apply']
  calc
    _ = ∫ w : Block n × Block m, (starRingEnd ℂ) (a w.1*b w.2)*f w := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [productState_coe volume volume a b,hf.coeFn_toLp] with w hp hf'
      rw [hp,hf',RCLike.inner_apply']
    _ = ∫ y : Block m, ∫ x : Block n, (starRingEnd ℂ) (a x*b y)*f (x,y) := integral_prod_symm _ hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [map_mul]
      ring

theorem fourier_pairing (f : Block n → ℂ) (h1 : Integrable f) (h2 : MemLp f 2)
    (a : BlockHilbert n) :
    (∫ x : Block n, (starRingEnd ℂ) ((Lp.fourierTransformₗᵢ (Block n) ℂ) a x)*(𝓕 f) x) =
      ∫ x : Block n, (starRingEnd ℂ) (a x)*f x := by
  calc
    _ = inner ℂ ((Lp.fourierTransformₗᵢ (Block n) ℂ) a)
        ((Lp.fourierTransformₗᵢ (Block n) ℂ) (h2.toLp f)) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [fourier_toLp_coe f h1 h2] with x hx
      rw [hx,RCLike.inner_apply']
    _ = inner ℂ a (h2.toLp f) := (Lp.fourierTransformₗᵢ (Block n) ℂ).inner_map_map _ _
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp] with x hx
      rw [hx,RCLike.inner_apply']

theorem leftIntegral_pairing (f : Block n × Block m → ℂ) (hc : Continuous f)
    (h1 : Integrable f) (h2 : MemLp f 2) (a : BlockHilbert n) (b : BlockHilbert m) :
    inner ℂ (productState volume volume ((Lp.fourierTransformₗᵢ (Block n) ℂ) a) b)
        ((leftIntegral_memLp n m f hc h1 h2).toLp (leftIntegral n m f)) =
      inner ℂ (productState volume volume a b) (h2.toLp f) := by
  rw [product_pairing,product_pairing]
  apply integral_congr_ae
  rw [Measure.volume_eq_prod (Block n) (Block m)] at h1
  filter_upwards [h1.prod_left_ae,slice_memLp n m f h2] with y hy hs
  exact congrArg (fun z : ℂ => (starRingEnd ℂ) (b y)*z) (fourier_pairing n (fun x => f (x,y)) hy hs a)

theorem leftFourier_toLp_eq (f : Block n × Block m → ℂ) (hc : Continuous f)
    (h1 : Integrable f) (h2 : MemLp f 2) :
    leftFourier n m (h2.toLp f) =
      (leftIntegral_memLp n m f hc h1 h2).toLp (leftIntegral n m f) := by
  apply sub_eq_zero.mp
  apply zero_of_orthogonal_products n m
  intro a b
  rw [inner_sub_right,sub_eq_zero]
  let a' := (Lp.fourierTransformₗᵢ (Block n) ℂ).symm a
  have hinner := (leftFourier n m).inner_map_map (productState volume volume a' b) (h2.toLp f)
  rw [leftFourier_product,show (Lp.fourierTransformₗᵢ (Block n) ℂ) a' = a from
    (Lp.fourierTransformₗᵢ (Block n) ℂ).apply_symm_apply a] at hinner
  have he := leftIntegral_pairing n m f hc h1 h2 a' b
  rw [show (Lp.fourierTransformₗᵢ (Block n) ℂ) a' = a from
    (Lp.fourierTransformₗᵢ (Block n) ℂ).apply_symm_apply a] at he
  exact hinner.trans he.symm

theorem leftFourier_toLp_coe (f : Block n × Block m → ℂ) (hc : Continuous f)
    (h1 : Integrable f) (h2 : MemLp f 2) :
    leftFourier n m (h2.toLp f) =ᵐ[volume] leftIntegral n m f := by
  rw [leftFourier_toLp_eq n m f hc h1 h2]
  exact (leftIntegral_memLp n m f hc h1 h2).coeFn_toLp

#print axioms product_pairing
#print axioms fourier_pairing
#print axioms leftIntegral_pairing
#print axioms leftFourier_toLp_eq
#print axioms leftFourier_toLp_coe

end
end UnifiedTheory.Audit.KFCausalPartialFourierIntegral

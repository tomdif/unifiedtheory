/- The existing unitary partial Fourier transform agrees with the slice
Fourier integral for general, nonseparable L2 profiles. Fiber L2 facts and
Fubini integrability are derived, not assumed operator identifications. -/
import UnifiedTheory.Audit.KFCausalPartialFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalPartialFourierFiberFormula
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalEuclideanProductCoordinates
open KFCausalL2TensorEmbedding
open KFCausalPartialFourier

variable (n m : ℕ)

def sliceFourier (F : Block n × Block m → ℂ) (z : Block n × Block m) : ℂ :=
  (𝓕 (fun x => F (x,z.2))) z.1

theorem slices_memLp (F : Block n × Block m → ℂ) (hF : MemLp F 2 volume) :
    ∀ᵐ y ∂volume, MemLp (fun x => F (x,y)) 2 volume := by
  have hi := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  filter_upwards [hF.aestronglyMeasurable.prodMk_right,hi.prod_left_ae] with y hm hy
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hy

theorem inner_toLp (f : BlockHilbert n) (F : Block n → ℂ) (hF : MemLp F 2 volume) :
    inner ℂ f (hF.toLp F) = ∫ x, star (f x)*F x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with x hx
  simp only [hx,RCLike.inner_apply']
  rfl

theorem product_test_pairing (f : BlockHilbert n) (g : BlockHilbert m)
    (F : Block n × Block m → ℂ) (hF : MemLp F 2 volume) :
    inner ℂ (productState volume volume f g) (hF.toLp F) =
      ∫ y, star (g y)*(∫ x, star (f x)*F (x,y)) := by
  have hi := (product_memLp volume volume f g (Lp.memLp f) (Lp.memLp g)).star.integrable_mul hF
  calc
    _ = ∫ z, star (f z.1*g z.2)*F z := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [productState_coe volume volume f g,hF.coeFn_toLp] with z hz hFz
      simp only [hz,hFz,RCLike.inner_apply']
      rfl
    _ = ∫ y, ∫ x, star (f x*g y)*F (x,y) := integral_prod_symm _ hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [star_mul]
      ring

theorem slice_test_pairing (f : BlockHilbert n) (F : Block n → ℂ)
    (hF1 : Integrable F) (hF2 : MemLp F 2 volume) :
    (∫ x, star (((Lp.fourierTransformₗᵢ (Block n) ℂ) f) x)*(𝓕 F) x) =
      ∫ x, star (f x)*F x := by
  have he := (Lp.fourierTransformₗᵢ (Block n) ℂ).inner_map_map f (hF2.toLp F)
  rw [KFCausalL2FourierIntegral.fourier_toLp_eq F hF1 hF2,
    inner_toLp,inner_toLp] at he
  exact he

theorem fourier_product_pairing (f : BlockHilbert n) (g : BlockHilbert m)
    (F : Block n × Block m → ℂ) (hF : MemLp F 2 volume)
    (hF1 : ∀ᵐ y ∂volume, Integrable (fun x => F (x,y)))
    (hG : MemLp (sliceFourier n m F) 2 volume) :
    inner ℂ (productState volume volume ((Lp.fourierTransformₗᵢ (Block n) ℂ) f) g)
      (hG.toLp (sliceFourier n m F)) =
        inner ℂ (productState volume volume f g) (hF.toLp F) := by
  rw [product_test_pairing,product_test_pairing]
  apply integral_congr_ae
  filter_upwards [hF1,slices_memLp n m F hF] with y hy hFy
  exact congrArg (star (g y)*·) (slice_test_pairing n f (fun x => F (x,y)) hy hFy)

theorem leftFourier_toLp_eq (F : Block n × Block m → ℂ) (hF : MemLp F 2 volume)
    (hF1 : ∀ᵐ y ∂volume, Integrable (fun x => F (x,y)))
    (hG : MemLp (sliceFourier n m F) 2 volume) :
    leftFourier n m (hF.toLp F) = hG.toLp (sliceFourier n m F) := by
  apply sub_eq_zero.mp
  apply KFCausalEuclideanTensorDensity.zero_of_orthogonal_products n m
  intro f g
  let u := (Lp.fourierTransformₗᵢ (Block n) ℂ).symm f
  have he := (leftFourier n m).inner_map_map (productState volume volume u g) (hF.toLp F)
  rw [leftFourier_product] at he
  have hu : (Lp.fourierTransformₗᵢ (Block n) ℂ) u = f :=
    (Lp.fourierTransformₗᵢ (Block n) ℂ).apply_symm_apply f
  rw [hu] at he
  have hg := fourier_product_pairing n m u g F hF hF1 hG
  rw [hu] at hg
  rw [inner_sub_right,he,hg,sub_self]

theorem leftFourier_toLp_coe (F : Block n × Block m → ℂ) (hF : MemLp F 2 volume)
    (hF1 : ∀ᵐ y ∂volume, Integrable (fun x => F (x,y)))
    (hG : MemLp (sliceFourier n m F) 2 volume) :
    leftFourier n m (hF.toLp F) =ᵐ[volume] sliceFourier n m F := by
  rw [leftFourier_toLp_eq n m F hF hF1 hG]
  exact hG.coeFn_toLp

#print axioms slices_memLp
#print axioms inner_toLp
#print axioms product_test_pairing
#print axioms slice_test_pairing
#print axioms fourier_product_pairing
#print axioms leftFourier_toLp_eq
#print axioms leftFourier_toLp_coe
end
end UnifiedTheory.Audit.KFCausalPartialFourierFiberFormula

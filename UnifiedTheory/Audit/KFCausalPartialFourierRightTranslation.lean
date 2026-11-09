/- Translation in the untransformed block commutes with the actual
partial Fourier transform on all L2 vectors, by tensor density. -/
import UnifiedTheory.Audit.KFCausalPartialFourierTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalPartialFourierRightTranslation
noncomputable section
open MeasureTheory MeasureTheory.Measure
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanTensorUnitary
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback
open UnifiedTheory.Audit.KFCausalFourierTranslation
open UnifiedTheory.Audit.KFCausalPartialFourier

variable (n m : ℕ)

def rightShift (v : Block m) : (Block n × Block m) ≃ᵐ (Block n × Block m) :=
  (MeasurableEquiv.refl _).prodCongr (shift v)

theorem rightShift_preserves (v : Block m) : MeasurePreserving (rightShift n m v) :=
  (MeasurePreserving.id volume).prod (shift_preserves_volume v)

def rightTranslation (v : Block m) : ProductHilbert n m ≃ₗᵢ[ℂ] ProductHilbert n m :=
  unitaryPullback (rightShift n m v) (rightShift_preserves n m v)

theorem rightTranslation_coe (v : Block m) (f : ProductHilbert n m) :
    rightTranslation n m v f =ᵐ[volume] fun z => f (z.1,z.2+v) :=
  unitaryPullback_coe _ _ _

theorem rightTranslation_product (v : Block m) (f : BlockHilbert n) (g : BlockHilbert m) :
    rightTranslation n m v (productState volume volume f g) =
      productState volume volume f (translation v g) := by
  apply Lp.ext
  filter_upwards [rightTranslation_coe n m v (productState volume volume f g),
    (rightShift_preserves n m v).quasiMeasurePreserving.ae (productState_coe volume volume f g),
    productState_coe volume volume f (translation v g),
    quasiMeasurePreserving_snd.ae (translation_coe v g)] with z ht hp hq hg
  change (productState volume volume f g) (z.1,z.2+v) = _ at hp
  rw [ht,hp,hq,hg]
  rfl

theorem leftFourier_rightTranslation (v : Block m) (f : ProductHilbert n m) :
    leftFourier n m (rightTranslation n m v f) = rightTranslation n m v (leftFourier n m f) := by
  have he := equal_on_products n m
    ((leftFourier n m : ProductHilbert n m →L[ℂ] ProductHilbert n m).comp
      (rightTranslation n m v : ProductHilbert n m →L[ℂ] ProductHilbert n m))
    ((rightTranslation n m v : ProductHilbert n m →L[ℂ] ProductHilbert n m).comp
      (leftFourier n m : ProductHilbert n m →L[ℂ] ProductHilbert n m)) (by
      intro u w
      change leftFourier n m (rightTranslation n m v (productState volume volume u w)) =
        rightTranslation n m v (leftFourier n m (productState volume volume u w))
      rw [rightTranslation_product,leftFourier_product,leftFourier_product,rightTranslation_product])
  exact congrArg (fun A : ProductHilbert n m →L[ℂ] ProductHilbert n m => A f) he

#print axioms rightShift_preserves
#print axioms rightTranslation_coe
#print axioms rightTranslation_product
#print axioms leftFourier_rightTranslation

end
end UnifiedTheory.Audit.KFCausalPartialFourierRightTranslation

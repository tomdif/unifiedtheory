/- Translation of the first coordinate block is diagonalized by the actual
partial Fourier unitary on every product-L2 state. Tensor density supplies
the extension; no differentiability or factorization premise on the state. -/
import UnifiedTheory.Audit.KFCausalPartialFourier
import UnifiedTheory.Audit.KFCausalFourierTranslation
import UnifiedTheory.Audit.KFCausalContractiveMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalPartialFourierTranslation
noncomputable section
open MeasureTheory MeasureTheory.Measure
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanTensorUnitary
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback
open UnifiedTheory.Audit.KFCausalFourierTranslation
open UnifiedTheory.Audit.KFCausalPartialFourier
open UnifiedTheory.Audit.KFCausalContractiveMultiplier

variable (n m : ℕ)

def leftShift (v : Block n) : (Block n × Block m) ≃ᵐ (Block n × Block m) :=
  (shift v).prodCongr (MeasurableEquiv.refl _)

theorem leftShift_preserves (v : Block n) : MeasurePreserving (leftShift n m v) :=
  (shift_preserves_volume v).prod (MeasurePreserving.id volume)

def leftTranslation (v : Block n) : ProductHilbert n m ≃ₗᵢ[ℂ] ProductHilbert n m :=
  unitaryPullback (leftShift n m v) (leftShift_preserves n m v)

theorem leftTranslation_coe (v : Block n) (f : ProductHilbert n m) :
    leftTranslation n m v f =ᵐ[volume] fun z => f (z.1+v,z.2) :=
  unitaryPullback_coe _ _ _

theorem leftTranslation_product (v : Block n) (f : BlockHilbert n) (g : BlockHilbert m) :
    leftTranslation n m v (productState volume volume f g) =
      productState volume volume (translation v f) g := by
  apply Lp.ext
  filter_upwards [leftTranslation_coe n m v (productState volume volume f g),
    (leftShift_preserves n m v).quasiMeasurePreserving.ae (productState_coe volume volume f g),
    productState_coe volume volume (translation v f) g,
    quasiMeasurePreserving_fst.ae (translation_coe v f)] with z ht hp hq hf
  change (productState volume volume f g) (z.1+v,z.2) = _ at hp
  rw [ht,hp,hq,hf]
  rfl

def leftPhase (v : Block n) : ProductHilbert n m →L[ℂ] ProductHilbert n m :=
  multiplyL (fun z => phase v z.1) ((phase_continuous v).measurable.comp measurable_fst)
    (fun z => (phase_norm v z.1).le)

theorem leftPhase_coe (v : Block n) (f : ProductHilbert n m) :
    leftPhase n m v f =ᵐ[volume] fun z => phase v z.1*f z :=
  multiplyL_coe _ _ _ f

theorem leftPhase_product (v : Block n) (f : BlockHilbert n) (g : BlockHilbert m) :
    leftPhase n m v (productState volume volume f g) =
      productState volume volume (phaseAction v f) g := by
  apply Lp.ext
  filter_upwards [leftPhase_coe n m v (productState volume volume f g),
    productState_coe volume volume f g,productState_coe volume volume (phaseAction v f) g,
    quasiMeasurePreserving_fst.ae (phaseAction_coe v f)] with z hm hp hq hf
  rw [hm,hp,hq,hf,mul_assoc]

theorem leftFourier_translation (v : Block n) (f : ProductHilbert n m) :
    leftFourier n m (leftTranslation n m v f) = leftPhase n m v (leftFourier n m f) := by
  have he := equal_on_products n m
    ((leftFourier n m : ProductHilbert n m →L[ℂ] ProductHilbert n m).comp
      (leftTranslation n m v : ProductHilbert n m →L[ℂ] ProductHilbert n m))
    ((leftPhase n m v).comp (leftFourier n m : ProductHilbert n m →L[ℂ] ProductHilbert n m)) (by
      intro u w
      change leftFourier n m (leftTranslation n m v (productState volume volume u w)) =
        leftPhase n m v (leftFourier n m (productState volume volume u w))
      rw [leftTranslation_product,leftFourier_product,leftFourier_product,leftPhase_product,
        fourier_translation])
  exact congrArg (fun A : ProductHilbert n m →L[ℂ] ProductHilbert n m => A f) he

#print axioms leftShift_preserves
#print axioms leftTranslation_coe
#print axioms leftTranslation_product
#print axioms leftPhase_coe
#print axioms leftPhase_product
#print axioms leftFourier_translation

end
end UnifiedTheory.Audit.KFCausalPartialFourierTranslation

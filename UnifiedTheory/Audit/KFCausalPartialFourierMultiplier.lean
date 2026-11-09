/- A bounded multiplier on the spectator block commutes with the actual
partial Fourier transform on the whole product L2 space. Product-state
identities extend using the previously proved tensor density theorem. -/
import UnifiedTheory.Audit.KFCausalPartialFourier
import UnifiedTheory.Audit.KFCausalContractiveMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPartialFourierMultiplier
noncomputable section
open MeasureTheory MeasureTheory.Measure
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalContractiveMultiplier
open UnifiedTheory.Audit.KFCausalPartialFourier
open UnifiedTheory.Audit.KFCausalEuclideanTensorUnitary

variable (n m : ℕ) (w : Block m → ℂ) (hw : Measurable w)
  (hb : ∀ y, ‖w y‖ ≤ 1)

def rightMultiplier : ProductHilbert n m →L[ℂ] ProductHilbert n m :=
  multiplyL (fun z => w z.2) (hw.comp measurable_snd) (fun z => hb z.2)

theorem rightMultiplier_coe (f : ProductHilbert n m) :
    rightMultiplier n m w hw hb f =ᵐ[volume] fun z => w z.2 * f z :=
  multiplyL_coe _ _ _ f

theorem rightMultiplier_product (f : BlockHilbert n) (g : BlockHilbert m) :
    rightMultiplier n m w hw hb (productState volume volume f g) =
      productState volume volume f (multiplyL w hw hb g) := by
  apply Lp.ext
  filter_upwards [rightMultiplier_coe n m w hw hb (productState volume volume f g),
    productState_coe volume volume f g,
    productState_coe volume volume f (multiplyL w hw hb g),
    quasiMeasurePreserving_snd.ae (multiplyL_coe w hw hb g)] with z hM hp hq hg
  rw [hM,hp,hq,hg]
  ring

theorem leftFourier_commutes (f : ProductHilbert n m) :
    leftFourier n m (rightMultiplier n m w hw hb f) =
      rightMultiplier n m w hw hb (leftFourier n m f) := by
  have he := equal_on_products n m
    ((leftFourier n m : ProductHilbert n m →L[ℂ] ProductHilbert n m).comp
      (rightMultiplier n m w hw hb))
    ((rightMultiplier n m w hw hb).comp
      (leftFourier n m : ProductHilbert n m →L[ℂ] ProductHilbert n m)) (by
        intro u v
        change leftFourier n m (rightMultiplier n m w hw hb (productState volume volume u v)) =
          rightMultiplier n m w hw hb (leftFourier n m (productState volume volume u v))
        rw [rightMultiplier_product,leftFourier_product,leftFourier_product,rightMultiplier_product])
  exact congrArg (fun P : ProductHilbert n m →L[ℂ] ProductHilbert n m => P f) he

#print axioms rightMultiplier_coe
#print axioms rightMultiplier_product
#print axioms leftFourier_commutes

end
end UnifiedTheory.Audit.KFCausalPartialFourierMultiplier

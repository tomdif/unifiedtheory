/- Fourier transformation commutes with joining Euclidean coordinate blocks.
The statement is on the actual L2 unitaries and holds for all product states. -/
import UnifiedTheory.Audit.KFCausalHermiteProductBasis
import UnifiedTheory.Audit.KFCausalFullFourierProduct
import UnifiedTheory.Audit.KFCausalL2FourierIsometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalJoinedFourierProduct
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates
open KFCausalHermiteProductBasis (joinCoordinates mergeIsometry)
open KFCausalL2TensorEmbedding (productState productState_coe)
open KFCausalPartialFourier
open KFCausalFullFourierProduct

def separate (n m : ℕ) : Block (n+m) ≃ᵐ (Block n × Block m) :=
  (mergeIsometry n m).symm.toMeasurableEquiv.trans (split n m)

theorem separate_preserves (n m : ℕ) : MeasurePreserving (separate n m) :=
  (split_preserves_volume n m).comp (mergeIsometry n m).symm.measurePreserving

theorem join_coe (n m : ℕ) (f : ProductHilbert n m) :
    joinCoordinates n m f =ᵐ[volume] f ∘ separate n m := by
  filter_upwards [KFCausalMeasureUnitaryPullback.unitaryPullback_symm_coe
      (mergeIsometry n m).toMeasurableEquiv (mergeIsometry n m).measurePreserving
      (coordinates n m f),
    (mergeIsometry n m).symm.measurePreserving.quasiMeasurePreserving.ae
      (coordinates_coe n m f)] with x hx hy
  exact hx.trans hy

theorem join_product_coe (n m : ℕ) (f : BlockHilbert n) (g : BlockHilbert m) :
    joinCoordinates n m (productState volume volume f g) =ᵐ[volume]
      fun x => f (separate n m x).1*g (separate n m x).2 := by
  filter_upwards [join_coe n m (productState volume volume f g),
    (separate_preserves n m).quasiMeasurePreserving.ae
      (productState_coe volume volume f g)] with x hx hy
  exact hx.trans hy

theorem join_fullFourier (n m : ℕ) (f : ProductHilbert n m) :
    (Lp.fourierTransformₗᵢ (Block (n+m)) ℂ) (joinCoordinates n m f) =
      joinCoordinates n m (fullFourier n m f) := by
  have he := KFCausalL2FourierIsometry.fourier_pullback (mergeIsometry n m).symm
    (coordinates n m f)
  change (Lp.fourierTransformₗᵢ (Block (n+m)) ℂ)
    ((KFCausalMeasureUnitaryPullback.unitaryPullback
      (mergeIsometry n m).toMeasurableEquiv (mergeIsometry n m).measurePreserving).symm
      (coordinates n m f)) = _
  convert he using 1
  simp only [joinCoordinates, fullFourier, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem join_fourier_product (n m : ℕ) (f : BlockHilbert n) (g : BlockHilbert m) :
    (Lp.fourierTransformₗᵢ (Block (n+m)) ℂ)
      (joinCoordinates n m (productState volume volume f g)) =
    joinCoordinates n m (productState volume volume
      ((Lp.fourierTransformₗᵢ (Block n) ℂ) f) ((Lp.fourierTransformₗᵢ (Block m) ℂ) g)) := by
  rw [join_fullFourier, fullFourier_eq_partials, rightFourier_product, leftFourier_product]

#print axioms join_fullFourier
#print axioms join_fourier_product
end
end UnifiedTheory.Audit.KFCausalJoinedFourierProduct

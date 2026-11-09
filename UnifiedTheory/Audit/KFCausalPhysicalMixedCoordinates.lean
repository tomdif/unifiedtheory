/- Actual unitary mixed coordinates for the physical six-mode Hilbert space.
First form symmetric/antisymmetric pairs, then Fourier-transform just the two
antisymmetric positions. Clock, symmetric positions and neutral matter remain
in the other block. Frequencies use mathlib's 2*pi Fourier convention; they
are not silently identified with momenta or with the finite charge action. -/
import UnifiedTheory.Audit.KFCausalPairedModeCoordinates
import UnifiedTheory.Audit.KFCausalPartialFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPartialFourier
open UnifiedTheory.Audit.KFCausalL2FourierIntegral

def pairedCoordinates : Hilbert ≃ₗᵢ[ℂ] ProductHilbert 2 4 :=
  euclideanPullback.trans (modePullback.symm.trans (coordinates 2 4).symm)

def mixedCoordinates : Hilbert ≃ₗᵢ[ℂ] ProductHilbert 2 4 :=
  pairedCoordinates.trans (leftFourier 2 4)

def pairedState (f : BlockHilbert 2) (g : BlockHilbert 4) : Hilbert :=
  pairedCoordinates.symm (productState volume volume f g)

theorem pairedState_coordinates (f : BlockHilbert 2) (g : BlockHilbert 4) :
    pairedCoordinates (pairedState f g) = productState volume volume f g :=
  pairedCoordinates.apply_symm_apply _

theorem mixedCoordinates_pairedState (f : BlockHilbert 2) (g : BlockHilbert 4) :
    mixedCoordinates (pairedState f g) =
      productState volume volume ((Lp.fourierTransformₗᵢ (Block 2) ℂ) f) g := by
  change leftFourier 2 4 (pairedCoordinates (pairedState f g)) = _
  rw [pairedState_coordinates, leftFourier_product]

theorem mixedCoordinates_inverse_product (f : BlockHilbert 2) (g : BlockHilbert 4) :
    mixedCoordinates.symm (productState volume volume f g) =
      pairedState ((Lp.fourierTransformₗᵢ (Block 2) ℂ).symm f) g := by
  apply mixedCoordinates.injective
  rw [LinearIsometryEquiv.apply_symm_apply, mixedCoordinates_pairedState,
    LinearIsometryEquiv.apply_symm_apply]

theorem mixedCoordinates_functions_coe (f : Block 2 → ℂ) (g : Block 4 → ℂ)
    (hf1 : Integrable f) (hf2 : MemLp f 2) (hg2 : MemLp g 2) :
    mixedCoordinates (pairedState (hf2.toLp f) (hg2.toLp g)) =ᵐ[volume]
      fun z : Block 2 × Block 4 => (𝓕 f) z.1 * g z.2 := by
  change leftFourier 2 4 (pairedCoordinates (pairedState (hf2.toLp f) (hg2.toLp g))) =ᵐ[volume] _
  rw [pairedState_coordinates]
  exact leftFourier_functions_coe 2 4 f g hf1 hf2 hg2

theorem pairedState_position_coe (f : Block 2 → ℂ) (g : Block 4 → ℂ)
    (hf : MemLp f 2) (hg : MemLp g 2) :
    euclideanPullback (pairedState (hf.toLp f) (hg.toLp g)) =ᵐ[volume]
      fun x => f (WithLp.toLp 2 ![scale * (x 1-x 2), scale * (x 3-x 4)]) *
        g (WithLp.toLp 2 ![x 0, scale * (x 1+x 2), scale * (x 3+x 4), x 5]) := by
  have he : euclideanPullback (pairedState (hf.toLp f) (hg.toLp g)) =
      modePullback (coordinates 2 4 (productState volume volume (hf.toLp f) (hg.toLp g))) := by
    exact euclideanPullback.apply_symm_apply _
  rw [he]
  filter_upwards [modePullback_coe (coordinates 2 4
    (productState volume volume (hf.toLp f) (hg.toLp g))),
    mode_preserves_volume.quasiMeasurePreserving.ae
      (coordinates_product_coe 2 4 f g hf hg)] with x hx hp
  exact hx.trans hp

theorem mixedCoordinates_norm (f : Hilbert) : ‖mixedCoordinates f‖ = ‖f‖ :=
  mixedCoordinates.norm_map f

theorem mixedCoordinates_inner (f g : Hilbert) :
    inner ℂ (mixedCoordinates f) (mixedCoordinates g) = inner ℂ f g :=
  mixedCoordinates.inner_map_map f g

theorem mixedCoordinates_surjective : Function.Surjective mixedCoordinates :=
  mixedCoordinates.surjective

#print axioms pairedCoordinates
#print axioms mixedCoordinates
#print axioms pairedState_coordinates
#print axioms mixedCoordinates_pairedState
#print axioms mixedCoordinates_inverse_product
#print axioms mixedCoordinates_functions_coe
#print axioms pairedState_position_coe
#print axioms mixedCoordinates_norm
#print axioms mixedCoordinates_inner
#print axioms mixedCoordinates_surjective

end
end UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates

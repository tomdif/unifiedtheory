/- An actual unitary partial Fourier transform of the two narrow reciprocal
charged modes. The clock, two broad modes and neutral coordinate remain as
spectators. This transform retains mathlib's Fourier frequency convention. -/
import UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalNarrowFourierCoordinates
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanConfiguration (Space FrequencyHilbert euclideanPullback)
open KFCausalEuclideanProductCoordinates
open KFCausalL2TensorEmbedding
open KFCausalPairedModeCoordinates (scale)
open KFCausalMeasureUnitaryPullback
open KFCausalPartialFourier

def modeIsometry : Space ≃ₗᵢ[ℝ] Joint 2 4 :=
  KFCausalPairedModeCoordinates.modeIsometry.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (Sum.inl (0 : Fin 2)) (Sum.inr (1 : Fin 4))))

theorem narrow_coordinates (x : Space) :
    (split 2 4 (modeIsometry x)).1 =
      WithLp.toLp 2 ![scale*(x 1+x 2),scale*(x 3-x 4)] := by
  ext i
  fin_cases i <;> simp [split_fst,modeIsometry,LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrLeft,Equiv.swap_apply_def,
    KFCausalPairedModeCoordinates.modeIsometry,KFCausalPairedModeCoordinates.modeEquiv,
    KFCausalPairedModeCoordinates.forward]

theorem spectator_coordinates (x : Space) :
    (split 2 4 (modeIsometry x)).2 =
      WithLp.toLp 2 ![x 0,scale*(x 1-x 2),scale*(x 3+x 4),x 5] := by
  ext i
  fin_cases i <;> simp [split_snd,modeIsometry,LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrLeft,Equiv.swap_apply_def,
    KFCausalPairedModeCoordinates.modeIsometry,KFCausalPairedModeCoordinates.modeEquiv,
    KFCausalPairedModeCoordinates.forward]

theorem mode_preserves_volume : MeasurePreserving modeIsometry := modeIsometry.measurePreserving

def modePullback : JointHilbert 2 4 ≃ₗᵢ[ℂ] FrequencyHilbert :=
  unitaryPullback modeIsometry.toMeasurableEquiv mode_preserves_volume

theorem modePullback_coe (f : JointHilbert 2 4) :
    modePullback f =ᵐ[volume] f ∘ modeIsometry := unitaryPullback_coe _ _ _

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
  rw [pairedState_coordinates,leftFourier_product]

theorem mixedCoordinates_functions_coe (f : Block 2 → ℂ) (g : Block 4 → ℂ)
    (hf1 : Integrable f) (hf2 : MemLp f 2) (hg2 : MemLp g 2) :
    mixedCoordinates (pairedState (hf2.toLp f) (hg2.toLp g)) =ᵐ[volume]
      fun z : Block 2 × Block 4 => (𝓕 f) z.1*g z.2 := by
  change leftFourier 2 4 (pairedCoordinates (pairedState (hf2.toLp f) (hg2.toLp g))) =ᵐ[volume] _
  rw [pairedState_coordinates]
  exact leftFourier_functions_coe 2 4 f g hf1 hf2 hg2

theorem pairedState_position_coe (f : Block 2 → ℂ) (g : Block 4 → ℂ)
    (hf : MemLp f 2) (hg : MemLp g 2) :
    euclideanPullback (pairedState (hf.toLp f) (hg.toLp g)) =ᵐ[volume]
      fun x => f (WithLp.toLp 2 ![scale*(x 1+x 2),scale*(x 3-x 4)])*
        g (WithLp.toLp 2 ![x 0,scale*(x 1-x 2),scale*(x 3+x 4),x 5]) := by
  have he : euclideanPullback (pairedState (hf.toLp f) (hg.toLp g)) =
      modePullback (coordinates 2 4 (productState volume volume (hf.toLp f) (hg.toLp g))) :=
    euclideanPullback.apply_symm_apply _
  rw [he]
  filter_upwards [modePullback_coe (coordinates 2 4
    (productState volume volume (hf.toLp f) (hg.toLp g))),
    mode_preserves_volume.quasiMeasurePreserving.ae
      (coordinates_product_coe 2 4 f g hf hg)] with x hx hp
  simpa only [Function.comp_apply,narrow_coordinates,spectator_coordinates] using hx.trans hp

theorem mixedCoordinates_norm (f : Hilbert) : ‖mixedCoordinates f‖ = ‖f‖ :=
  mixedCoordinates.norm_map f

theorem mixedCoordinates_inner (f g : Hilbert) :
    inner ℂ (mixedCoordinates f) (mixedCoordinates g) = inner ℂ f g :=
  mixedCoordinates.inner_map_map f g

theorem mixedCoordinates_surjective : Function.Surjective mixedCoordinates :=
  mixedCoordinates.surjective

#print axioms narrow_coordinates
#print axioms spectator_coordinates
#print axioms mode_preserves_volume
#print axioms modePullback_coe
#print axioms pairedState_coordinates
#print axioms mixedCoordinates_pairedState
#print axioms mixedCoordinates_functions_coe
#print axioms pairedState_position_coe
#print axioms mixedCoordinates_norm
#print axioms mixedCoordinates_inner
#print axioms mixedCoordinates_surjective
end
end UnifiedTheory.Audit.KFCausalNarrowFourierCoordinates

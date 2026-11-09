/- Physical translations in an antisymmetric mode become translations of
the first paired block. The existing partial Fourier transform therefore
gives an exact phase representative in the actual charge coordinates. -/
import UnifiedTheory.Audit.KFCausalPartialFourierTranslation
import UnifiedTheory.Audit.KFCausalPhysicalCircleAction
import UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space FrequencyHilbert euclideanPullback)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalFourierTranslation (translation translation_coe shift_preserves_volume phase)
open UnifiedTheory.Audit.KFCausalPartialFourier (leftFourier)
open UnifiedTheory.Audit.KFCausalPartialFourierTranslation

def leftVector (a : Block 2) : Joint 2 4 := WithLp.toLp 2 fun
  | .inl i => a i
  | .inr _ => 0

theorem leftVector_smul (t : ℝ) (a : Block 2) : leftVector (t • a) = t • leftVector a := by
  ext i
  rcases i with i | i <;> simp [leftVector]

theorem split_mode_add (v : Space) (a : Block 2) (hv : modeIsometry v = leftVector a) (x : Space) :
    split 2 4 (modeIsometry (x+v)) = ((split 2 4 (modeIsometry x)).1+a,(split 2 4 (modeIsometry x)).2) := by
  rw [map_add,hv]
  ext i <;> simp [split_fst,split_snd,leftVector]

theorem positionCoordinates_coe (f : ProductHilbert 2 4) :
    modePullback (coordinates 2 4 f) =ᵐ[volume] fun x => f (split 2 4 (modeIsometry x)) := by
  filter_upwards [modePullback_coe (coordinates 2 4 f),
    mode_preserves_volume.quasiMeasurePreserving.ae (coordinates_coe 2 4 f)] with x hm hc
  exact hm.trans hc

theorem positionCoordinates_translation (v : Space) (a : Block 2)
    (hv : modeIsometry v = leftVector a) (f : ProductHilbert 2 4) :
    translation v (modePullback (coordinates 2 4 f)) =
      modePullback (coordinates 2 4 (leftTranslation 2 4 a f)) := by
  apply Lp.ext
  filter_upwards [translation_coe v (modePullback (coordinates 2 4 f)),
    (shift_preserves_volume v).quasiMeasurePreserving.ae (positionCoordinates_coe f),
    positionCoordinates_coe (leftTranslation 2 4 a f),
    mode_preserves_volume.quasiMeasurePreserving.ae
      ((split_preserves_volume 2 4).quasiMeasurePreserving.ae (leftTranslation_coe 2 4 a f))] with x ht hf hg hl
  change (modePullback (coordinates 2 4 f)) (x+v) = f (split 2 4 (modeIsometry (x+v))) at hf
  rw [ht,hf,hg,hl,split_mode_add v a hv]

def pairedEuclidean : FrequencyHilbert ≃ₗᵢ[ℂ] ProductHilbert 2 4 :=
  modePullback.symm.trans (coordinates 2 4).symm

theorem pairedEuclidean_translation (v : Space) (a : Block 2)
    (hv : modeIsometry v = leftVector a) (f : FrequencyHilbert) :
    pairedEuclidean (translation v f) = leftTranslation 2 4 a (pairedEuclidean f) := by
  apply (coordinates 2 4).injective
  apply modePullback.injective
  have he (g : FrequencyHilbert) : modePullback (coordinates 2 4 (pairedEuclidean g)) = g := by
    simp only [pairedEuclidean,LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.apply_symm_apply]
  rw [he,← positionCoordinates_translation v a hv,he]

def chargeEuclidean : FrequencyHilbert ≃ₗᵢ[ℂ] JointHilbert 2 4 :=
  pairedEuclidean.trans ((leftFourier 2 4).trans (coordinates 2 4))

theorem chargeEuclidean_physical (f : KFCausalConfigurationTestSpace.Hilbert) :
    chargeEuclidean (euclideanPullback f) = chargeCoordinates f := rfl

theorem chargeEuclidean_translation_coe (v : Space) (a : Block 2)
    (hv : modeIsometry v = leftVector a) (f : FrequencyHilbert) :
    chargeEuclidean (translation v f) =ᵐ[volume]
      fun x => phase a (split 2 4 x).1*(chargeEuclidean f) x := by
  have he : chargeEuclidean (translation v f) =
      coordinates 2 4 (leftPhase 2 4 a (leftFourier 2 4 (pairedEuclidean f))) := by
    change coordinates 2 4 (leftFourier 2 4 (pairedEuclidean (translation v f))) = _
    rw [pairedEuclidean_translation v a hv,leftFourier_translation]
  rw [he]
  filter_upwards [coordinates_coe 2 4 (leftPhase 2 4 a (leftFourier 2 4 (pairedEuclidean f))),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae
      (leftPhase_coe 2 4 a (leftFourier 2 4 (pairedEuclidean f))),
    coordinates_coe 2 4 (leftFourier 2 4 (pairedEuclidean f))] with x hc hp hf
  change (chargeEuclidean f) x = _ at hf
  simp only [Function.comp_apply] at hc hf
  rw [hc,hp,hf]

theorem chargeEuclidean_directional_coe (v : Space) (a : Block 2)
    (hv : modeIsometry v = leftVector a) (t : ℝ) (f : FrequencyHilbert) :
    chargeEuclidean (translation (t • v) f) =ᵐ[volume]
      fun x => Complex.exp ((2*Real.pi*t*inner ℝ (split 2 4 x).1 a : ℝ)*Complex.I)*(chargeEuclidean f) x := by
  have hvt : modeIsometry (t • v) = leftVector (t • a) := by rw [map_smul,hv,leftVector_smul]
  filter_upwards [chargeEuclidean_translation_coe (t • v) (t • a) hvt f] with x hx
  rw [hx,KFCausalDirectionalTranslationMomentum.phase_eq]

#print axioms leftVector_smul
#print axioms split_mode_add
#print axioms positionCoordinates_coe
#print axioms positionCoordinates_translation
#print axioms pairedEuclidean_translation
#print axioms chargeEuclidean_physical
#print axioms chargeEuclidean_translation_coe
#print axioms chargeEuclidean_directional_coe

end
end UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates

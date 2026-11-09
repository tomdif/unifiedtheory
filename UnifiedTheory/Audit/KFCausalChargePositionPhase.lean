/- Translations of antisymmetric Fourier coordinates are exactly phases
of the original antisymmetric positions. Every identity is on full L2. -/
import UnifiedTheory.Audit.KFCausalL2FourierModulation
import UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalChargePositionPhase
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space FrequencyHilbert)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates
open UnifiedTheory.Audit.KFCausalFourierTranslation (translation translation_coe shift_preserves_volume phase)
open UnifiedTheory.Audit.KFCausalPartialFourier (leftFourier)
open UnifiedTheory.Audit.KFCausalPartialFourierTranslation
open UnifiedTheory.Audit.KFCausalL2FourierModulation

theorem leftVector_neg (a : Block 2) : leftVector (-a) = -leftVector a := by
  ext i
  rcases i with i | i <;> simp [leftVector]

theorem coordinates_leftTranslation (a : Block 2) (f : ProductHilbert 2 4) :
    coordinates 2 4 (leftTranslation 2 4 a f) = translation (leftVector a) (coordinates 2 4 f) := by
  apply Lp.ext
  filter_upwards [coordinates_coe 2 4 (leftTranslation 2 4 a f),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae (leftTranslation_coe 2 4 a f),
    translation_coe (leftVector a) (coordinates 2 4 f),
    (shift_preserves_volume (leftVector a)).quasiMeasurePreserving.ae (coordinates_coe 2 4 f)] with x hc hl ht hf
  change (coordinates 2 4 f) (x+leftVector a) = f (split 2 4 (x+leftVector a)) at hf
  simp only [Function.comp_apply] at hc
  rw [hc,hl,ht,hf]
  congr 1
  ext i <;> simp [split_fst,split_snd,leftVector]

def positionPhase (a : Block 2) (f : FrequencyHilbert) : FrequencyHilbert :=
  pairedEuclidean.symm (leftPhase 2 4 a (pairedEuclidean f))

theorem positionPhase_coe (a : Block 2) (f : FrequencyHilbert) :
    positionPhase a f =ᵐ[volume] fun x => phase a (split 2 4 (modeIsometry x)).1*f x := by
  have hi : modePullback (coordinates 2 4 (pairedEuclidean f)) = f :=
    pairedEuclidean.symm_apply_apply f
  filter_upwards [positionCoordinates_coe (leftPhase 2 4 a (pairedEuclidean f)),
    mode_preserves_volume.quasiMeasurePreserving.ae
      ((split_preserves_volume 2 4).quasiMeasurePreserving.ae (leftPhase_coe 2 4 a (pairedEuclidean f))),
    positionCoordinates_coe (pairedEuclidean f)] with x hp hl hf
  change (positionPhase a f) x = _ at hp
  rw [hi] at hf
  rw [hp,hl,hf]

theorem chargeEuclidean_positionPhase (a : Block 2) (f : FrequencyHilbert) :
    chargeEuclidean (positionPhase a f) = translation (leftVector (-a)) (chargeEuclidean f) := by
  change coordinates 2 4 (leftFourier 2 4 (pairedEuclidean
    (pairedEuclidean.symm (leftPhase 2 4 a (pairedEuclidean f))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,leftFourier_phase,coordinates_leftTranslation]
  rfl

theorem inverse_translation_coe (a : Block 2) (f : JointHilbert 2 4) :
    chargeEuclidean.symm (translation (leftVector a) f) =ᵐ[volume]
      fun x => phase (-a) (split 2 4 (modeIsometry x)).1*(chargeEuclidean.symm f) x := by
  have he : chargeEuclidean.symm (translation (leftVector a) f) =
      positionPhase (-a) (chargeEuclidean.symm f) := by
    apply chargeEuclidean.injective
    rw [LinearIsometryEquiv.apply_symm_apply,chargeEuclidean_positionPhase,
      neg_neg,LinearIsometryEquiv.apply_symm_apply]
  rw [he]
  exact positionPhase_coe (-a) _

theorem inverse_directional_coe (a : Block 2) (t : ℝ) (f : JointHilbert 2 4) :
    chargeEuclidean.symm (translation (t • leftVector a) f) =ᵐ[volume] fun x =>
      Complex.exp ((2*Real.pi*t*inner ℝ (split 2 4 (modeIsometry x)).1 (-a) : ℝ)*Complex.I)*
        (chargeEuclidean.symm f) x := by
  rw [← leftVector_smul]
  filter_upwards [inverse_translation_coe (t • a) f] with x hx
  rw [hx,← smul_neg,KFCausalDirectionalTranslationMomentum.phase_eq]

#print axioms leftVector_neg
#print axioms coordinates_leftTranslation
#print axioms positionPhase_coe
#print axioms chargeEuclidean_positionPhase
#print axioms inverse_translation_coe
#print axioms inverse_directional_coe

end
end UnifiedTheory.Audit.KFCausalChargePositionPhase

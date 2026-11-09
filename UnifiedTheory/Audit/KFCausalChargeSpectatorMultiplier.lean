/- Arbitrary contractive multipliers on the four spectator position
coordinates pass unchanged through the actual antisymmetric partial
Fourier transform. The identities hold on the whole L2 space. -/
import UnifiedTheory.Audit.KFCausalPartialFourierMultiplier
import UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalChargeSpectatorMultiplier
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (FrequencyHilbert)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates
open UnifiedTheory.Audit.KFCausalPartialFourier (leftFourier)
open UnifiedTheory.Audit.KFCausalPartialFourierMultiplier
open UnifiedTheory.Audit.KFCausalContractiveMultiplier

variable (w : Block 4 → ℂ) (hw : Measurable w) (hb : ∀ x, ‖w x‖ ≤ 1)

def euclideanMultiplier (f : FrequencyHilbert) : FrequencyHilbert :=
  pairedEuclidean.symm (rightMultiplier 2 4 w hw hb (pairedEuclidean f))

theorem euclideanMultiplier_coe (f : FrequencyHilbert) :
    euclideanMultiplier w hw hb f =ᵐ[volume] fun x => w (split 2 4 (modeIsometry x)).2*f x := by
  have hi : modePullback (coordinates 2 4 (pairedEuclidean f)) = f := pairedEuclidean.symm_apply_apply f
  filter_upwards [positionCoordinates_coe (rightMultiplier 2 4 w hw hb (pairedEuclidean f)),
    mode_preserves_volume.quasiMeasurePreserving.ae
      ((split_preserves_volume 2 4).quasiMeasurePreserving.ae (rightMultiplier_coe 2 4 w hw hb (pairedEuclidean f))),
    positionCoordinates_coe (pairedEuclidean f)] with x hp hr hf
  change (euclideanMultiplier w hw hb f) x = _ at hp
  rw [hi] at hf
  rw [hp,hr,hf]

def jointMultiplier : JointHilbert 2 4 →L[ℂ] JointHilbert 2 4 :=
  multiplyL (fun x => w (split 2 4 x).2) (hw.comp (by fun_prop)) (fun x => hb _)

theorem jointMultiplier_coe (f : JointHilbert 2 4) :
    jointMultiplier w hw hb f =ᵐ[volume] fun x => w (split 2 4 x).2*f x :=
  multiplyL_coe _ _ _ f

theorem coordinates_multiplier (f : ProductHilbert 2 4) :
    coordinates 2 4 (rightMultiplier 2 4 w hw hb f) = jointMultiplier w hw hb (coordinates 2 4 f) := by
  apply Lp.ext
  filter_upwards [coordinates_coe 2 4 (rightMultiplier 2 4 w hw hb f),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae (rightMultiplier_coe 2 4 w hw hb f),
    jointMultiplier_coe w hw hb (coordinates 2 4 f),coordinates_coe 2 4 f] with x hc hr hj hf
  simp only [Function.comp_apply] at hc hf
  rw [hc,hr,hj,hf]

theorem chargeEuclidean_multiplier (f : FrequencyHilbert) :
    chargeEuclidean (euclideanMultiplier w hw hb f) = jointMultiplier w hw hb (chargeEuclidean f) := by
  change coordinates 2 4 (leftFourier 2 4 (pairedEuclidean
    (pairedEuclidean.symm (rightMultiplier 2 4 w hw hb (pairedEuclidean f))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,leftFourier_commutes,coordinates_multiplier]
  rfl

#print axioms euclideanMultiplier_coe
#print axioms jointMultiplier_coe
#print axioms coordinates_multiplier
#print axioms chargeEuclidean_multiplier

end
end UnifiedTheory.Audit.KFCausalChargeSpectatorMultiplier

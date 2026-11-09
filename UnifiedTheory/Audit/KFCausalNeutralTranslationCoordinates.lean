/- Neutral coordinate translation commutes with the actual clock-floor
straightening unitary. Its coupled Fourier representation is an exact
unit-modulus multiplier on every L2 state. -/
import UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates
import UnifiedTheory.Audit.KFCausalPhysicalCanonicalCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse flow)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (coordinateHomeomorph)
open UnifiedTheory.Audit.KFCausalClockFloorTestPullback (weight)
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates (coupledFourier)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space split euclideanPullback euclideanPullback_coe split_preserves_volume)
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation (translation translation_coe shift_preserves)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def vector (r : ℝ) : Configuration := (0,Pi.single 4 r)
def action (r : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert := translation volume (vector r)

theorem action_coe (r : ℝ) (f : Hilbert) : action r f =ᵐ[volume] fun x => f (x+vector r) :=
  translation_coe volume (vector r) f

theorem flow_neutral (t r : ℝ) (x : Transverse) :
    flow t (x+Pi.single 4 r) = flow t x+Pi.single 4 r := by
  funext i
  fin_cases i <;> simp [flow]
  ring

theorem coordinate_shift (ε : ℝ) (hε : 0 < ε) (r : ℝ) (x : Configuration) :
    coordinateHomeomorph ε hε (x+vector r) = coordinateHomeomorph ε hε x+vector r := by
  apply Prod.ext
  · change KFCausalRegularizedLongitudinalChart.chart ε (x.1+0) =
      KFCausalRegularizedLongitudinalChart.chart ε x.1+0
    rw [add_zero,add_zero]
  · change flow (-(x.1+0)) (x.2+Pi.single 4 r) = flow (-x.1) x.2+Pi.single 4 r
    simpa only [add_zero] using flow_neutral (-x.1) r x.2

theorem weight_shift (ε r : ℝ) (x : Configuration) : weight ε (x+vector r) = weight ε x := by
  simp [weight,vector]

theorem coordinates_commutes (ε : ℝ) (hε : 0 < ε) (r : ℝ) (f : Hilbert) :
    coordinates ε hε (action r f) = action r (coordinates ε hε f) := by
  apply Lp.ext
  filter_upwards [coordinates_coe ε hε (action r f),
    (coordinate_quasiMeasurePreserving ε hε).ae (action_coe r f),
    action_coe r (coordinates ε hε f),
    (shift_preserves volume (vector r)).quasiMeasurePreserving.ae (coordinates_coe ε hε f)] with x hc ht ha hd
  change action r f (coordinateHomeomorph ε hε x) = _ at ht
  change coordinates ε hε f (x+vector r) = _ at hd
  rw [hc,ha,hd]
  change weight ε x*action r f (coordinateHomeomorph ε hε x) =
    weight ε (x+vector r)*f (coordinateHomeomorph ε hε (x+vector r))
  rw [ht,weight_shift,coordinate_shift]

theorem coordinates_inverse_commutes (ε : ℝ) (hε : 0 < ε) (r : ℝ) (f : Hilbert) :
    (coordinates ε hε).symm (action r f) = action r ((coordinates ε hε).symm f) := by
  apply (coordinates ε hε).injective
  rw [LinearIsometryEquiv.apply_symm_apply,coordinates_commutes,LinearIsometryEquiv.apply_symm_apply]

theorem euclidean_action (r : ℝ) (f : Hilbert) :
    euclideanPullback (action r f) =
      KFCausalFourierTranslation.translation (split.symm (vector r)) (euclideanPullback f) := by
  apply Lp.ext
  filter_upwards [euclideanPullback_coe (action r f),
    split_preserves_volume.quasiMeasurePreserving.ae (action_coe r f),
    KFCausalFourierTranslation.translation_coe (split.symm (vector r)) (euclideanPullback f),
    (KFCausalFourierTranslation.shift_preserves_volume (split.symm (vector r))).quasiMeasurePreserving.ae
      (euclideanPullback_coe f)] with x he ha ht hf
  change action r f (split x) = _ at ha
  change euclideanPullback f (x+split.symm (vector r)) = _ at hf
  rw [he,ht,hf]
  simp only [Function.comp_apply]
  rw [ha]
  congr 1

theorem coupledFourier_action (ε : ℝ) (hε : 0 < ε) (r : ℝ) (f : Hilbert) :
    coupledFourier ε hε (action r f) =
      KFCausalFourierTranslation.phaseAction (split.symm (vector r)) (coupledFourier ε hε f) := by
  change (Lp.fourierTransformₗᵢ Space ℂ) (euclideanPullback ((coordinates ε hε).symm (action r f))) = _
  rw [coordinates_inverse_commutes,euclidean_action,KFCausalFourierTranslation.fourier_translation]
  rfl

theorem coupledFourier_action_coe (ε : ℝ) (hε : 0 < ε) (r : ℝ) (f : Hilbert) :
    coupledFourier ε hε (action r f) =ᵐ[volume] fun k =>
      KFCausalFourierTranslation.phase (split.symm (vector r)) k*coupledFourier ε hε f k := by
  rw [coupledFourier_action]
  exact KFCausalFourierTranslation.phaseAction_coe _ _

#print axioms action_coe
#print axioms flow_neutral
#print axioms coordinate_shift
#print axioms weight_shift
#print axioms coordinates_commutes
#print axioms coordinates_inverse_commutes
#print axioms euclidean_action
#print axioms coupledFourier_action
#print axioms coupledFourier_action_coe

end
end UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates

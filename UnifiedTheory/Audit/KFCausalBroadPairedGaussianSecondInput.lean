/- The actual paired Gaussian baseline in the second straightened clock
coordinates. The two inverse half-clock weights are combined explicitly,
and the transverse normalization matches the physical shear. -/
import UnifiedTheory.Audit.KFCausalBroadPairedGaussian
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalSecondInput
import UnifiedTheory.Audit.KFCausalPhysicalReciprocalNormalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalBroadPairedGaussianSecondInput
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates (Block Joint split split_preserves_volume coordinates_coe)
open KFCausalPhysicalMixedCoordinates (mixedCoordinates)
open KFCausalPhysicalFourierGeneralCoordinates (Product mixed_inverse_coe)
open KFCausalPhysicalReciprocalNormalization (normalize coupling)
open KFCausalClockFloorMixedChart (mixedMap mixedMap_quasiMeasurePreserving)
open KFCausalClockFloorPairedStraightening (clockInverse dilation)
open KFCausalClockFloorMixedRadial (clockMixed clockMixed_coe)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalVacuumMixedClockNormalization (inverseHalf)
open KFCausalClockFloorInvariantTrial (clockFunction realClock)
open KFCausalPairedGaussianStates (coordinateDensity)

private theorem split_left (x : Product) (i : Fin 2) :
    (split 2 4).symm x (.inl i)=x.1 i := rfl

private theorem split_right (x : Product) (i : Fin 4) :
    (split 2 4).symm x (.inr i)=x.2 i := rfl

theorem mixedMap_clock (ε : ℝ) (hε : 0 < ε) (x : Product) :
    (mixedMap ε hε x).2 0=clockInverse ε hε x.2 := rfl

theorem normalize_mixedMap (ε : ℝ) (hε : 0 < ε) (α w c : ℝ)
    (hα : 0 < α) (hw : 0 < w) (x : Product) :
    normalize α w c ((split 2 4).symm (mixedMap ε hε x))=
      KFCausalComplexShearPerturbation.flow (coupling α w) (clockInverse ε hε x.2:ℂ)
        (normalize α w c ((split 2 4).symm x)) := by
  rw [← KFCausalPhysicalReciprocalNormalization.normalize_shear α w c _ hα hw]
  ext i
  fin_cases i <;> simp [KFCausalPhysicalReciprocalNormalization.normalize,
    mixedMap,dilation,KFCausalClockFloorSpectatorChart.backward,
    KFCausalClockFloorSpectatorChart.changeClock,KFCausalClockFloorSpectatorChart.flow,
    KFCausalChargeShearJointFlow.flow_first,KFCausalChargeShearJointFlow.flow_second,
    clockInverse,split_left,split_right,← Real.exp_neg,← neg_div]

variable (ε a α w c : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hw : 0 < w)
  (hmatch : Real.pi^2/α=α*c^2)

include hmatch in
theorem paired_mixed_coe :
    mixedCoordinates (KFCausalBroadPairedGaussian.state ε a α w hε ha hα hw) =ᵐ[volume]
      fun x : Product => coordinateDensity α (α*w/128) w c (clockFunction ε a) ((split 2 4).symm x) := by
  let S := KFCausalBroadPairedGaussian.state ε a α w hε ha hα hw
  have h₁ := (split_preserves_volume 2 4).symm.quasiMeasurePreserving.ae
    (KFCausalBroadPairedGaussian.state_coordinates_coe ε a α w hε ha hα hw c hmatch)
  have h₂ := (split_preserves_volume 2 4).symm.quasiMeasurePreserving.ae
    (coordinates_coe 2 4 (mixedCoordinates S))
  filter_upwards [h₁,h₂] with x hx hc
  change KFCausalPhysicalCircleAction.chargeCoordinates S ((split 2 4).symm x)=_ at hx
  change KFCausalPhysicalCircleAction.chargeCoordinates S ((split 2 4).symm x)=
    mixedCoordinates S (split 2 4 ((split 2 4).symm x)) at hc
  rw [MeasurableEquiv.apply_symm_apply] at hc
  exact hc.symm.trans hx

def secondProfile (x : Product) : ℂ :=
  ((Real.exp (clockInverse ε hε x.2)+ε:ℝ):ℂ)⁻¹*
    coordinateDensity α (α*w/128) w c (clockFunction ε a)
      ((split 2 4).symm (mixedMap ε hε x))

include hmatch in
theorem paired_second_input_coe :
    clockMixed ε hε (inverseL ε hε
      (KFCausalBroadPairedGaussian.state ε a α w hε ha hα hw)) =ᵐ[volume]
      secondProfile ε a α w c hε := by
  let S := KFCausalBroadPairedGaussian.state ε a α w hε ha hα hw
  have hp : mixedCoordinates (inverseL ε hε S) =ᵐ[volume]
      fun x : Product => inverseHalf ε (x.2 0)*
        coordinateDensity α (α*w/128) w c (clockFunction ε a) ((split 2 4).symm x) := by
    filter_upwards [mixed_inverse_coe ε hε S,paired_mixed_coe ε a α w c hε ha hα hw hmatch]
      with x hx hs
    rw [hx,hs]
  filter_upwards [clockMixed_coe ε hε (inverseL ε hε S),
    (mixedMap_quasiMeasurePreserving ε hε).ae hp] with x hx hp
  rw [hx,hp,← mul_assoc,KFCausalCorrelatedClusteredPhysicalSecondInput.weight_cancellation]
  rfl

#print axioms mixedMap_clock
#print axioms normalize_mixedMap
#print axioms paired_mixed_coe
#print axioms paired_second_input_coe
end
end UnifiedTheory.Audit.KFCausalBroadPairedGaussianSecondInput

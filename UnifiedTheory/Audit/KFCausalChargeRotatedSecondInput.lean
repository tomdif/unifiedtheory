/- Actual charge rotation followed by inverse clock dressing and the second
mixed straightening. The finite original vacuum output is retained exactly. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalSecondInput
import UnifiedTheory.Audit.KFCausalClockFloorChargeClockHalf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalChargeRotatedSecondInput
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalFourierGeneralCoordinates (Product mixed_inverse_coe)
open KFCausalEuclideanProductCoordinates (Joint split split_preserves_volume coordinates_coe)
open KFCausalPhysicalMixedCoordinates (mixedCoordinates)
open KFCausalPhysicalCircleAction (chargeCoordinates action action_coordinates)
open KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero flowEquiv flow_preserves_volume)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorMixedRadial (clockMixed clockMixed_coe)
open KFCausalClockFloorMixedChart (mixedMap mixedMap_quasiMeasurePreserving)
open KFCausalCorrelatedClusteredPhysicalSecondInput (weight_cancellation)

theorem charge_of_mixed (f : Hilbert) (ρ : Product → ℂ)
    (hf : mixedCoordinates f =ᵐ[volume] ρ) :
    chargeCoordinates f =ᵐ[volume] fun x => ρ (split 2 4 x) := by
  filter_upwards [coordinates_coe 2 4 (mixedCoordinates f),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae hf] with x hx hf
  exact hx.trans hf

theorem mixed_of_charge (f : Hilbert) (ρ : Joint 2 4 → ℂ)
    (hf : chargeCoordinates f =ᵐ[volume] ρ) :
    mixedCoordinates f =ᵐ[volume] fun x => ρ ((split 2 4).symm x) := by
  have he : ∀ᵐ x ∂volume, (mixedCoordinates f) (split 2 4 x)=ρ x := by
    filter_upwards [coordinates_coe 2 4 (mixedCoordinates f),hf] with x hx hf
    exact hx.symm.trans hf
  simpa only [MeasurableEquiv.apply_symm_apply] using
    (split_preserves_volume 2 4).symm.quasiMeasurePreserving.ae he

def rotatedPoint (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (x : Product) : Product :=
  split 2 4 (flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) θ
    ((split 2 4).symm x))

theorem rotated_mixed (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Hilbert)
    (ρ : Product → ℂ) (hf : mixedCoordinates f =ᵐ[volume] ρ) :
    mixedCoordinates (action h hh θ f) =ᵐ[volume] fun x => ρ (rotatedPoint h hh θ x) := by
  have hc := charge_of_mixed f ρ hf
  have hr : chargeCoordinates (action h hh θ f) =ᵐ[volume]
      fun x => ρ (split 2 4 (flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) θ x)) := by
    rw [action_coordinates]
    filter_upwards [KFCausalMixedCircleAction.action_coe (momentumScale h)
      (momentumScale_ne_zero h hh) θ (chargeCoordinates f),
      (flow_preserves_volume (momentumScale h) (momentumScale_ne_zero h hh) θ).quasiMeasurePreserving.ae hc]
      with x hx hc
    exact hx.trans hc
  exact mixed_of_charge _ _ hr

theorem rotated_second_input (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (θ : ℝ) (f : Hilbert) (ρ : Product → ℂ)
    (hf : mixedCoordinates f =ᵐ[volume] ρ) :
    clockMixed ε hε (inverseL ε hε (action h hh θ f)) =ᵐ[volume]
      fun x => ((Real.exp (KFCausalClockFloorPairedStraightening.clockInverse ε hε x.2)+ε:ℝ):ℂ)⁻¹*
        ρ (rotatedPoint h hh θ (mixedMap ε hε x)) := by
  have hr := rotated_mixed h hh θ f ρ hf
  have hi : mixedCoordinates (inverseL ε hε (action h hh θ f)) =ᵐ[volume]
      fun x => KFCausalVacuumMixedClockNormalization.inverseHalf ε (x.2 0)*
        ρ (rotatedPoint h hh θ x) := by
    filter_upwards [mixed_inverse_coe ε hε (action h hh θ f),hr] with x hx hr
    rw [hx,hr]
  filter_upwards [clockMixed_coe ε hε (inverseL ε hε (action h hh θ f)),
    (mixedMap_quasiMeasurePreserving ε hε).ae hi] with x hx hi
  rw [hx,hi,← mul_assoc,weight_cancellation]

theorem original_rotated_finite_second_input {m : ℕ}
    (f : KFCausalCorrelatedClusteredProfiles.Family m) (ε h : ℝ) (a p : Fin m → ℝ)
    (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
    (hb : |h| ≤ Real.pi*ε/3) (δ : ℝ) (hδ : 0 < δ) (θ : ℝ) :
    clockMixed ε hε (inverseL ε hε (action h hh θ
      (KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteSeconds
        f ε h a p hε hh ha hb δ 7))) =ᵐ[volume]
      fun x => ((Real.exp (KFCausalClockFloorPairedStraightening.clockInverse ε hε x.2)+ε:ℝ):ℂ)⁻¹*
        KFCausalCorrelatedClusteredPhysicalFourierBridge.normalizedFinite f ε a p h δ
          (rotatedPoint h hh θ (mixedMap ε hε x)) :=
  rotated_second_input ε hε h hh θ _ _
    (KFCausalCorrelatedClusteredPhysicalFourierBridge.original_finite_square_mixed
      f ε a p hε h hh ha hb δ hδ)

#print axioms charge_of_mixed
#print axioms mixed_of_charge
#print axioms rotated_mixed
#print axioms rotated_second_input
#print axioms original_rotated_finite_second_input
end
end UnifiedTheory.Audit.KFCausalChargeRotatedSecondInput

/- The actual finite vacuum-square output, after the inverse half-clock
and second clock straightening. Both half-clock weights combine to the
full inverse clock. This supplies the unrotated endpoint for the proposed
mixed-square quotient; it is not a second exponential graph. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalFourierBridge
import UnifiedTheory.Audit.KFCausalClockFloorMixedRadial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalSecondInput
noncomputable section
open MeasureTheory
open KFCausalPhysicalFourierGeneralCoordinates (Product mixed_inverse_coe)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredPhysicalFourierBridge (normalizedFinite original_finite_square_mixed)
open KFCausalClockFloorMixedRadial (clockMixed clockMixed_coe)
open KFCausalClockFloorMixedCoordinates (mixedWeight)
open KFCausalClockFloorMixedChart (mixedMap mixedMap_quasiMeasurePreserving)
open KFCausalClockFloorPairedStraightening (clockInverse)
open KFCausalVacuumMixedClockNormalization (inverseHalf)
open KFCausalClockFloorBoundedInverse (inverseL)

variable (ε : ℝ) (hε : 0 < ε)

theorem weight_cancellation (x : Product) :
    mixedWeight ε hε x*inverseHalf ε ((mixedMap ε hε x).2 0) =
      ((Real.exp (clockInverse ε hε x.2)+ε:ℝ):ℂ)⁻¹ := by
  change (Real.sqrt (Real.exp (clockInverse ε hε x.2)+ε):ℂ)⁻¹*
    (Real.sqrt (Real.exp (clockInverse ε hε x.2)+ε):ℂ)⁻¹ = _
  rw [← mul_inv,← pow_two,← Complex.ofReal_pow,
    Real.sq_sqrt (show 0 ≤ Real.exp (clockInverse ε hε x.2)+ε by positivity)]

variable {m : ℕ} (f : Family m) (h : ℝ) (a p : Fin m → ℝ)
  (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)

def secondInputProfile (δ : ℝ) (x : Product) : ℂ :=
  ((Real.exp (clockInverse ε hε x.2)+ε:ℝ):ℂ)⁻¹*
    normalizedFinite f ε a p h δ (mixedMap ε hε x)

theorem original_finite_square_second_input (δ : ℝ) (hδ : 0 < δ) :
    clockMixed ε hε (inverseL ε hε
      (KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteSeconds
        f ε h a p hε hh ha hb δ 7)) =ᵐ[volume] secondInputProfile ε hε f h a p δ := by
  let Q := KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteSeconds
    f ε h a p hε hh ha hb δ 7
  have hp : KFCausalPhysicalMixedCoordinates.mixedCoordinates (inverseL ε hε Q) =ᵐ[volume]
      fun x => inverseHalf ε (x.2 0)*normalizedFinite f ε a p h δ x := by
    filter_upwards [mixed_inverse_coe ε hε Q,
      original_finite_square_mixed f ε a p hε h hh ha hb δ hδ] with x hx hq
    rw [hx,hq]
  filter_upwards [clockMixed_coe ε hε (inverseL ε hε Q),
    (mixedMap_quasiMeasurePreserving ε hε).ae hp] with x hx hp
  rw [hx,hp,← mul_assoc,weight_cancellation]
  rfl

#print axioms weight_cancellation
#print axioms original_finite_square_second_input
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalSecondInput

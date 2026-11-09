/- The pure-clock coordinate unitary in the actual charge coordinates.
The partial Fourier transform commutes with the clock-only change, so its
whole-L2 weighted representative keeps all charged coordinates fixed. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockPartialFourier
import UnifiedTheory.Audit.KFCausalPhysicalCircleAction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates (pairedCoordinates mixedCoordinates)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalPartialFourier (leftFourier)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockPairedCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorPureClockPartialFourier
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback (unitaryPullback_symm_coe)

variable (ε : ℝ) (hε : 0 < ε)
local notation "U" => KFCausalClockFloorPureClockCoordinates.coordinates ε hε

def jointMap (x : Joint 2 4) : Joint 2 4 :=
  (split 2 4).symm (pairedMap ε hε (split 2 4 x))

theorem jointMap_quasiMeasurePreserving : Measure.QuasiMeasurePreserving (jointMap ε hε) volume volume :=
  (split_preserves_volume 2 4).symm.quasiMeasurePreserving.comp
    ((pairedMap_quasiMeasurePreserving ε hε).comp (split_preserves_volume 2 4).quasiMeasurePreserving)

theorem jointMap_formula (x : Joint 2 4) : jointMap ε hε x = WithLp.toLp 2 (fun
    | .inl i => x (.inl i)
    | .inr i => ![KFCausalRegularizedLongitudinalChart.chart ε (x (.inr 0)),
        x (.inr 1),x (.inr 2),x (.inr 3)] i) := by
  rw [jointMap,pairedMap_apply]
  ext i
  rcases i with i | i
  · rfl
  · fin_cases i <;> rfl

def jointUnitary : JointHilbert 2 4 ≃ₗᵢ[ℂ] JointHilbert 2 4 :=
  (coordinates 2 4).symm.trans ((pairedUnitary ε hε).trans (coordinates 2 4))

def jointWeight (x : Joint 2 4) : ℂ := Real.sqrt (Real.exp (x (.inr 0))+ε)

theorem jointUnitary_coe (f : JointHilbert 2 4) :
    jointUnitary ε hε f =ᵐ[volume] fun x => jointWeight ε x*f (jointMap ε hε x) := by
  have hi := unitaryPullback_symm_coe (split 2 4) (split_preserves_volume 2 4) f
  filter_upwards [coordinates_coe 2 4 (pairedUnitary ε hε ((coordinates 2 4).symm f)),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae
      (pairedUnitary_coe ε hε ((coordinates 2 4).symm f)),
    ((pairedMap_quasiMeasurePreserving ε hε).comp
      (split_preserves_volume 2 4).quasiMeasurePreserving).ae hi] with x he hp hi'
  change coordinates 2 4 (pairedUnitary ε hε ((coordinates 2 4).symm f)) x = _
  simp only [Function.comp_apply] at he
  rw [he,hp]
  change (coordinates 2 4).symm f ((pairedMap ε hε ∘ split 2 4) x) = _ at hi'
  simp only [Function.comp_apply] at hi'
  rw [hi']
  rfl

theorem paired_unitary_coordinates (f : Hilbert) :
    pairedUnitary ε hε (pairedCoordinates f) = pairedCoordinates (U f) := by
  change pairedCoordinates (U (pairedCoordinates.symm (pairedCoordinates f))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem mixed_unitary_coordinates (f : Hilbert) :
    mixedCoordinates (U f) = pairedUnitary ε hε (mixedCoordinates f) := by
  change leftFourier 2 4 (pairedCoordinates (U f)) =
    pairedUnitary ε hε (leftFourier 2 4 (pairedCoordinates f))
  rw [← paired_unitary_coordinates,partialFourier_commutes]

theorem charge_unitary_coordinates (f : Hilbert) :
    chargeCoordinates (U f) = jointUnitary ε hε (chargeCoordinates f) := by
  change coordinates 2 4 (mixedCoordinates (U f)) =
    coordinates 2 4 (pairedUnitary ε hε ((coordinates 2 4).symm (coordinates 2 4 (mixedCoordinates f))))
  rw [LinearIsometryEquiv.symm_apply_apply,mixed_unitary_coordinates]

#print axioms jointMap_quasiMeasurePreserving
#print axioms jointMap_formula
#print axioms jointUnitary_coe
#print axioms paired_unitary_coordinates
#print axioms mixed_unitary_coordinates
#print axioms charge_unitary_coordinates
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeCoordinates

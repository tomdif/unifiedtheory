/- The actual bounded physical defect multiplier in the unitary straightened
Euclidean coordinates used to define longitudinal momentum. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
import UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
import UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
import UnifiedTheory.Audit.KFCausalEuclideanConfiguration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorFlow (coordinateHomeomorph)

def straightening (ε : ℝ) (hε : 0 < ε) : Hilbert ≃ₗᵢ[ℂ] FrequencyHilbert :=
  (coordinates ε hε).symm.trans euclideanPullback

theorem inverse_coordinates_defect_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    (coordinates ε hε).symm (defectOperator ε hε f) =ᵐ[volume]
      fun x => (realDefect ε hε x.1:ℂ)*((coordinates ε hε).symm f) x := by
  filter_upwards [coordinates_inverse_coe ε hε (defectOperator ε hε f),
    coordinates_inverse_coe ε hε f,
    (coordinate_inverse_quasiMeasurePreserving ε hε).ae (defectOperator_coe ε hε f)] with x hx hy hd
  rw [hx,hy]
  unfold inverseFunction
  rw [hd]
  change _ * ((realDefect ε hε x.1:ℂ)*_) = (realDefect ε hε x.1:ℂ)*(_*_)
  ring

theorem straightening_defect_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    straightening ε hε (defectOperator ε hε f) =ᵐ[volume]
      fun x => (realDefect ε hε (x 0):ℂ)*(straightening ε hε f) x := by
  filter_upwards [euclideanPullback_coe ((coordinates ε hε).symm (defectOperator ε hε f)),
    euclideanPullback_coe ((coordinates ε hε).symm f),
    split_preserves_volume.quasiMeasurePreserving.ae (inverse_coordinates_defect_coe ε hε f)] with x hx hy hd
  change (euclideanPullback ((coordinates ε hε).symm (defectOperator ε hε f))) x = _
  rw [hx]
  change ((coordinates ε hε).symm (defectOperator ε hε f)) (split x) = _
  rw [hd]
  change (realDefect ε hε (split x).1:ℂ)*((coordinates ε hε).symm f) (split x) =
    (realDefect ε hε (x 0):ℂ)*(euclideanPullback ((coordinates ε hε).symm f)) x
  rw [hy,split_apply]
  rfl

#print axioms inverse_coordinates_defect_coe
#print axioms straightening_defect_coe

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates

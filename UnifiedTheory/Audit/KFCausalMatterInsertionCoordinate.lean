/- The multiplier of the actual quadratic and quartic matter seconds
uses the field at half the Gaussian clock shift. It is distinct from
an unshifted physical field power after the vacuum square. -/
import UnifiedTheory.Audit.KFCausalSourcedWidthPointFieldInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalMatterInsertionCoordinate
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint split)
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalComplexClockInverse (complexInverse complexInverse_real)
open KFCausalTwoShearClockQuotient (shift)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalChargeRotatedSecondInput (rotatedPoint)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalClockFloorPairedStraightening (clockInverse)

def halfScale (ε h : ℝ) (q : ℂ) : ℂ :=
  Complex.exp ((complexInverse ε (shift (h/2) q)-complexInverse ε q)/2)

def coefficient (ε h α w c θ : ℝ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  KFCausalPointFieldInsertionCoordinate.neutralCoefficient ε h α w c θ q x+
    2*(KFCausalPairedModeCoordinates.scale:ℂ)*(3*halfScale ε h q-2)*
      KFCausalSymmetricInsertionCoordinate.coefficient ε h α w c θ 1 q x

theorem halfScale_real (ε : ℝ) (hε : 0 < ε) (h : ℝ) (x : Product) :
    halfScale ε h (x.2 0:ℂ) =
      KFCausalClockFloorRelativeShift.scale ε (-h/2) (clockInverse ε hε x.2) := by
  have hs : complexInverse ε (x.2 0:ℂ)=(clockInverse ε hε x.2:ℂ) :=
    complexInverse_real ε hε _
  unfold halfScale KFCausalClockFloorRelativeShift.scale
    KFCausalClockFloorRelativeShift.relative KFCausalClockFloorRelativeShift.inverse
  rw [show -h/2=-(h/2) by ring,
    KFCausalSingleGaussianNormalizedDensity.argument_clock ε hε (h/2) x,hs]
  rfl

theorem coefficient_real (ε : ℝ) (hε : 0 < ε) (h α w : ℝ)
    (hh : h ≠ 0) (hα : 0 < α) (hw : 0 < w) (θ : ℝ) (x : Product) :
    coefficient ε h α w (momentumScale h) θ (x.2 0:ℂ) ((split 2 4).symm x) =
      KFCausalShiftedNarrowFourierGeometry.mixedField
        (KFCausalClockFloorRelativeShift.scale ε (-h/2) (clockInverse ε hε x.2))
        (rotatedPoint h hh θ (mixedMap ε hε x)).2 := by
  rw [coefficient,KFCausalSourcedWidthPointFieldInsertion.neutralCoefficient_real ε hε h α w hh hα hw θ x,
    KFCausalSourcedWidthSymmetricInsertion.coefficient_real ε hε h α w hh hα hw θ 1 x,
    halfScale_real ε hε h x]
  rfl

#print axioms halfScale_real
#print axioms coefficient_real
end
end UnifiedTheory.Audit.KFCausalMatterInsertionCoordinate

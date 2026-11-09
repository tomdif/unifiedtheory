/- Exact normalized complex-shear representative of the actual Gaussian
first square after arbitrary charge rotation and second clock dressing. -/
import UnifiedTheory.Audit.KFCausalWidthGaussianSecondInput
import UnifiedTheory.Audit.KFCausalSingleGaussianNormalizedDensity
import UnifiedTheory.Audit.KFCausalWidthGaussianShearIdentity
import UnifiedTheory.Audit.KFCausalBroadPairedGaussianSecondInput
import UnifiedTheory.Audit.KFCausalWidthGaussianHolomorphicQuotient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalWidthGaussianNormalizedDensity
noncomputable section
open MeasureTheory
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalEuclideanProductCoordinates (split)
open KFCausalWidthGaussianSecondInput (density firstOutput)
open KFCausalClockFloorRelativeShift (inverse argument relative scale)
open KFCausalComplexClockInverse (complexInverse complexInverse_real)
open KFCausalClockFloorPairedStraightening (clockInverse)
open KFCausalPhysicalReciprocalNormalization (normalize coupling)
open KFCausalComplexQuadraticPerturbation (quadratic)
open KFCausalComplexShearPerturbation (flow rotatedFlow)
open KFCausalNormalizedComplexRotation (rotationIsometry physical_rotation)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive groundWidth_matching)
open KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero)
open KFCausalChargeRotatedSecondInput (rotatedPoint)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalBroadPairedGaussianSecondInput (mixedMap_clock normalize_mixedMap)
open KFCausalWidthGaussianShearIdentity (packet_flow_normalize)
open KFCausalGaussianPhysicalShearIdentity (quadratic_rotation)
open KFCausalSingleGaussianNormalizedDensity (rotated_clock argument_clock)
open KFCausalTwoShearClockQuotient (shift)
open KFCausalWidthGaussianHolomorphicQuotient (numerator baselineVector targetVector)

theorem density_flow (ε h a w : ℝ) (hh : h ≠ 0) (hw : 0 < w) (x : Product) :
    density ε h a w x = ((Real.pi/groundWidth h:ℝ):ℂ)*
      Complex.exp (-inverse ε (-h) (x.2 0))*
      Complex.exp (-(a:ℂ)*(argument ε (-h) (x.2 0))^2)*
      Complex.exp (-quadratic (fun i => flow (coupling (groundWidth h) w)
        (relative ε (-h) (x.2 0))
        (normalize (groundWidth h) w (momentumScale h) ((split 2 4).symm x)) i)) := by
  have hp := packet_flow_normalize (groundWidth h) w (momentumScale h)
    (groundWidth_positive h hh) hw (groundWidth_matching h hh) (relative ε (-h) (x.2 0)) x
  change Complex.exp (-KFCausalShiftedPhysicalFourierSlices.radius
    ((groundWidth h:ℂ)*(scale ε (-h) (x.2 0))^2) w x.1 x.2)*
    KFCausalShiftedNarrowFourierSlices.neutralPacket (groundWidth h/32)
      (scale ε (-h) (x.2 0)) 0 1 x.2 = _ at hp
  unfold density KFCausalVacuumMixedClockNormalization.normalizedClock
    KFCausalClockFloorCoherentStrip.clockPhase KFCausalClockFloorFullGaussian.clockFactor
    KFCausalClockFloorInvariantTrial.neutralWidth
  simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one]
  rw [Complex.ofReal_div]
  calc
    _ = ((Real.pi:ℂ)/(groundWidth h:ℂ))*Complex.exp (-inverse ε (-h) (x.2 0))*
      Complex.exp (-(a:ℂ)*(argument ε (-h) (x.2 0))^2)*
      (Complex.exp (-KFCausalShiftedPhysicalFourierSlices.radius
        ((groundWidth h:ℂ)*(scale ε (-h) (x.2 0))^2) w x.1 x.2)*
        KFCausalShiftedNarrowFourierSlices.neutralPacket (groundWidth h/32)
          (scale ε (-h) (x.2 0)) 0 1 x.2) := by ring
    _ = _ := by rw [hp]

theorem density_numerator (ε : ℝ) (hε : 0 < ε) (h a w : ℝ) (hh : h ≠ 0) (hw : 1 ≤ w)
    (θ : ℝ) (x : Product) :
    ((Real.exp (clockInverse ε hε x.2)+ε:ℝ):ℂ)⁻¹*
      density ε h a w (rotatedPoint h hh θ (mixedMap ε hε x)) =
      numerator ε h a (groundWidth h) w (momentumScale h) θ (x.2 0:ℂ) ((split 2 4).symm x) := by
  have hs : complexInverse ε (x.2 0:ℂ)=(clockInverse ε hε x.2:ℂ) :=
    complexInverse_real ε hε _
  have hi : inverse ε (-h) (clockInverse ε hε x.2)=complexInverse ε (shift h (x.2 0:ℂ)) := by
    rw [inverse,argument_clock ε hε h x]
  have hn : normalize (groundWidth h) w (momentumScale h)
      ((split 2 4).symm (rotatedPoint h hh θ (mixedMap ε hε x))) =
      rotationIsometry θ (baselineVector ε (groundWidth h) w (momentumScale h) (x.2 0:ℂ)
        ((split 2 4).symm x)) := by
    rw [rotatedPoint,MeasurableEquiv.symm_apply_apply,physical_rotation,
      normalize_mixedMap ε hε (groundWidth h) w (momentumScale h)
        (groundWidth_positive h hh) (lt_of_lt_of_le zero_lt_one hw)]
    simp only [baselineVector,hs]
  have hq (z : ℂ) (v : KFCausalComplexShearPerturbation.Space) :
      quadratic (fun i => flow (coupling (groundWidth h) w) z (rotationIsometry θ v) i)=
        quadratic (fun i => rotatedFlow (rotationIsometry θ) (coupling (groundWidth h) w) z v i) := by
    exact (quadratic_rotation (-θ) (flow (coupling (groundWidth h) w) z (rotationIsometry θ v))).symm
  rw [density_flow ε h a w hh (lt_of_lt_of_le zero_lt_one hw),rotated_clock ε hε h hh θ x,hn,hq]
  simp only [numerator,targetVector,KFCausalClockFloorComplexDefect.complexClock,
    relative,hi,argument_clock ε hε h x,hs,Complex.ofReal_exp,Complex.ofReal_add]
  ring

theorem rotated_second_input_coe (ε : ℝ) (hε : 0 < ε) (h a w : ℝ) (hh : h ≠ 0) (hw : 1 ≤ w)
    (ha : 0 < a) (hb : |h| ≤ Real.pi*ε/3) (θ : ℝ) :
    KFCausalClockFloorMixedRadial.clockMixed ε hε (KFCausalClockFloorBoundedInverse.inverseL ε hε
      (KFCausalPhysicalCircleAction.action h hh θ (firstOutput ε h a w hε hh ha hw hb))) =ᵐ[volume]
      fun x => numerator ε h a (groundWidth h) w (momentumScale h) θ
        (x.2 0:ℂ) ((split 2 4).symm x) := by
  filter_upwards [KFCausalWidthGaussianSecondInput.rotated_second_input ε h a w hε hh ha hw hb θ]
    with x hx
  exact hx.trans (density_numerator ε hε h a w hh hw θ x)

#print axioms density_flow
#print axioms density_numerator
#print axioms rotated_second_input_coe
end
end UnifiedTheory.Audit.KFCausalWidthGaussianNormalizedDensity

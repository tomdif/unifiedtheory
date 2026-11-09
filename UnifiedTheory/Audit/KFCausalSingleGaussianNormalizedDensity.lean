/- Exact normalized complex-shear representative of the actual Gaussian
first square after arbitrary charge rotation and second clock dressing. -/
import UnifiedTheory.Audit.KFCausalSingleGaussianSecondInput
import UnifiedTheory.Audit.KFCausalGaussianPhysicalShearIdentity
import UnifiedTheory.Audit.KFCausalBroadPairedGaussianSecondInput
import UnifiedTheory.Audit.KFCausalSingleGaussianHolomorphicQuotient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalSingleGaussianNormalizedDensity
noncomputable section
open MeasureTheory
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalEuclideanProductCoordinates (split)
open KFCausalSingleGaussianSecondInput (density firstOutput)
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
open KFCausalGaussianPhysicalShearIdentity (packet_flow_normalize quadratic_rotation)
open KFCausalTwoShearClockQuotient (shift)
open KFCausalSingleGaussianHolomorphicQuotient (numerator baselineVector targetVector)

theorem density_flow (ε h a : ℝ) (hh : h ≠ 0) (x : Product) :
    density ε h a x = ((Real.pi/groundWidth h:ℝ):ℂ)*
      Complex.exp (-inverse ε (-h) (x.2 0))*
      Complex.exp (-(a:ℂ)*(argument ε (-h) (x.2 0))^2)*
      Complex.exp (-quadratic (fun i => flow (coupling (groundWidth h) 1)
        (relative ε (-h) (x.2 0))
        (normalize (groundWidth h) 1 (momentumScale h) ((split 2 4).symm x)) i)) := by
  have hp := packet_flow_normalize (groundWidth h) (momentumScale h)
    (groundWidth_positive h hh) (groundWidth_matching h hh) (relative ε (-h) (x.2 0)) x
  change Complex.exp (-KFCausalShiftedPhysicalFourierSlices.radius
    ((groundWidth h:ℂ)*(scale ε (-h) (x.2 0))^2) 1 x.1 x.2)*
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
        ((groundWidth h:ℂ)*(scale ε (-h) (x.2 0))^2) 1 x.1 x.2)*
        KFCausalShiftedNarrowFourierSlices.neutralPacket (groundWidth h/32)
          (scale ε (-h) (x.2 0)) 0 1 x.2) := by ring
    _ = _ := by rw [hp]

theorem rotated_clock (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (θ : ℝ) (x : Product) :
    (rotatedPoint h hh θ (mixedMap ε hε x)).2 0=clockInverse ε hε x.2 := by
  change KFCausalNormalizedChargeFlow.flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) θ
    ((split 2 4).symm (mixedMap ε hε x)) (.inr 0)=_
  rw [KFCausalNormalizedChargeFlow.flow_clock]
  exact mixedMap_clock ε hε x

theorem argument_clock (ε : ℝ) (hε : 0 < ε) (h : ℝ) (x : Product) :
    argument ε (-h) (clockInverse ε hε x.2)=shift h (x.2 0:ℂ) := by
  have hc : KFCausalRegularizedLongitudinalChart.chart ε (clockInverse ε hε x.2)=x.2 0 :=
    (KFCausalRegularizedLongitudinalChart.chartIso ε hε).apply_symm_apply _
  simp only [argument,hc,shift,Complex.ofReal_neg]
  ring

theorem density_numerator (ε : ℝ) (hε : 0 < ε) (h a : ℝ) (hh : h ≠ 0)
    (θ : ℝ) (x : Product) :
    ((Real.exp (clockInverse ε hε x.2)+ε:ℝ):ℂ)⁻¹*
      density ε h a (rotatedPoint h hh θ (mixedMap ε hε x)) =
      numerator ε h a (groundWidth h) (momentumScale h) θ (x.2 0:ℂ) ((split 2 4).symm x) := by
  have hs : complexInverse ε (x.2 0:ℂ)=(clockInverse ε hε x.2:ℂ) :=
    complexInverse_real ε hε _
  have hi : inverse ε (-h) (clockInverse ε hε x.2)=complexInverse ε (shift h (x.2 0:ℂ)) := by
    rw [inverse,argument_clock ε hε h x]
  have hn : normalize (groundWidth h) 1 (momentumScale h)
      ((split 2 4).symm (rotatedPoint h hh θ (mixedMap ε hε x))) =
      rotationIsometry θ (baselineVector ε (groundWidth h) (momentumScale h) (x.2 0:ℂ)
        ((split 2 4).symm x)) := by
    rw [rotatedPoint,MeasurableEquiv.symm_apply_apply,physical_rotation,
      normalize_mixedMap ε hε (groundWidth h) 1 (momentumScale h)
        (groundWidth_positive h hh) (by norm_num)]
    simp only [baselineVector,hs]
  have hq (z : ℂ) (v : KFCausalComplexShearPerturbation.Space) :
      quadratic (fun i => flow (coupling (groundWidth h) 1) z (rotationIsometry θ v) i)=
        quadratic (fun i => rotatedFlow (rotationIsometry θ) (coupling (groundWidth h) 1) z v i) := by
    exact (quadratic_rotation (-θ) (flow (coupling (groundWidth h) 1) z (rotationIsometry θ v))).symm
  rw [density_flow ε h a hh,rotated_clock ε hε h hh θ x,hn,hq]
  simp only [numerator,targetVector,KFCausalClockFloorComplexDefect.complexClock,
    relative,hi,argument_clock ε hε h x,hs,Complex.ofReal_exp,Complex.ofReal_add]
  ring

theorem rotated_second_input_coe (ε : ℝ) (hε : 0 < ε) (h a : ℝ) (hh : h ≠ 0)
    (ha : 0 < a) (hb : |h| ≤ Real.pi*ε/3) (θ : ℝ) :
    KFCausalClockFloorMixedRadial.clockMixed ε hε (KFCausalClockFloorBoundedInverse.inverseL ε hε
      (KFCausalPhysicalCircleAction.action h hh θ (firstOutput ε h a hε hh ha hb))) =ᵐ[volume]
      fun x => numerator ε h a (groundWidth h) (momentumScale h) θ
        (x.2 0:ℂ) ((split 2 4).symm x) := by
  filter_upwards [KFCausalSingleGaussianSecondInput.rotated_second_input ε h a hε hh ha hb θ]
    with x hx
  exact hx.trans (density_numerator ε hε h a hh θ x)

#print axioms density_flow
#print axioms rotated_clock
#print axioms argument_clock
#print axioms density_numerator
#print axioms rotated_second_input_coe
end
end UnifiedTheory.Audit.KFCausalSingleGaussianNormalizedDensity

/- The actual Fourier output profile, after the real mixed clock chart,
equals the explicit holomorphic broad baseline at the half-clock shift.
Every clock prefactor and transverse shear is cancelled algebraically. -/
import UnifiedTheory.Audit.KFCausalBroadPairedGaussianOutputFourier
import UnifiedTheory.Audit.KFCausalIndependentRadialComplexBaseline
import UnifiedTheory.Audit.KFCausalBroadPairedGaussianSecondInput

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalBroadPairedGaussianOutputBaseline
noncomputable section
open KFCausalEuclideanProductCoordinates (Block split)
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalClockFloorPairedStraightening (clockInverse dilation)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalClockFloorMixedCoordinates (mixedWeight)
open KFCausalClockFloorRelativeShift (argument inverse relative scale)
open KFCausalClockFloorShearBounds (complexScale)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open KFCausalShiftedNarrowFourierGeometry (radius neutral broadRadius)
open KFCausalBroadPairedGaussianOutputFourier (transformed)
open KFCausalIndependentRadialHolomorphicQuotient (baseline)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalTwoShearClockQuotient (shift)

private theorem argument_clock (ε h : ℝ) (hε : 0<ε) (x : Product) :
    argument ε (-h/2) (clockInverse ε hε x.2)=shift (h/2) (x.2 0:ℂ) := by
  have hc : KFCausalRegularizedLongitudinalChart.chart ε (clockInverse ε hε x.2)=x.2 0 :=
    (KFCausalRegularizedLongitudinalChart.chartIso ε hε).apply_symm_apply _
  unfold argument shift
  rw [hc]
  push_cast
  ring

theorem scale_product (ε h : ℝ) (hε : 0<ε) (x : Product) :
    scale ε (-h/2) (clockInverse ε hε x.2)*(Real.exp (clockInverse ε hε x.2/2):ℂ)=
      Complex.exp (complexInverse ε (shift (h/2) (x.2 0:ℂ))/2) := by
  unfold scale complexScale relative inverse
  rw [argument_clock]
  rw [show (Real.exp (clockInverse ε hε x.2/2):ℂ)=
      Complex.exp ((clockInverse ε hε x.2:ℂ)/2) by simp]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem neutral_mixedMap (ε h : ℝ) (hε : 0<ε) (x : Product) :
    neutral (scale ε (-h/2) (clockInverse ε hε x.2)) (mixedMap ε hε x).2 =
      neutral (Complex.exp (complexInverse ε (shift (h/2) (x.2 0:ℂ))/2)) x.2 := by
  rw [← scale_product ε h hε x]
  simp only [neutral,mixedMap,KFCausalClockFloorSpectatorChart.backward,
    KFCausalClockFloorSpectatorChart.changeClock,KFCausalClockFloorSpectatorChart.flow]
  dsimp only [clockInverse]
  push_cast
  ring

theorem radius_mixedMap (ε h α : ℝ) (hε : 0<ε) (x : Product) :
    radius ((α:ℂ)*(scale ε (-h/2) (clockInverse ε hε x.2))^2)
      (mixedMap ε hε x).1 (mixedMap ε hε x).2 =
      radius ((α:ℂ)*(Complex.exp (complexInverse ε (shift (h/2) (x.2 0:ℂ))/2))^2)
        x.1 x.2 := by
  rw [← scale_product ε h hε x]
  simp only [radius,broadRadius,mixedMap,dilation,
    KFCausalClockFloorSpectatorChart.backward,KFCausalClockFloorSpectatorChart.changeClock,
    KFCausalClockFloorSpectatorChart.flow,
    norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (Real.exp_pos _)]
  dsimp only [clockInverse]
  push_cast
  simp only [mul_pow,div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

theorem clock_cancellation (ε h a : ℝ) (hε : 0<ε) (x : Product) :
    mixedWeight ε hε x*clockAmplitude ε a 0 (-h/2) (clockInverse ε hε x.2)/
        (scale ε (-h/2) (clockInverse ε hε x.2))^2 =
      Complex.exp (-complexInverse ε (shift (h/2) (x.2 0:ℂ)))*
        Complex.exp (-(a:ℂ)*(shift (h/2) (x.2 0:ℂ))^2) := by
  let s := clockInverse ε hε x.2
  let S := complexInverse ε (shift (h/2) (x.2 0:ℂ))
  have hs : (Real.sqrt (Real.exp s+ε):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (add_pos (Real.exp_pos s) hε)).ne'
  have hr : (scale ε (-h/2) s)^2=Complex.exp (S-(s:ℂ)) := by
    dsimp [s,S]
    unfold scale complexScale relative inverse
    rw [argument_clock,pow_two,← Complex.exp_add]
    congr 1
    ring
  have he : (Real.exp (-s):ℂ)/(scale ε (-h/2) s)^2=Complex.exp (-S) := by
    rw [hr,div_eq_mul_inv,← Complex.exp_neg]
    rw [show (Real.exp (-s):ℂ)=Complex.exp (-(s:ℂ)) by simp,← Complex.exp_add]
    congr 1
    ring
  simp only [clockAmplitude,KFCausalClockFloorCoherentStrip.clockPhase,
    Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one,
    KFCausalClockFloorFullGaussian.clockFactor,argument_clock,mixedWeight,
    KFCausalClockFloorChargeTrialBridge.amplitude,Complex.ofReal_mul]
  change (Real.sqrt (Real.exp s+ε):ℂ)⁻¹*
    (((Real.sqrt (Real.exp s+ε):ℂ)*(Real.exp (-s):ℂ))*
      Complex.exp (-(a:ℂ)*(shift (h/2) (x.2 0:ℂ))^2))/(scale ε (-h/2) s)^2=_
  calc
    _ = ((Real.sqrt (Real.exp s+ε):ℂ)⁻¹*(Real.sqrt (Real.exp s+ε):ℂ))*
        ((Real.exp (-s):ℂ)/(scale ε (-h/2) s)^2)*
        Complex.exp (-(a:ℂ)*(shift (h/2) (x.2 0:ℂ))^2) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hs,one_mul,he]

theorem transformed_eq_baseline (ε h a α W wL wR c : ℝ) (hε : 0<ε)
    (hα : 0<α) (hW : 0<W) (hL : 0<wL) (hR : 0<wR)
    (hmatch : Real.pi^2/α=α*c^2) (x : Product) :
    mixedWeight ε hε x*transformed ε (a/2) α (1/(4*W)) h (mixedMap ε hε x)=
      baseline ε a α W wL wR c (shift (h/2) (x.2 0:ℂ)) ((split 2 4).symm x) := by
  rw [KFCausalIndependentRadialComplexBaseline.baseline_formula
    ε a α W wL wR c hα hW hL hR hmatch]
  unfold transformed
  rw [KFCausalBroadPairedGaussianSecondInput.mixedMap_clock,
    radius_mixedMap ε h α hε x,neutral_mixedMap ε h hε x]
  have hβ : α*(1/(4*W))/128=α/(512*W) := by ring
  rw [hβ]
  have hc := clock_cancellation ε h (a/2) hε x
  have hp : ((Real.pi/(4*W*α):ℝ):ℂ)=((Real.pi:ℂ)/((α:ℂ)))*(1/(4*W):ℝ) := by
    push_cast
    ring
  rw [hp]
  calc
    _ = ((Real.pi:ℂ)/(α:ℂ))*(1/(4*W):ℝ)*
        (mixedWeight ε hε x*clockAmplitude ε (a/2) 0 (-h/2) (clockInverse ε hε x.2)/
          (scale ε (-h/2) (clockInverse ε hε x.2))^2)*
        Complex.exp (-((1/(4*W):ℝ):ℂ)*
          radius ((α:ℂ)*(Complex.exp (complexInverse ε (shift (h/2) (x.2 0:ℂ))/2))^2) x.1 x.2-
          ((α/(512*W):ℝ):ℂ)*(neutral (Complex.exp (complexInverse ε (shift (h/2) (x.2 0:ℂ))/2)) x.2)^2) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by rw [hc]; ring

#print axioms scale_product
#print axioms neutral_mixedMap
#print axioms radius_mixedMap
#print axioms clock_cancellation
#print axioms transformed_eq_baseline
end
end UnifiedTheory.Audit.KFCausalBroadPairedGaussianOutputBaseline

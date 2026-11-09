/- Actual ordered broad Gaussian outputs in straightened clock coordinates.
The representative follows from the proved physical partial Fourier transform
and null-set-preserving clock chart, followed by exact complex Gaussian algebra.
No L2 representative is analytically continued. -/
import UnifiedTheory.Audit.KFCausalBroadPairedGaussianOutputBaseline
import UnifiedTheory.Audit.KFCausalIndependentRadialMomentExponential

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialShiftedBaseline
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates (split)
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalClockFloorMixedRadial (clockMixed clockMixed_coe)
open KFCausalClockFloorMixedChart (mixedMap_quasiMeasurePreserving)
open KFCausalBroadPairedGaussianOutputFourier (output_mixed_coe)
open KFCausalBroadPairedGaussianOutputBaseline (transformed_eq_baseline)
open KFCausalIndependentRadialHolomorphicQuotient (baseline)
open KFCausalIndependentRadialMomentExponential (baselineHalfOutput baselineOutput)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive groundWidth_matching)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalTwoShearClockQuotient (shift)

theorem output_clockMixed_coe (ε h a α W wL wR c : ℝ) (hε : 0<ε)
    (ha : 0<a) (hα : 0<α) (hW : 0<W) (hL : 0<wL) (hR : 0<wR)
    (hmatch : Real.pi^2/α=α*c^2) (hb : |h|≤2*Real.pi*ε/3) :
    clockMixed ε hε
      (KFCausalBroadPairedGaussian.output ε (a/2) α (1/(4*W))
        hε (by positivity) hα h hb) =ᵐ[volume]
      fun x : Product => baseline ε a α W wL wR c
        (shift (h/2) (x.2 0:ℂ)) ((split 2 4).symm x) := by
  have hm := (mixedMap_quasiMeasurePreserving ε hε).ae
    (output_mixed_coe ε (a/2) α (1/(4*W)) hε (by positivity) hα (by positivity) h hb)
  filter_upwards [clockMixed_coe ε hε
    (KFCausalBroadPairedGaussian.output ε (a/2) α (1/(4*W))
      hε (by positivity) hα h hb),hm] with x hx hm
  rw [hx,hm]
  exact transformed_eq_baseline ε h a α W wL wR c hε hα hW hL hR hmatch x

theorem baseline_half_coe (ε h a W wL wR : ℝ) (hε : 0<ε) (hh : h≠0)
    (ha : 0<a) (hW : 0<W) (hL : 0<wL) (hR : 0<wR) (hb : |h|≤ε/10) :
    clockMixed ε hε (baselineHalfOutput ε h a W hε hh ha hb) =ᵐ[volume]
      fun x : Product => baseline ε a (groundWidth h) W wL wR (momentumScale h)
        (shift (h/2) (x.2 0:ℂ)) ((split 2 4).symm x) := by
  have hw : |h|≤2*Real.pi*ε/3 := by
    have ht := KFCausalSingleGaussianMixedSquare.original_strip ε h hε hb
    have hp := mul_pos Real.pi_pos hε
    linarith
  exact output_clockMixed_coe ε h a (groundWidth h) W wL wR (momentumScale h)
    hε ha (groundWidth_positive h hh) hW hL hR (groundWidth_matching h hh) hw

theorem baseline_full_coe (ε h a W wL wR : ℝ) (hε : 0<ε) (hh : h≠0)
    (ha : 0<a) (hW : 0<W) (hL : 0<wL) (hR : 0<wR) (hb : |h|≤ε/10) :
    clockMixed ε hε (baselineOutput ε h a W hε hh ha hb) =ᵐ[volume]
      fun x : Product => baseline ε a (groundWidth h) W wL wR (momentumScale h)
        (shift h (x.2 0:ℂ)) ((split 2 4).symm x) := by
  have ht := output_clockMixed_coe ε (2*h) a (groundWidth h) W wL wR (momentumScale h)
    hε ha (groundWidth_positive h hh) hW hL hR (groundWidth_matching h hh)
    (KFCausalSingleGaussianMixedSquare.doubled_strip ε h hε hb)
  simpa only [show 2*h/2=h by ring] using ht

#print axioms output_clockMixed_coe
#print axioms baseline_half_coe
#print axioms baseline_full_coe
end
end UnifiedTheory.Audit.KFCausalIndependentRadialShiftedBaseline

/- The same physical broad paired Gaussian represents the baseline
for both independent target widths. Its Hilbert-space input is explicit. -/
import UnifiedTheory.Audit.KFCausalBroadPairedHolomorphicBaseline
import UnifiedTheory.Audit.KFCausalIndependentRadialHolomorphicQuotient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialBaseline
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates (split)
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalBroadPairedGaussianSecondInput
open KFCausalClockFloorPairedStraightening (clockInverse)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalClockFloorInvariantTrial (clockFunction)
open KFCausalRegularizedLongitudinalChart (chart chartIso)
open KFCausalIndependentRadialNormalization
open KFCausalPhysicalReciprocalNormalization (coupling)
open KFCausalBroadPairedHolomorphicBaseline (clock_cancellation)

theorem profile_eq_baseline (ε a α W wL wR c : ℝ) (hε : 0 < ε) (hα : 0 < α)
    (hL : 0 < wL) (hR : 0 < wR) (hW : 0 < W) (x : Product) :
    secondProfile ε (a/2) α (1/(4*W)) c hε x=
      KFCausalIndependentRadialHolomorphicQuotient.baseline ε a α W wL wR c (x.2 0:ℂ) ((split 2 4).symm x) := by
  let s := clockInverse ε hε x.2
  let Y := (split 2 4).symm (mixedMap ε hε x)
  have hchart : chart ε s=x.2 0 := (chartIso ε hε).apply_symm_apply _
  have hN := KFCausalIndependentRadialNormalization.normalize_mixedMap ε hε α wL wR c hα hR x
  have hQ := baseline_quadratic α W wL wR c hα hL hR hW Y
  unfold KFCausalIndependentRadialHolomorphicQuotient.baseline
    KFCausalIndependentRadialHolomorphicQuotient.baselineVector
  rw [KFCausalComplexClockInverse.complexInverse_real ε hε]
  change secondProfile ε (a/2) α (1/(4*W)) c hε x=
    (Real.pi/(4*W*α):ℝ)*Complex.exp (-(s:ℂ))*Complex.exp (-(a/2:ℝ)*(x.2 0:ℂ)^2)*
      Complex.exp (-KFCausalComplexQuadraticPerturbation.weightedQuadratic (weights W wL wR)
        (fun i => KFCausalComplexShearPerturbation.flow (coupling α wR) (s:ℂ)
          (normalize α wL wR c ((split 2 4).symm x)) i))
  rw [← hN,hQ]
  change ((Real.exp s+ε:ℝ):ℂ)⁻¹*
    ((Real.pi*(1/(4*W))/α:ℝ)*clockFunction ε (a/2) s*
      Complex.exp (-((α*(1/(4*W))*KFCausalChargeGaussianGeometry.radius c Y+
        α*(1/(4*W))/128*(Y (.inr 3))^2:ℝ):ℂ)))= _
  have hf : Real.pi*(1/(4*W))/α=Real.pi/(4*W*α) := by ring
  have he : α*(1/(4*W))*KFCausalChargeGaussianGeometry.radius c Y+
      α*(1/(4*W))/128*(Y (.inr 3))^2=
      α/(4*W)*KFCausalChargeGaussianGeometry.radius c Y+
        α/(512*W)*(Y (.inr 3))^2 := by ring
  rw [hf,he]
  have hclock := clock_cancellation ε (a/2) s hε
  rw [hchart] at hclock
  linear_combination
    (Real.pi/(4*W*α):ℝ)*Complex.exp (-((α/(4*W)*KFCausalChargeGaussianGeometry.radius c Y+
      α/(512*W)*(Y (.inr 3))^2:ℝ):ℂ))*hclock

theorem baseline_second_input_coe (ε a α W wL wR c : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hL : 0 < wL) (hR : 0 < wR) (hW : 0 < W) (hmatch : Real.pi^2/α=α*c^2) :
    KFCausalClockFloorMixedRadial.clockMixed ε hε
      (KFCausalClockFloorBoundedInverse.inverseL ε hε
        (KFCausalBroadPairedGaussian.state ε (a/2) α (1/(4*W)) hε (by positivity) hα (by positivity))) =ᵐ[volume]
      fun x : Product => KFCausalIndependentRadialHolomorphicQuotient.baseline
        ε a α W wL wR c (x.2 0:ℂ) ((split 2 4).symm x) := by
  filter_upwards [paired_second_input_coe ε (a/2) α (1/(4*W)) c hε (by positivity) hα (by positivity) hmatch]
    with x hx
  exact hx.trans (profile_eq_baseline ε a α W wL wR c hε hα hL hR hW x)

#print axioms profile_eq_baseline
#print axioms baseline_second_input_coe
end
end UnifiedTheory.Audit.KFCausalIndependentRadialBaseline

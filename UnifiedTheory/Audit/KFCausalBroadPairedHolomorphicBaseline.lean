/- Exact identification of the broad paired baseline with the direct
holomorphic Gaussian formula used by the mixed-square multiplier. -/
import UnifiedTheory.Audit.KFCausalBroadPairedGaussianSecondInput
import UnifiedTheory.Audit.KFCausalSingleGaussianHolomorphicQuotient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalBroadPairedHolomorphicBaseline
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates (split)
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalBroadPairedGaussianSecondInput
open KFCausalClockFloorPairedStraightening (clockInverse)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalClockFloorInvariantTrial (clockFunction realClock)
open KFCausalRegularizedLongitudinalChart (chart chartIso)
open KFCausalPhysicalReciprocalNormalization

theorem clock_cancellation (ε a s : ℝ) (hε : 0 < ε) :
    ((Real.exp s+ε:ℝ):ℂ)⁻¹*clockFunction ε a s=
      Complex.exp (-(s:ℂ))*Complex.exp (-(a:ℂ)*(chart ε s:ℂ)^2) := by
  have hd : Real.exp s+ε ≠ 0 := ne_of_gt (add_pos (Real.exp_pos s) hε)
  have hs : Real.exp s ≠ 0 := ne_of_gt (Real.exp_pos s)
  have hr : (Real.exp s+ε)⁻¹*((1+ε*Real.exp (-s))*Real.exp (-a*(chart ε s)^2))=
      Real.exp (-s)*Real.exp (-a*(chart ε s)^2) := by
    rw [Real.exp_neg]
    field_simp [hd,hs]
  have hc := congrArg (fun t : ℝ => (t:ℂ)) hr
  simpa [clockFunction,realClock] using hc

theorem profile_eq_baseline (ε a α c : ℝ) (hε : 0 < ε) (hα : 0 < α) (x : Product) :
    secondProfile ε (a/2) α (1/4) c hε x=
      KFCausalSingleGaussianHolomorphicQuotient.baseline ε a α c (x.2 0:ℂ) ((split 2 4).symm x) := by
  let s := clockInverse ε hε x.2
  let Y := (split 2 4).symm (mixedMap ε hε x)
  have hchart : chart ε s=x.2 0 := (chartIso ε hε).apply_symm_apply _
  have hN := normalize_mixedMap ε hε α 1 c hα (by norm_num) x
  have hQ := baseline_quadratic α 1 1 c hα (by norm_num) (by norm_num) Y
  unfold KFCausalSingleGaussianHolomorphicQuotient.baseline
    KFCausalSingleGaussianHolomorphicQuotient.baselineVector
  rw [KFCausalComplexClockInverse.complexInverse_real ε hε]
  change secondProfile ε (a/2) α (1/4) c hε x=
    (Real.pi/(4*α):ℝ)*Complex.exp (-(s:ℂ))*Complex.exp (-(a/2:ℝ)*(x.2 0:ℂ)^2)*
      Complex.exp (-KFCausalComplexQuadraticPerturbation.weightedQuadratic (weights 1 1)
        (fun i => KFCausalComplexShearPerturbation.flow (coupling α 1) (s:ℂ)
          (normalize α 1 c ((split 2 4).symm x)) i))
  rw [← hN,hQ]
  change ((Real.exp s+ε:ℝ):ℂ)⁻¹*
    ((Real.pi*(1/4)/α:ℝ)*clockFunction ε (a/2) s*
      Complex.exp (-((α*(1/4)*KFCausalChargeGaussianGeometry.radius c Y+
        α*(1/4)/128*(Y (.inr 3))^2:ℝ):ℂ)))= _
  have hf : Real.pi*(1/4)/α=Real.pi/(4*α) := by ring
  have he : α*(1/4)*KFCausalChargeGaussianGeometry.radius c Y+
      α*(1/4)/128*(Y (.inr 3))^2=
      α/(4*1)*KFCausalChargeGaussianGeometry.radius c Y+
        α/(512*1)*(Y (.inr 3))^2 := by ring
  rw [hf,he]
  have hclock := clock_cancellation ε (a/2) s hε
  rw [hchart] at hclock
  linear_combination
    (Real.pi/(4*α):ℝ)*Complex.exp (-((α/(4*1)*KFCausalChargeGaussianGeometry.radius c Y+
      α/(512*1)*(Y (.inr 3))^2:ℝ):ℂ))*hclock

theorem baseline_second_input_coe (ε a α c : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hmatch : Real.pi^2/α=α*c^2) :
    KFCausalClockFloorMixedRadial.clockMixed ε hε
      (KFCausalClockFloorBoundedInverse.inverseL ε hε
        (KFCausalBroadPairedGaussian.state ε (a/2) α (1/4) hε (by positivity) hα (by norm_num))) =ᵐ[volume]
      fun x : Product => KFCausalSingleGaussianHolomorphicQuotient.baseline
        ε a α c (x.2 0:ℂ) ((split 2 4).symm x) := by
  filter_upwards [paired_second_input_coe ε (a/2) α (1/4) c hε (by positivity) hα (by norm_num) hmatch]
    with x hx
  exact hx.trans (profile_eq_baseline ε a α c hε hα x)

#print axioms clock_cancellation
#print axioms profile_eq_baseline
#print axioms baseline_second_input_coe
end
end UnifiedTheory.Audit.KFCausalBroadPairedHolomorphicBaseline

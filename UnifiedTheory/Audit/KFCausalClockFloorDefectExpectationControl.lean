/- A quantitative local Lipschitz estimate for clock-defect expectations
under the actual unbounded averaged evolution. It follows from cutoff-
uniform Ehrenfest estimates and the proved all-L2 strong dynamics limit. -/
import UnifiedTheory.Audit.KFCausalClockFloorEhrenfestVelocity
import UnifiedTheory.Audit.KFCausalClockFloorAveragedSequenceConvergence
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectExpectationControl
noncomputable section
open Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorEhrenfestVelocity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy timeEnergy_nonneg)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSequenceConvergence
open UnifiedTheory.Audit.KFCausalClockFloorAveragedCountableLimit (cutoff cutoff_pos)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hne : hbar ≠ 0)
  (hh : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "J" => embedding ε hε hbar hne hh mass2 quartic vacuum 0
local notation "U" => evolution ε hε hbar hne hh mass2 quartic vacuum
local notation "D" => defectOperator ε hε

theorem bounded_expectation_lipschitz (a : ℝ) (ha : 0 < a) (s T r t : ℝ)
    (hr : |r-s| ≤ T) (ht : |t-s| ≤ T)
    (w : FormSpace ε hε hbar hne hh mass2 quartic vacuum 0) :
    |expectationCurve ε hε hbar hne hh mass2 quartic vacuum a ha s t (J w)-
      expectationCurve ε hε hbar hne hh mass2 quartic vacuum a ha s r (J w)| ≤
      ((20*|hbar|/ε^2+1/ε)*Real.exp (2*T)*timeEnergy ε hε hbar hne hh mass2 quartic vacuum s w)*|t-r| := by
  have hE := timeEnergy_nonneg ε hε hbar hne hh mass2 quartic vacuum s w
  have hz (z : ℝ) (hz : z ∈ uIcc r t) : |z-s| ≤ T := by
    rcases mem_uIcc.mp hz with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact abs_le.mpr ⟨by linarith [(abs_le.mp hr).1],by linarith [(abs_le.mp ht).2]⟩
    · exact abs_le.mpr ⟨by linarith [(abs_le.mp ht).1],by linarith [(abs_le.mp hr).2]⟩
  have h := (convex_uIcc r t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (expectationCurve_derivative ε hε hbar hne hh mass2 quartic vacuum a ha s z (J w)).hasDerivWithinAt)
    (fun z hzt => show ‖quantumRate ε hε hbar hne hh mass2 quartic vacuum a ha s z (J w)‖ ≤
        (20*|hbar|/ε^2+1/ε)*Real.exp (2*T)*timeEnergy ε hε hbar hne hh mass2 quartic vacuum s w by
      rw [Real.norm_eq_abs]
      apply (uniform_quantumRate_bound ε hε hbar hne hh mass2 quartic vacuum a ha s z w).trans
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hE
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr (by linarith [hz z hzt]))
    left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using h

theorem expectation_cutoff_limit (s t : ℝ) (f : Hilbert) :
    Tendsto (fun n => expectationCurve ε hε hbar hne hh mass2 quartic vacuum
      (cutoff n) (cutoff_pos n) s t f) atTop
      (𝓝 ((inner ℂ (U s t f) (D (U s t f))).re)) := by
  have hv := cutoff_dynamics_strong_limit ε hε hbar hne hh mass2 quartic vacuum s t f
  have hd := ((D).continuous.tendsto _).comp hv
  exact Complex.continuous_re.tendsto _ |>.comp (hv.inner hd)

theorem evolution_expectation_lipschitz (s T r t : ℝ)
    (hr : |r-s| ≤ T) (ht : |t-s| ≤ T)
    (w : FormSpace ε hε hbar hne hh mass2 quartic vacuum 0) :
    |(inner ℂ (U s t (J w)) (D (U s t (J w)))).re-
      (inner ℂ (U s r (J w)) (D (U s r (J w)))).re| ≤
      ((20*|hbar|/ε^2+1/ε)*Real.exp (2*T)*timeEnergy ε hε hbar hne hh mass2 quartic vacuum s w)*|t-r| := by
  have hl := ((expectation_cutoff_limit ε hε hbar hne hh mass2 quartic vacuum s t (J w)).sub
    (expectation_cutoff_limit ε hε hbar hne hh mass2 quartic vacuum s r (J w))).abs
  exact le_of_tendsto hl (Filter.Eventually.of_forall (fun n =>
    bounded_expectation_lipschitz ε hε hbar hne hh mass2 quartic vacuum
      (cutoff n) (cutoff_pos n) s T r t hr ht w))

#print axioms bounded_expectation_lipschitz
#print axioms expectation_cutoff_limit
#print axioms evolution_expectation_lipschitz

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectExpectationControl

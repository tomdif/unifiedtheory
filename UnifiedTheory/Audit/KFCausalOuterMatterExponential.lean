/- The exact exponential half steps surrounding an outer physical matter
insertion, on the original vacuum or matter second output. -/
import UnifiedTheory.Audit.KFCausalOuterMatterHalfField
import UnifiedTheory.Audit.KFCausalMatterHalfStepAssembly
import UnifiedTheory.Audit.KFCausalVacuumMatterInput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalOuterMatterExponential
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorBoundedInverse (inverseL ordered_graph_iff)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalClockFloorVacuumSquare (exponential_rescale)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalPhysicalCircleAction (action)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive groundWidth_matching)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalSourcedWidthMatterSquare (baseline baselineOutput)
open KFCausalOuterMatterHalfField (multiplierAction halfOutput)
open KFCausalVacuumMatterInput (innerDegree innerOutput)
open KFCausalSingleGaussianMixedSquare (original_strip doubled_strip)

variable (ε h a W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (k m : ℕ) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hw : 1 ≤ w)
  (hW : w ≤ W) (hb : |h| ≤ ε/10)
local notation "α" => groundWidth h
local notation "c" => momentumScale h
local notation "hα" => groundWidth_positive h hh
local notation "hW₀" => lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hw) hW

include hε hb in
theorem half_baseline_strip : |h| ≤ 2*Real.pi*ε/3 := by
  have hs := original_strip ε h hε hb
  have hp := mul_pos Real.pi_pos hε
  linarith

def baselineHalfOutput : Hilbert :=
  KFCausalBroadPairedGaussian.output ε (a/2) α (1/(4*W)) hε (by positivity) hα h
    (half_baseline_strip ε h hε hb)

def halfState (θ : ℝ) : Hilbert :=
  halfOutput ε h a W w C p b P k m hε hh ha hw hW hb θ
    (baselineHalfOutput ε h a W hε hh ha hb)

def fullState (θ : ℝ) : Hilbert :=
  multiplierAction ε h a W w C p b P k m hε hh ha hw hW hb θ (-h) (by simp)
    (baselineOutput ε h a W hε hh ha hb)

theorem half_graph (θ : ℝ) :
    (multiplierAction ε h a W w C p b P k m hε hh ha hw hW hb θ 0 (by simp)
      (inverseL ε hε (baseline ε h a W w hε hh ha hw hW)),
      halfState ε h a W w C p b P k m hε hh ha hw hW hb θ) ∈
      (longitudinalExponential ε hε h (1/2)).graph := by
  apply KFCausalOuterMatterHalfField.multiplierAction_graph
  exact (ordered_graph_iff ε hε h _ _).mp
    (KFCausalBroadPairedGaussian.output_graph ε (a/2) α (1/(4*W)) hε
      (by positivity) hα (by have := hW₀; positivity) h (half_baseline_strip ε h hε hb))

theorem full_graph (θ : ℝ) :
    (multiplierAction ε h a W w C p b P k m hε hh ha hw hW hb θ 0 (by simp)
      (inverseL ε hε (baseline ε h a W w hε hh ha hw hW)),
      fullState ε h a W w C p b P k m hε hh ha hw hW hb θ) ∈
      (longitudinalExponential ε hε h 1).graph := by
  have hg := KFCausalOuterMatterHalfField.multiplierAction_graph
    ε h a W w C p b P k m hε hh ha hw hW hb θ (2*h)
    (by rw [show -(2*h)/2=-h by ring,abs_neg]) _ _
    ((ordered_graph_iff ε hε (2*h) _ _).mp
      (KFCausalBroadPairedGaussian.output_graph ε (a/2) α (1/(4*W)) hε
        (by positivity) hα (by have := hW₀; positivity) (2*h) (doubled_strip ε h hε hb)))
  have he := (exponential_rescale ε hε h 2 (1/2) _ _).mp hg
  simpa only [show -(2*h)/2=-h by ring,show (1/2:ℝ)*2=1 by norm_num] using he

theorem second_half_graph (θ : ℝ) :
    (halfState ε h a W w C p b P k m hε hh ha hw hW hb θ,
      fullState ε h a W w C p b P k m hε hh ha hw hW hb θ) ∈
      (longitudinalExponential ε hε h (1/2)).graph :=
  KFCausalMatterHalfStepAssembly.second_half_graph ε hε h _ _ _
    (half_graph ε h a W w C p b P k m hε hh ha hw hW hb θ)
    (full_graph ε h a W w C p b P k m hε hh ha hw hW hb θ)

theorem actual_input (i : Option (Fin 2)) (θ : ℝ) :
    multiplierAction ε h a W w C p b P (innerDegree i) 0 hε hh ha hw hW hb θ 0 (by simp)
      (inverseL ε hε (baseline ε h a W w hε hh ha hw hW)) =
      inverseL ε hε (action h hh θ (innerOutput ε h a w C p b P hε hh ha hw hb i)) := by
  apply (clockMixed ε hε).injective
  apply Lp.ext
  filter_upwards [KFCausalOuterMatterHalfField.multiplierAction_clockMixed
    ε h a W w C p b P (innerDegree i) 0 hε hh ha hw hW hb θ 0 (by simp)
      (inverseL ε hε (baseline ε h a W w hε hh ha hw hW)),
    KFCausalBroadWidthHolomorphicBaseline.baseline_second_input_coe ε a α W w c
      hε ha hα (zero_lt_one.trans_le hw) hW₀ (groundWidth_matching h hh),
    KFCausalVacuumMatterInput.rotated_second_input_coe ε h a w C p b P
      hε hh ha hw hb i θ] with x hx hbase hi
  rw [hx,hi,baseline,hbase]
  simp only [Complex.ofReal_zero,zero_mul,add_zero]
  rw [KFCausalOuterMatterMultiplier.multiplier_mul_baseline
    ε h a α W w c θ C p b P (innerDegree i) 0 (hW₀).ne',pow_zero,one_mul]

theorem actual_half_graph (i : Option (Fin 2)) (θ : ℝ) :
    (inverseL ε hε (action h hh θ (innerOutput ε h a w C p b P hε hh ha hw hb i)),
      halfState ε h a W w C p b P (innerDegree i) 0 hε hh ha hw hW hb θ) ∈
      (longitudinalExponential ε hε h (1/2)).graph := by
  have hg := half_graph ε h a W w C p b P (innerDegree i) 0 hε hh ha hw hW hb θ
  rwa [actual_input ε h a W w C p b P hε hh ha hw hW hb i θ] at hg

#print axioms half_baseline_strip
#print axioms half_graph
#print axioms full_graph
#print axioms second_half_graph
#print axioms actual_input
#print axioms actual_half_graph
end
end UnifiedTheory.Audit.KFCausalOuterMatterExponential

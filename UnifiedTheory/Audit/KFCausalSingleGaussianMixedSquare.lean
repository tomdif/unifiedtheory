/- An actual second vacuum-square graph for every charge rotation of the
first square of the singleton Gaussian. The narrower epsilon/10 range is
explicit. No second exponential-domain hypothesis is assumed. -/
import UnifiedTheory.Audit.KFCausalSingleGaussianNormalizedDensity
import UnifiedTheory.Audit.KFCausalSingleGaussianHolomorphicContinuity
import UnifiedTheory.Audit.KFCausalBroadPairedHolomorphicBaseline
import UnifiedTheory.Audit.KFCausalMixedStripTailAttachment

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalSingleGaussianMixedSquare
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorBoundedInverse (inverseL ordered_graph_iff)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalClockFloorVacuumSquare (square square_graph exponential_rescale)
open KFCausalPhysicalCircleAction (action)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive groundWidth_matching)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalEuclideanProductCoordinates (split)
open KFCausalSingleGaussianSecondInput (state firstOutput first_graph)
open KFCausalMixedStripTailAttachment (tailPoint normalize_tail family family_horizontal_continuous action_of_clockMixed)

theorem original_strip (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ ε/10) :
    |h| ≤ Real.pi*ε/3 := by
  have hp := mul_lt_mul_of_pos_right Real.pi_gt_three hε
  linarith

theorem doubled_strip (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ ε/10) :
    |2*h| ≤ 2*Real.pi*ε/3 := by
  have ho := original_strip ε h hε hb
  rw [abs_mul]
  norm_num
  linarith

variable (ε h a : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hb : |h| ≤ ε/10)
local notation "α" => groundWidth h
local notation "c" => momentumScale h
local notation "hα" => groundWidth_positive h hh
local notation "hb₀" => original_strip ε h hε hb

def bound : ℝ := 4*ε⁻¹*Real.exp (|h|/ε+4*a*h^2)
def multiplier (θ : ℝ) := family (KFCausalSingleGaussianHolomorphicQuotient.multiplier ε h a α c θ)

include hε hb in
private theorem horizontal_continuous (θ : ℝ) :
    ∀ y, |y| ≤ |h| → Continuous (fun w : ℝ × KFCausalEuclideanClockSplit.TailSpace =>
      multiplier ε h a θ ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2) :=
  family_horizontal_continuous _ _ (KFCausalSingleGaussianHolomorphicQuotient.multiplier_horizontal_continuous ε h a α c θ hε hb)

include hε hh ha hb in
private theorem multiplier_bound (θ : ℝ) :
    ∀ q, |q.im| ≤ |h| → ∀ z, ‖multiplier ε h a θ q z‖ ≤ bound ε h a := by
  intro q hq z
  exact KFCausalSingleGaussianHolomorphicQuotient.multiplier_bound ε h a α c θ hε hb ha.le hα q hq (tailPoint z)

def multiplierAction (θ y : ℝ) (hy : |y| ≤ |h|) : Hilbert →L[ℂ] Hilbert :=
  KFCausalMixedStripExponentialGraph.action ε hε (multiplier ε h a θ) |h| (bound ε h a)
    (horizontal_continuous ε h a hε hb θ) (KFCausalSingleGaussianHolomorphicQuotient.bound_nonnegative ε h a hε)
    (multiplier_bound ε h a hε hh ha hb θ) y hy

def baseline : Hilbert := KFCausalBroadPairedGaussian.state ε (a/2) α (1/4) hε (by positivity) hα (by norm_num)
def baselineOutput : Hilbert :=
  KFCausalBroadPairedGaussian.output ε (a/2) α (1/4) hε (by positivity) hα (2*h) (doubled_strip ε h hε hb)

theorem actual_input (θ : ℝ) :
    multiplierAction ε h a hε hh ha hb θ 0 (by simp)
      (inverseL ε hε (baseline ε h a hε hh ha)) =
      inverseL ε hε (action h hh θ (firstOutput ε h a hε hh ha hb₀)) := by
  apply action_of_clockMixed ε hε (KFCausalSingleGaussianHolomorphicQuotient.multiplier ε h a α c θ) |h| (bound ε h a)
    (horizontal_continuous ε h a hε hb θ) (KFCausalSingleGaussianHolomorphicQuotient.bound_nonnegative ε h a hε)
    (multiplier_bound ε h a hε hh ha hb θ)
  · intro q x
    simp only [KFCausalSingleGaussianHolomorphicQuotient.multiplier,KFCausalSingleGaussianHolomorphicQuotient.targetVector,KFCausalSingleGaussianHolomorphicQuotient.baselineVector,normalize_tail]
  · filter_upwards [KFCausalSingleGaussianNormalizedDensity.rotated_second_input_coe
      ε hε h a hh ha hb₀ θ,
      KFCausalBroadPairedHolomorphicBaseline.baseline_second_input_coe
        ε a α c hε ha hα (groundWidth_matching h hh)] with x hn hb
    rw [hn,baseline,hb,KFCausalSingleGaussianHolomorphicQuotient.multiplier_mul_baseline]

def exponentialOutput (θ : ℝ) : Hilbert :=
  multiplierAction ε h a hε hh ha hb θ (-h) (by simp)
    (baselineOutput ε h a hε hh ha hb)

theorem second_exponential_graph (θ : ℝ) :
    (inverseL ε hε (action h hh θ (firstOutput ε h a hε hh ha hb₀)),
      exponentialOutput ε h a hε hh ha hb θ) ∈
      (longitudinalExponential ε hε h 1).graph := by
  have hbase : (inverseL ε hε (baseline ε h a hε hh ha),baselineOutput ε h a hε hh ha hb) ∈
      (longitudinalExponential ε hε (2*h) (1/2)).graph :=
    (ordered_graph_iff ε hε (2*h) _ _).mp
      (KFCausalBroadPairedGaussian.output_graph ε (a/2) α (1/4) hε (by positivity) hα (by norm_num)
        (2*h) (doubled_strip ε h hε hb))
  have hf : ∀ z q, |q.im| ≤ |h| → AnalyticAt ℂ (fun q => multiplier ε h a θ q z) q := by
    intro z q hq
    exact KFCausalSingleGaussianHolomorphicQuotient.multiplier_analytic ε h a α c θ hε hb q hq (tailPoint z)
  have hs : |-(2*h)/2| ≤ |h| := by rw [show -(2*h)/2=-h by ring,abs_neg]
  have hg := KFCausalMixedStripExponentialGraph.graph_action ε hε (multiplier ε h a θ) |h| (bound ε h a)
    (horizontal_continuous ε h a hε hb θ) (KFCausalSingleGaussianHolomorphicQuotient.bound_nonnegative ε h a hε)
    (multiplier_bound ε h a hε hh ha hb θ) hf (2*h) (by simp) hs _ _ hbase
  change (multiplierAction ε h a hε hh ha hb θ 0 _ _,
    multiplierAction ε h a hε hh ha hb θ (-(2*h)/2) _ _) ∈ _ at hg
  rw [actual_input ε h a hε hh ha hb θ] at hg
  have he := (exponential_rescale ε hε h 2 (1/2) _ _).mp hg
  simpa only [show -(2*h)/2=-h by ring,show (1/2:ℝ)*2=1 by norm_num] using he

def secondOutput (θ : ℝ) : Hilbert := inverseL ε hε (exponentialOutput ε h a hε hh ha hb θ)

theorem mixed_square_graph (θ : ℝ) :
    (action h hh θ (firstOutput ε h a hε hh ha hb₀),secondOutput ε h a hε hh ha hb θ) ∈
      (square ε hε h).graph :=
  (square_graph ε hε h _ _).mpr ⟨_,second_exponential_graph ε h a hε hh ha hb θ,rfl⟩

theorem mixed_square_domain (θ : ℝ) :
    action h hh θ (firstOutput ε h a hε hh ha hb₀) ∈ (square ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (mixed_square_graph ε h a hε hh ha hb θ)

theorem two_actual_graphs (θ : ℝ) :
    (state ε h a hε hh ha,firstOutput ε h a hε hh ha hb₀) ∈ (square ε hε h).graph ∧
      (action h hh θ (firstOutput ε h a hε hh ha hb₀),secondOutput ε h a hε hh ha hb θ) ∈
        (square ε hε h).graph :=
  ⟨first_graph ε h a hε hh ha hb₀,mixed_square_graph ε h a hε hh ha hb θ⟩

#print axioms original_strip
#print axioms doubled_strip
#print axioms actual_input
#print axioms second_exponential_graph
#print axioms mixed_square_graph
#print axioms mixed_square_domain
#print axioms two_actual_graphs
end
end UnifiedTheory.Audit.KFCausalSingleGaussianMixedSquare

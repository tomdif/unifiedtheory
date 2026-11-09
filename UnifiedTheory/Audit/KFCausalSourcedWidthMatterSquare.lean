/- Actual vacuum-after-matter graphs for the quadratic and quartic
Hamiltonian components, retaining their half-shifted field powers. -/
import UnifiedTheory.Audit.KFCausalSourcedWidthMatterSecondInput
import UnifiedTheory.Audit.KFCausalSourcedWidthMatterRegularity
import UnifiedTheory.Audit.KFCausalBroadWidthHolomorphicBaseline
import UnifiedTheory.Audit.KFCausalMixedStripTailAttachment
import UnifiedTheory.Audit.KFCausalSingleGaussianMixedSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalSourcedWidthMatterSquare
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
open KFCausalSourcedWidthSecondInput (state)
open KFCausalReciprocalNeutralMatterSpectral (matterIndex)
open KFCausalMixedFieldGaussianStrip (degree)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalMixedStripTailAttachment (tailPoint normalize_tail family family_horizontal_continuous action_of_clockMixed)

open KFCausalSingleGaussianMixedSquare (original_strip doubled_strip)

variable (ε h a W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (j : Fin 2) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a)
  (hw : 1 ≤ w) (hW : w ≤ W) (hb : |h| ≤ ε/10)
local notation "α" => groundWidth h
local notation "c" => momentumScale h
local notation "hα" => groundWidth_positive h hh
local notation "hb₀" => original_strip ε h hε hb
local notation "hw₀" => lt_of_lt_of_le zero_lt_one hw
local notation "hW₀" => lt_of_lt_of_le hw₀ hW

local notation "k" => degree j

def matterSecond : Hilbert →ₗ.[ℂ] Hilbert :=
  composition (reverseFactor ε hε h modelDirections pointField (matterIndex j))
    (energyFactor ε hε h modelDirections pointField (matterIndex j))

def firstOutput : Hilbert :=
  KFCausalReciprocalNeutralSecondFactors.second ε a h w hε ha hh hw hb₀ C p b P (matterIndex j)

theorem first_graph :
    (state ε h a w C p b P hε hh ha hw,
      firstOutput ε h a w C p b P j hε hh ha hw hb) ∈ (matterSecond ε h j hε).graph := by
  simpa only [state,firstOutput,matterSecond] using
    KFCausalReciprocalNeutralSecondFactors.second_graph ε a h w hε ha hh hw hb₀ C p b P (matterIndex j)

def bound : ℝ := KFCausalSourcedWidthMatterMultiplier.bound ε h a α W w C p b P k
def multiplier (θ : ℝ) := family (KFCausalSourcedWidthMatterMultiplier.multiplier ε h a α W w c θ C p b P k)

include hε hb in
private theorem horizontal_continuous (θ : ℝ) :
    ∀ y, |y| ≤ |h| → Continuous (fun z : ℝ × KFCausalEuclideanClockSplit.TailSpace =>
      multiplier ε h a W w C p b P j θ ((z.1:ℂ)+(y:ℂ)*Complex.I) z.2) :=
  family_horizontal_continuous _ _ (KFCausalSourcedWidthMatterMultiplier.multiplier_horizontal_continuous ε h a α W w c θ C p b P k hε hb)

include hε hh ha hw hW hb in
private theorem multiplier_bound (θ : ℝ) :
    ∀ q, |q.im| ≤ |h| → ∀ z, ‖multiplier ε h a W w C p b P j θ q z‖ ≤ bound ε h a W w C p b P j := by
  intro q hq z
  exact KFCausalSourcedWidthMatterMultiplier.multiplier_bound ε h a α W w c θ C p b P k hε hb ha.le hα hw hW q hq (tailPoint z)

def multiplierAction (θ y : ℝ) (hy : |y| ≤ |h|) : Hilbert →L[ℂ] Hilbert :=
  KFCausalMixedStripExponentialGraph.action ε hε (multiplier ε h a W w C p b P j θ) |h| (bound ε h a W w C p b P j)
    (horizontal_continuous ε h a W w C p b P j hε hb θ) (KFCausalSourcedWidthMatterMultiplier.bound_nonnegative ε h a α W w C p b P k hε hα hw hW)
    (multiplier_bound ε h a W w C p b P j hε hh ha hw hW hb θ) y hy

def baseline : Hilbert := KFCausalBroadPairedGaussian.state ε (a/2) α (1/(4*W)) hε (by positivity) hα (by have := hW₀; positivity)
def baselineOutput : Hilbert :=
  KFCausalBroadPairedGaussian.output ε (a/2) α (1/(4*W)) hε (by positivity) hα (2*h) (doubled_strip ε h hε hb)

theorem actual_input (θ : ℝ) :
    multiplierAction ε h a W w C p b P j hε hh ha hw hW hb θ 0 (by simp)
      (inverseL ε hε (baseline ε h a W w hε hh ha hw hW)) =
      inverseL ε hε (action h hh θ (firstOutput ε h a w C p b P j hε hh ha hw hb)) := by
  apply action_of_clockMixed ε hε (KFCausalSourcedWidthMatterMultiplier.multiplier ε h a α W w c θ C p b P k) |h| (bound ε h a W w C p b P j)
    (horizontal_continuous ε h a W w C p b P j hε hb θ) (KFCausalSourcedWidthMatterMultiplier.bound_nonnegative ε h a α W w C p b P k hε hα hw hW)
    (multiplier_bound ε h a W w C p b P j hε hh ha hw hW hb θ)
  · intro q x
    simp only [KFCausalSourcedWidthMatterMultiplier.multiplier,KFCausalMatterInsertionCoordinate.coefficient,KFCausalPointFieldInsertionCoordinate.neutralCoefficient,KFCausalSymmetricInsertionCoordinate.coefficient,KFCausalWidthGaussianNeutralMultiplier.multiplier,KFCausalWidthGaussianNeutralMultiplier.neutral,KFCausalWidthGaussianHolomorphicQuotient.multiplier,KFCausalWidthGaussianHolomorphicQuotient.targetVector,KFCausalWidthGaussianHolomorphicQuotient.baselineVector,normalize_tail]
  · filter_upwards [KFCausalSourcedWidthMatterSecondInput.rotated_second_input_coe
      ε h a w C p b P hε hh ha hw hb₀ θ j,
      KFCausalBroadWidthHolomorphicBaseline.baseline_second_input_coe
        ε a α W w c hε ha hα hw₀ hW₀ (groundWidth_matching h hh)] with x hn hb
    rw [firstOutput,hn,baseline,hb,KFCausalSourcedWidthMatterMultiplier.multiplier_mul_baseline ε h a α W w c θ C p b P k (hW₀).ne']

def exponentialOutput (θ : ℝ) : Hilbert :=
  multiplierAction ε h a W w C p b P j hε hh ha hw hW hb θ (-h) (by simp)
    (baselineOutput ε h a W hε hh ha hb)

theorem second_exponential_graph (θ : ℝ) :
    (inverseL ε hε (action h hh θ (firstOutput ε h a w C p b P j hε hh ha hw hb)),
      exponentialOutput ε h a W w C p b P j hε hh ha hw hW hb θ) ∈
      (longitudinalExponential ε hε h 1).graph := by
  have hbase : (inverseL ε hε (baseline ε h a W w hε hh ha hw hW),baselineOutput ε h a W hε hh ha hb) ∈
      (longitudinalExponential ε hε (2*h) (1/2)).graph :=
    (ordered_graph_iff ε hε (2*h) _ _).mp
      (KFCausalBroadPairedGaussian.output_graph ε (a/2) α (1/(4*W)) hε (by positivity) hα (by have := hW₀; positivity)
        (2*h) (doubled_strip ε h hε hb))
  have hf : ∀ z q, |q.im| ≤ |h| → AnalyticAt ℂ (fun q => multiplier ε h a W w C p b P j θ q z) q := by
    intro z q hq
    exact KFCausalSourcedWidthMatterMultiplier.multiplier_analytic ε h a α W w c θ C p b P k hε hb q hq (tailPoint z)
  have hs : |-(2*h)/2| ≤ |h| := by rw [show -(2*h)/2=-h by ring,abs_neg]
  have hg := KFCausalMixedStripExponentialGraph.graph_action ε hε (multiplier ε h a W w C p b P j θ) |h| (bound ε h a W w C p b P j)
    (horizontal_continuous ε h a W w C p b P j hε hb θ) (KFCausalSourcedWidthMatterMultiplier.bound_nonnegative ε h a α W w C p b P k hε hα hw hW)
    (multiplier_bound ε h a W w C p b P j hε hh ha hw hW hb θ) hf (2*h) (by simp) hs _ _ hbase
  change (multiplierAction ε h a W w C p b P j hε hh ha hw hW hb θ 0 _ _,
    multiplierAction ε h a W w C p b P j hε hh ha hw hW hb θ (-(2*h)/2) _ _) ∈ _ at hg
  rw [actual_input ε h a W w C p b P j hε hh ha hw hW hb θ] at hg
  have he := (exponential_rescale ε hε h 2 (1/2) _ _).mp hg
  simpa only [show -(2*h)/2=-h by ring,show (1/2:ℝ)*2=1 by norm_num] using he

def secondOutput (θ : ℝ) : Hilbert := inverseL ε hε (exponentialOutput ε h a W w C p b P j hε hh ha hw hW hb θ)

theorem mixed_square_graph (θ : ℝ) :
    (action h hh θ (firstOutput ε h a w C p b P j hε hh ha hw hb),secondOutput ε h a W w C p b P j hε hh ha hw hW hb θ) ∈
      (square ε hε h).graph :=
  (square_graph ε hε h _ _).mpr ⟨_,second_exponential_graph ε h a W w C p b P j hε hh ha hw hW hb θ,rfl⟩

include hW in
theorem mixed_square_domain (θ : ℝ) :
    action h hh θ (firstOutput ε h a w C p b P j hε hh ha hw hb) ∈ (square ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (mixed_square_graph ε h a W w C p b P j hε hh ha hw hW hb θ)

theorem actual_matter_and_vacuum_graphs (θ : ℝ) :
    (state ε h a w C p b P hε hh ha hw,
      firstOutput ε h a w C p b P j hε hh ha hw hb) ∈ (matterSecond ε h j hε).graph ∧
      (action h hh θ (firstOutput ε h a w C p b P j hε hh ha hw hb),
        secondOutput ε h a W w C p b P j hε hh ha hw hW hb θ) ∈ (square ε hε h).graph :=
  ⟨first_graph ε h a w C p b P j hε hh ha hw hb,
    mixed_square_graph ε h a W w C p b P j hε hh ha hw hW hb θ⟩

theorem square_matter_graph :
    (state ε h a w C p b P hε hh ha hw,
      secondOutput ε h a W w C p b P j hε hh ha hw hW hb 0) ∈
      (composition (square ε hε h) (matterSecond ε h j hε)).graph := by
  apply (composition_graph _ _ _ _).mpr
  refine ⟨_,first_graph ε h a w C p b P j hε hh ha hw hb,?_⟩
  simpa only [KFCausalPhysicalCircleAction.action_zero] using
    mixed_square_graph ε h a W w C p b P j hε hh ha hw hW hb 0

#print axioms first_graph
#print axioms actual_input
#print axioms second_exponential_graph
#print axioms mixed_square_graph
#print axioms mixed_square_domain
#print axioms actual_matter_and_vacuum_graphs
#print axioms square_matter_graph
end
end UnifiedTheory.Audit.KFCausalSourcedWidthMatterSquare

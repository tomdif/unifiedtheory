/- Actual Q U(theta) L Q graphs for each symmetric charged position and
original sourced reciprocal packet. The domain follows from bounded
holomorphic multiplication of the broader Gaussian graph. -/
import UnifiedTheory.Audit.KFCausalSourcedWidthSymmetricInsertion
import UnifiedTheory.Audit.KFCausalSourcedWidthSymmetricRegularity
import UnifiedTheory.Audit.KFCausalBroadWidthHolomorphicBaseline
import UnifiedTheory.Audit.KFCausalMixedStripTailAttachment
import UnifiedTheory.Audit.KFCausalSingleGaussianMixedSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalSourcedWidthSymmetricSquare
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
open KFCausalSourcedWidthSecondInput (state firstOutput first_graph)
open KFCausalSourcedWidthFirstField (fieldOutput first_field_graph field_after_square_graph)
open KFCausalPhysicalSpectatorGraph (symmetricPosition)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalMixedStripTailAttachment (tailPoint normalize_tail family family_horizontal_continuous action_of_clockMixed)

open KFCausalSingleGaussianMixedSquare (original_strip doubled_strip)

variable (ε h a W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (i : Fin 2) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a)
  (hw : 1 ≤ w) (hW : w ≤ W) (hb : |h| ≤ ε/10)
local notation "α" => groundWidth h
local notation "c" => momentumScale h
local notation "hα" => groundWidth_positive h hh
local notation "hb₀" => original_strip ε h hε hb
local notation "hw₀" => lt_of_lt_of_le zero_lt_one hw
local notation "hW₀" => lt_of_lt_of_le hw₀ hW

def bound : ℝ := KFCausalSourcedWidthSymmetricMultiplier.bound ε h a α W w C p b P i
def multiplier (θ : ℝ) := family (KFCausalSourcedWidthSymmetricMultiplier.multiplier ε h a α W w c θ C p b P i)

include hε hb in
private theorem horizontal_continuous (θ : ℝ) :
    ∀ y, |y| ≤ |h| → Continuous (fun z : ℝ × KFCausalEuclideanClockSplit.TailSpace =>
      multiplier ε h a W w C p b P i θ ((z.1:ℂ)+(y:ℂ)*Complex.I) z.2) :=
  family_horizontal_continuous _ _ (KFCausalSourcedWidthSymmetricMultiplier.multiplier_horizontal_continuous ε h a α W w c θ C p b P i hε hb)

include hε hh ha hw hW hb in
private theorem multiplier_bound (θ : ℝ) :
    ∀ q, |q.im| ≤ |h| → ∀ z, ‖multiplier ε h a W w C p b P i θ q z‖ ≤ bound ε h a W w C p b P i := by
  intro q hq z
  exact KFCausalSourcedWidthSymmetricMultiplier.multiplier_bound ε h a α W w c θ C p b P i hε hb ha.le hα hw hW q hq (tailPoint z)

def multiplierAction (θ y : ℝ) (hy : |y| ≤ |h|) : Hilbert →L[ℂ] Hilbert :=
  KFCausalMixedStripExponentialGraph.action ε hε (multiplier ε h a W w C p b P i θ) |h| (bound ε h a W w C p b P i)
    (horizontal_continuous ε h a W w C p b P i hε hb θ) (KFCausalSourcedWidthSymmetricMultiplier.bound_nonnegative ε h a α W w C p b P i hε hα hw hW)
    (multiplier_bound ε h a W w C p b P i hε hh ha hw hW hb θ) y hy

def baseline : Hilbert := KFCausalBroadPairedGaussian.state ε (a/2) α (1/(4*W)) hε (by positivity) hα (by have := hW₀; positivity)
def baselineOutput : Hilbert :=
  KFCausalBroadPairedGaussian.output ε (a/2) α (1/(4*W)) hε (by positivity) hα (2*h) (doubled_strip ε h hε hb)

theorem actual_input (θ : ℝ) :
    multiplierAction ε h a W w C p b P i hε hh ha hw hW hb θ 0 (by simp)
      (inverseL ε hε (baseline ε h a W w hε hh ha hw hW)) =
      inverseL ε hε (action h hh θ (fieldOutput ε h a w C p b P hε hh ha hw hb₀ (symmetricPosition i))) := by
  apply action_of_clockMixed ε hε (KFCausalSourcedWidthSymmetricMultiplier.multiplier ε h a α W w c θ C p b P i) |h| (bound ε h a W w C p b P i)
    (horizontal_continuous ε h a W w C p b P i hε hb θ) (KFCausalSourcedWidthSymmetricMultiplier.bound_nonnegative ε h a α W w C p b P i hε hα hw hW)
    (multiplier_bound ε h a W w C p b P i hε hh ha hw hW hb θ)
  · intro q x
    simp only [KFCausalSourcedWidthSymmetricMultiplier.multiplier,KFCausalSymmetricInsertionCoordinate.coefficient,KFCausalWidthGaussianNeutralMultiplier.multiplier,KFCausalWidthGaussianNeutralMultiplier.neutral,KFCausalWidthGaussianHolomorphicQuotient.multiplier,KFCausalWidthGaussianHolomorphicQuotient.targetVector,KFCausalWidthGaussianHolomorphicQuotient.baselineVector,normalize_tail]
  · filter_upwards [KFCausalSourcedWidthSymmetricInsertion.rotated_second_input_coe
      ε hε h a w C p b P hh hw ha hb₀ θ i,
      KFCausalBroadWidthHolomorphicBaseline.baseline_second_input_coe
        ε a α W w c hε ha hα hw₀ hW₀ (groundWidth_matching h hh)] with x hn hb
    rw [hn,baseline,hb,KFCausalSourcedWidthSymmetricMultiplier.multiplier_mul_baseline ε h a α W w c θ C p b P i (hW₀).ne']

def exponentialOutput (θ : ℝ) : Hilbert :=
  multiplierAction ε h a W w C p b P i hε hh ha hw hW hb θ (-h) (by simp)
    (baselineOutput ε h a W hε hh ha hb)

theorem second_exponential_graph (θ : ℝ) :
    (inverseL ε hε (action h hh θ (fieldOutput ε h a w C p b P hε hh ha hw hb₀ (symmetricPosition i))),
      exponentialOutput ε h a W w C p b P i hε hh ha hw hW hb θ) ∈
      (longitudinalExponential ε hε h 1).graph := by
  have hbase : (inverseL ε hε (baseline ε h a W w hε hh ha hw hW),baselineOutput ε h a W hε hh ha hb) ∈
      (longitudinalExponential ε hε (2*h) (1/2)).graph :=
    (ordered_graph_iff ε hε (2*h) _ _).mp
      (KFCausalBroadPairedGaussian.output_graph ε (a/2) α (1/(4*W)) hε (by positivity) hα (by have := hW₀; positivity)
        (2*h) (doubled_strip ε h hε hb))
  have hf : ∀ z q, |q.im| ≤ |h| → AnalyticAt ℂ (fun q => multiplier ε h a W w C p b P i θ q z) q := by
    intro z q hq
    exact KFCausalSourcedWidthSymmetricMultiplier.multiplier_analytic ε h a α W w c θ C p b P i hε hb q hq (tailPoint z)
  have hs : |-(2*h)/2| ≤ |h| := by rw [show -(2*h)/2=-h by ring,abs_neg]
  have hg := KFCausalMixedStripExponentialGraph.graph_action ε hε (multiplier ε h a W w C p b P i θ) |h| (bound ε h a W w C p b P i)
    (horizontal_continuous ε h a W w C p b P i hε hb θ) (KFCausalSourcedWidthSymmetricMultiplier.bound_nonnegative ε h a α W w C p b P i hε hα hw hW)
    (multiplier_bound ε h a W w C p b P i hε hh ha hw hW hb θ) hf (2*h) (by simp) hs _ _ hbase
  change (multiplierAction ε h a W w C p b P i hε hh ha hw hW hb θ 0 _ _,
    multiplierAction ε h a W w C p b P i hε hh ha hw hW hb θ (-(2*h)/2) _ _) ∈ _ at hg
  rw [actual_input ε h a W w C p b P i hε hh ha hw hW hb θ] at hg
  have he := (exponential_rescale ε hε h 2 (1/2) _ _).mp hg
  simpa only [show -(2*h)/2=-h by ring,show (1/2:ℝ)*2=1 by norm_num] using he

def secondOutput (θ : ℝ) : Hilbert := inverseL ε hε (exponentialOutput ε h a W w C p b P i hε hh ha hw hW hb θ)

theorem mixed_square_graph (θ : ℝ) :
    (action h hh θ (fieldOutput ε h a w C p b P hε hh ha hw hb₀ (symmetricPosition i)),secondOutput ε h a W w C p b P i hε hh ha hw hW hb θ) ∈
      (square ε hε h).graph :=
  (square_graph ε hε h _ _).mpr ⟨_,second_exponential_graph ε h a W w C p b P i hε hh ha hw hW hb θ,rfl⟩

include hW in
theorem mixed_square_domain (θ : ℝ) :
    action h hh θ (fieldOutput ε h a w C p b P hε hh ha hw hb₀ (symmetricPosition i)) ∈ (square ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (mixed_square_graph ε h a W w C p b P i hε hh ha hw hW hb θ)

theorem three_actual_graphs (θ : ℝ) :
    (state ε h a w C p b P hε hh ha hw,firstOutput ε h a w C p b P hε hh ha hw hb₀) ∈ (square ε hε h).graph ∧
      (firstOutput ε h a w C p b P hε hh ha hw hb₀,
        fieldOutput ε h a w C p b P hε hh ha hw hb₀ (symmetricPosition i)) ∈
          (KFCausalPhysicalField.physicalField (symmetricPosition i)).graph ∧
      (action h hh θ (fieldOutput ε h a w C p b P hε hh ha hw hb₀ (symmetricPosition i)),
        secondOutput ε h a W w C p b P i hε hh ha hw hW hb θ) ∈ (square ε hε h).graph :=
  ⟨first_graph ε h a w C p b P hε hh ha hw hb₀,
    first_field_graph ε h a w C p b P hε hh ha hw hb₀ (symmetricPosition i),
    mixed_square_graph ε h a W w C p b P i hε hh ha hw hW hb θ⟩

theorem square_field_square_graph :
    (state ε h a w C p b P hε hh ha hw,
      secondOutput ε h a W w C p b P i hε hh ha hw hW hb 0) ∈
      (composition (square ε hε h)
        (composition (KFCausalPhysicalField.physicalField (symmetricPosition i))
          (square ε hε h))).graph := by
  apply (composition_graph _ _ _ _).mpr
  refine ⟨_,field_after_square_graph ε h a w C p b P hε hh ha hw hb₀ (symmetricPosition i),?_⟩
  simpa only [KFCausalPhysicalCircleAction.action_zero] using
    mixed_square_graph ε h a W w C p b P i hε hh ha hw hW hb 0

#print axioms actual_input
#print axioms second_exponential_graph
#print axioms mixed_square_graph
#print axioms mixed_square_domain
#print axioms three_actual_graphs
#print axioms square_field_square_graph
end
end UnifiedTheory.Audit.KFCausalSourcedWidthSymmetricSquare

/- Actual half-clock and full-clock graphs for all bounded clock-weighted
matter actions, including the inverse-dressed output graph. -/
import UnifiedTheory.Audit.KFCausalClockWeightedMatterAction
import UnifiedTheory.Audit.KFCausalClockMixedClockGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalClockWeightedMatterGraphs
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorBoundedInverse (inverseL inverseL_graph)
open KFCausalClockFloorClockHalf (clockHalf half_inverse_graph)
open KFCausalClockFloorClockOperator (clockOperator)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalClockWeightedMatterAction (action action_clockMixed)
open KFCausalOrderedOperatorComposition (composition_graph)

private theorem weight_succ (ε : ℝ) (hε : 0 < ε) (n : ℕ) (q : ℝ) :
    (KFCausalOuterMatterClockWeights.clockWeight ε hε (n+1) q:ℂ) =
      (KFCausalClockMixedClockGraph.halfWeight ε hε q:ℂ)*
        (KFCausalOuterMatterClockWeights.clockWeight ε hε n q:ℂ) := by
  unfold KFCausalOuterMatterClockWeights.clockWeight
  rw [pow_succ,Complex.ofReal_mul]
  change (((KFCausalClockMixedClockGraph.halfWeight ε hε q)^n:ℝ):ℂ)*
    (KFCausalClockMixedClockGraph.halfWeight ε hε q:ℂ) =
    (KFCausalClockMixedClockGraph.halfWeight ε hε q:ℂ)*
      (((KFCausalClockMixedClockGraph.halfWeight ε hε q)^n:ℝ):ℂ)
  exact mul_comm _ _

variable (ε h a W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (k m n : ℕ) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hw : 1 ≤ w)
  (hW : w ≤ W) (hb : |h| ≤ ε/10)

theorem half_graph (θ y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    (action ε h a W w C p b P k m n hε hh ha hw hW hb θ y hy f,
      action ε h a W w C p b P k m (n+1) hε hh ha hw hW hb θ y hy f) ∈
      (clockHalf ε).graph := by
  apply (KFCausalClockMixedClockGraph.clockHalf_graph_iff ε hε _ _).mpr
  filter_upwards [action_clockMixed ε h a W w C p b P k m n hε hh ha hw hW hb θ y hy f,
    action_clockMixed ε h a W w C p b P k m (n+1) hε hh ha hw hW hb θ y hy f]
      with x hn hs
  rw [hn,hs,weight_succ]
  ring

theorem clock_graph (θ y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    (action ε h a W w C p b P k m n hε hh ha hw hW hb θ y hy f,
      action ε h a W w C p b P k m (n+2) hε hh ha hw hW hb θ y hy f) ∈
      (clockOperator ε hε).graph := by
  apply (KFCausalClockMixedClockGraph.clockHalf_square_graph_iff ε hε _ _).mp
  apply (composition_graph _ _ _ _).mpr
  exact ⟨_,half_graph ε h a W w C p b P k m n hε hh ha hw hW hb θ y hy f,
    half_graph ε h a W w C p b P k m (n+1) hε hh ha hw hW hb θ y hy f⟩

theorem inverseL_half_graph (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    (inverseL ε hε f,f) ∈ (clockHalf ε).graph := by
  rw [half_inverse_graph ε hε,inverseL_graph ε hε]

theorem inverseL_clock_graph (θ y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    (inverseL ε hε (action ε h a W w C p b P k m n hε hh ha hw hW hb θ y hy f),
      action ε h a W w C p b P k m (n+1) hε hh ha hw hW hb θ y hy f) ∈
      (clockOperator ε hε).graph := by
  apply (KFCausalClockMixedClockGraph.clockHalf_square_graph_iff ε hε _ _).mp
  apply (composition_graph _ _ _ _).mpr
  exact ⟨_,inverseL_half_graph ε hε _,
    half_graph ε h a W w C p b P k m n hε hh ha hw hW hb θ y hy f⟩

#print axioms half_graph
#print axioms clock_graph
#print axioms inverseL_half_graph
#print axioms inverseL_clock_graph
end
end UnifiedTheory.Audit.KFCausalClockWeightedMatterGraphs

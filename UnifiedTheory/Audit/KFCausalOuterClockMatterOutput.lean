/- The already constructed outer matter outputs retain the full clock
domain, including their primitive charge averages. -/
import UnifiedTheory.Audit.KFCausalClockWeightedMatterGraphs
import UnifiedTheory.Audit.KFCausalOuterMatterProjected

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalOuterClockMatterOutput
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockOperator (clockOperator clockOperator_selfAdjoint)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalOuterMatterExponential (fullState)
open KFCausalVacuumMatterInput (innerDegree innerOutput)
open KFCausalMixedFieldGaussianStrip (degree)
open KFCausalSourcedWidthMatterSquare (baselineOutput matterSecond)
open KFCausalMatterPrimitiveAverage (average average_graph)
open KFCausalPhysicalCircleAction (action)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable (ε h a W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hw : 1 ≤ w)
  (hW : w ≤ W) (hb : |h| ≤ ε/10) (i : Option (Fin 2)) (j : Fin 2)
local notation "v" => KFCausalOuterMatterSquare.secondOutput ε h a W w C p b P hε hh ha hw hW hb i j

def weightedOutput (n : ℕ) (θ : ℝ) : Hilbert :=
  KFCausalClockWeightedMatterAction.action ε h a W w C p b P (innerDegree i) (degree j) n
    hε hh ha hw hW hb θ (-h) (by simp) (baselineOutput ε h a W hε hh ha hb)

def clockOutput (θ : ℝ) : Hilbert := weightedOutput ε h a W w C p b P hε hh ha hw hW hb i j 1 θ
def projectedOutput : Hilbert := average (clockOutput ε h a W w C p b P hε hh ha hw hW hb i j)

theorem zero_output (θ : ℝ) :
    weightedOutput ε h a W w C p b P hε hh ha hw hW hb i j 0 θ =
      fullState ε h a W w C p b P (innerDegree i) (degree j) hε hh ha hw hW hb θ :=
  KFCausalClockWeightedMatterAction.action_zero_weight ε h a W w C p b P (innerDegree i) (degree j)
    hε hh ha hw hW hb θ (-h) (by simp) _

theorem clock_graph (θ : ℝ) :
    (v θ,clockOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈ (clockOperator ε hε).graph := by
  have hg := KFCausalClockWeightedMatterGraphs.inverseL_clock_graph ε h a W w C p b P
    (innerDegree i) (degree j) 0 hε hh ha hw hW hb θ (-h) (by simp)
    (baselineOutput ε h a W hε hh ha hb)
  change (inverseL ε hε (weightedOutput ε h a W w C p b P hε hh ha hw hW hb i j 0 θ),
    clockOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈ _ at hg
  rwa [zero_output ε h a W w C p b P hε hh ha hw hW hb i j θ] at hg

theorem clockOutput_continuous :
    Continuous (clockOutput ε h a W w C p b P hε hh ha hw hW hb i j) :=
  KFCausalClockWeightedMatterAction.action_continuous ε h a W w C p b P (innerDegree i) (degree j) 1
    hε hh ha hw hW hb (-h) (by simp) _

theorem clock_matter_graph (θ : ℝ) :
    (action h hh θ (innerOutput ε h a w C p b P hε hh ha hw hb i),
      clockOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈
      (composition (clockOperator ε hε) (matterSecond ε h j hε)).graph :=
  (composition_graph _ _ _ _).mpr ⟨v θ,
    KFCausalOuterMatterSquare.mixed_graph ε h a W w C p b P hε hh ha hw hW hb i j θ,
    clock_graph ε h a W w C p b P hε hh ha hw hW hb i j θ⟩

theorem projected_clock_graph :
    (KFCausalOuterMatterProjected.projectedOutput ε h a W w C p b P hε hh ha hw hW hb i j,
      projectedOutput ε h a W w C p b P hε hh ha hw hW hb i j) ∈ (clockOperator ε hε).graph := by
  rw [KFCausalOuterMatterProjected.projectedOutput_average]
  exact average_graph (clockOperator ε hε) (clockOperator_selfAdjoint ε hε).isClosed _ _
    (KFCausalOuterMatterSquare.secondOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i j)
    (clockOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i j)
    (clock_graph ε h a W w C p b P hε hh ha hw hW hb i j)

theorem projected_clock_matter_graph :
    (zeroProjection h hh (innerOutput ε h a w C p b P hε hh ha hw hb i),
      projectedOutput ε h a W w C p b P hε hh ha hw hW hb i j) ∈
      (composition (clockOperator ε hε) (matterSecond ε h j hε)).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,
    KFCausalOuterMatterProjected.projected_matter_graph ε h a W w C p b P hε hh ha hw hW hb i j,
    projected_clock_graph ε h a W w C p b P hε hh ha hw hW hb i j⟩

#print axioms zero_output
#print axioms clock_graph
#print axioms clockOutput_continuous
#print axioms clock_matter_graph
#print axioms projected_clock_graph
#print axioms projected_clock_matter_graph
end
end UnifiedTheory.Audit.KFCausalOuterClockMatterOutput

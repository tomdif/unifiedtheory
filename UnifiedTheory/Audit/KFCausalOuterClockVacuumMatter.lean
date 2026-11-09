/- The actual positive clock after the original vacuum or matter second
output. The inverse-dressed input requires the third half-clock weight. -/
import UnifiedTheory.Audit.KFCausalClockWeightedMatterGraphs
import UnifiedTheory.Audit.KFCausalOuterMatterExponential
import UnifiedTheory.Audit.KFCausalMatterPrimitiveAverage

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalOuterClockVacuumMatter
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorClockHalf (clockHalf clockHalf_selfAdjoint)
open KFCausalClockFloorClockOperator (clockOperator clockOperator_selfAdjoint)
open KFCausalPhysicalCircleAction (action action_strong_continuous)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalVacuumMatterInput (innerDegree innerOutput)
open KFCausalSourcedWidthMatterSquare (baseline)
open KFCausalMatterPrimitiveAverage (average average_graph average_action)
open KFCausalOrderedOperatorComposition (composition)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)

variable (ε h a W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hw : 1 ≤ w)
  (hW : w ≤ W) (hb : |h| ≤ ε/10) (i : Option (Fin 2))
local notation "u" => innerOutput ε h a w C p b P hε hh ha hw hb i

def weightedOutput (n : ℕ) (θ : ℝ) : Hilbert :=
  KFCausalClockWeightedMatterAction.action ε h a W w C p b P (innerDegree i) 0 n
    hε hh ha hw hW hb θ 0 (by simp) (inverseL ε hε (baseline ε h a W w hε hh ha hw hW))

def secondOutput (θ : ℝ) : Hilbert := weightedOutput ε h a W w C p b P hε hh ha hw hW hb i 3 θ
def projectedForward : Hilbert := average (weightedOutput ε h a W w C p b P hε hh ha hw hW hb i 2)
def projectedOutput : Hilbert := average (secondOutput ε h a W w C p b P hε hh ha hw hW hb i)

theorem zero_output (θ : ℝ) :
    weightedOutput ε h a W w C p b P hε hh ha hw hW hb i 0 θ = inverseL ε hε (action h hh θ u) := by
  rw [weightedOutput,KFCausalClockWeightedMatterAction.action_zero_weight,
    KFCausalOuterMatterExponential.actual_input ε h a W w C p b P hε hh ha hw hW hb i θ]

theorem weighted_half_graph (n : ℕ) (θ : ℝ) :
    (weightedOutput ε h a W w C p b P hε hh ha hw hW hb i n θ,
      weightedOutput ε h a W w C p b P hε hh ha hw hW hb i (n+1) θ) ∈ (clockHalf ε).graph :=
  KFCausalClockWeightedMatterGraphs.half_graph ε h a W w C p b P (innerDegree i) 0 n
    hε hh ha hw hW hb θ 0 (by simp) _

theorem weighted_clock_graph (n : ℕ) (θ : ℝ) :
    (weightedOutput ε h a W w C p b P hε hh ha hw hW hb i n θ,
      weightedOutput ε h a W w C p b P hε hh ha hw hW hb i (n+2) θ) ∈ (clockOperator ε hε).graph :=
  KFCausalClockWeightedMatterGraphs.clock_graph ε h a W w C p b P (innerDegree i) 0 n
    hε hh ha hw hW hb θ 0 (by simp) _

theorem one_output (θ : ℝ) :
    weightedOutput ε h a W w C p b P hε hh ha hw hW hb i 1 θ = action h hh θ u := by
  have hg := weighted_half_graph ε h a W w C p b P hε hh ha hw hW hb i 0 θ
  rw [zero_output ε h a W w C p b P hε hh ha hw hW hb i θ] at hg
  exact (clockHalf ε).mem_graph_snd_inj' hg
    (KFCausalClockWeightedMatterGraphs.inverseL_half_graph ε hε (action h hh θ u)) rfl

theorem first_half_graph (θ : ℝ) :
    (action h hh θ u,weightedOutput ε h a W w C p b P hε hh ha hw hW hb i 2 θ) ∈
      (clockHalf ε).graph := by
  have hg := weighted_half_graph ε h a W w C p b P hε hh ha hw hW hb i 1 θ
  rwa [one_output ε h a W w C p b P hε hh ha hw hW hb i θ] at hg

theorem second_half_graph (θ : ℝ) :
    (weightedOutput ε h a W w C p b P hε hh ha hw hW hb i 2 θ,
      secondOutput ε h a W w C p b P hε hh ha hw hW hb i θ) ∈ (clockHalf ε).graph :=
  weighted_half_graph ε h a W w C p b P hε hh ha hw hW hb i 2 θ

theorem mixed_graph (θ : ℝ) :
    (action h hh θ u,secondOutput ε h a W w C p b P hε hh ha hw hW hb i θ) ∈
      (clockOperator ε hε).graph := by
  have hg := weighted_clock_graph ε h a W w C p b P hε hh ha hw hW hb i 1 θ
  rwa [one_output ε h a W w C p b P hε hh ha hw hW hb i θ] at hg

theorem actual_second_graph (θ : ℝ) :
    (action h hh θ u,secondOutput ε h a W w C p b P hε hh ha hw hW hb i θ) ∈
      (composition (reverseFactor ε hε h modelDirections pointField 0)
        (energyFactor ε hε h modelDirections pointField 0)).graph := by
  rw [KFCausalClockMixedClockGraph.actual_clockSecond_eq]
  exact mixed_graph ε h a W w C p b P hε hh ha hw hW hb i θ

theorem weightedOutput_continuous (n : ℕ) :
    Continuous (weightedOutput ε h a W w C p b P hε hh ha hw hW hb i n) :=
  KFCausalClockWeightedMatterAction.action_continuous ε h a W w C p b P (innerDegree i) 0 n
    hε hh ha hw hW hb 0 (by simp) _

theorem secondOutput_continuous : Continuous (secondOutput ε h a W w C p b P hε hh ha hw hW hb i) :=
  weightedOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i 3

theorem projected_forward_graph :
    (zeroProjection h hh u,projectedForward ε h a W w C p b P hε hh ha hw hW hb i) ∈
      (clockHalf ε).graph := by
  have hg := average_graph (clockHalf ε) (clockHalf_selfAdjoint ε).isClosed
    (fun θ => action h hh θ u) _ (action_strong_continuous h hh u)
    (weightedOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i 2)
    (first_half_graph ε h a W w C p b P hε hh ha hw hW hb i)
  rwa [average_action h hh u] at hg

theorem projected_reverse_graph :
    (projectedForward ε h a W w C p b P hε hh ha hw hW hb i,
      projectedOutput ε h a W w C p b P hε hh ha hw hW hb i) ∈ (clockHalf ε).graph :=
  average_graph (clockHalf ε) (clockHalf_selfAdjoint ε).isClosed _ _
    (weightedOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i 2)
    (secondOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i)
    (second_half_graph ε h a W w C p b P hε hh ha hw hW hb i)

theorem projected_graph :
    (zeroProjection h hh u,projectedOutput ε h a W w C p b P hε hh ha hw hW hb i) ∈
      (clockOperator ε hε).graph := by
  have hg := average_graph (clockOperator ε hε) (clockOperator_selfAdjoint ε hε).isClosed
    (fun θ => action h hh θ u) _ (action_strong_continuous h hh u)
    (secondOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i)
    (mixed_graph ε h a W w C p b P hε hh ha hw hW hb i)
  rwa [average_action h hh u] at hg

#print axioms zero_output
#print axioms weighted_half_graph
#print axioms weighted_clock_graph
#print axioms one_output
#print axioms first_half_graph
#print axioms second_half_graph
#print axioms mixed_graph
#print axioms actual_second_graph
#print axioms weightedOutput_continuous
#print axioms secondOutput_continuous
#print axioms projected_forward_graph
#print axioms projected_reverse_graph
#print axioms projected_graph
end
end UnifiedTheory.Audit.KFCausalOuterClockVacuumMatter

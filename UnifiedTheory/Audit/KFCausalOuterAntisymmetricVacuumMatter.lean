/- The two actual antisymmetric kinetic seconds after each original
vacuum or matter output, with charge projection through closed momenta. -/
import UnifiedTheory.Audit.KFCausalAntisymmetricInsertionGraphs
import UnifiedTheory.Audit.KFCausalAntisymmetricKineticGraphAssembly
import UnifiedTheory.Audit.KFCausalOuterMatterExponential
import UnifiedTheory.Audit.KFCausalMatterPrimitiveAverage

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalOuterAntisymmetricVacuumMatter
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalPhysicalCircleAction (action action_strong_continuous)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalVacuumMatterInput (innerDegree innerOutput)
open KFCausalSourcedWidthMatterSquare (baseline)
open KFCausalMatterPrimitiveAverage (average average_graph average_inverseL average_action)
open KFCausalPhysicalTransverseMomentum (transverseMomentum transverseMomentum_selfAdjoint)
open KFCausalAntisymmetricMomentumCoordinates (antiDirection)
open KFCausalClockFloorAntisymmetricGraph (antiIndex)
open KFCausalAntisymmetricKineticGraphAssembly (kineticSecond)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)

variable (ε h a W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hw : 1 ≤ w)
  (hW : w ≤ W) (hb : |h| ≤ ε/10) (i : Option (Fin 2)) (j : Fin 2)
local notation "u" => innerOutput ε h a w C p b P hε hh ha hw hb i

def weightedOutput (n : ℕ) (θ : ℝ) : Hilbert :=
  KFCausalAntisymmetricInsertionAction.action ε h a W w C p b P (innerDegree i) n j
    hε hh ha hw hW hb θ 0 (by simp) (inverseL ε hε (baseline ε h a W w hε hh ha hw hW))

def forwardOutput (θ : ℝ) : Hilbert := weightedOutput ε h a W w C p b P hε hh ha hw hW hb i j 1 θ

def secondOutput (θ : ℝ) : Hilbert :=
  inverseL ε hε (weightedOutput ε h a W w C p b P hε hh ha hw hW hb i j 2 θ)

def projectedForward : Hilbert := average (forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j)
def projectedOutput : Hilbert :=
  inverseL ε hε (average (weightedOutput ε h a W w C p b P hε hh ha hw hW hb i j 2))

theorem zero_output (θ : ℝ) :
    weightedOutput ε h a W w C p b P hε hh ha hw hW hb i j 0 θ=inverseL ε hε (action h hh θ u) := by
  rw [weightedOutput,KFCausalAntisymmetricInsertionAction.action_zero_power,
    KFCausalOuterMatterExponential.actual_input ε h a W w C p b P hε hh ha hw hW hb i θ]

theorem weighted_momentum_graph (n : ℕ) (θ : ℝ) :
    (weightedOutput ε h a W w C p b P hε hh ha hw hW hb i j n θ,
      weightedOutput ε h a W w C p b P hε hh ha hw hW hb i j (n+1) θ) ∈
        (transverseMomentum h (antiDirection j)).graph :=
  KFCausalAntisymmetricInsertionGraphs.momentum_graph ε h a W w C p b P (innerDegree i) n j
    hε hh ha hw hW hb θ _

theorem first_momentum_graph (θ : ℝ) :
    (inverseL ε hε (action h hh θ u),forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈
      (transverseMomentum h (antiDirection j)).graph := by
  have hg := weighted_momentum_graph ε h a W w C p b P hε hh ha hw hW hb i j 0 θ
  rwa [zero_output ε h a W w C p b P hε hh ha hw hW hb i j θ] at hg

theorem second_momentum_graph (θ : ℝ) :
    (forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j θ,
      weightedOutput ε h a W w C p b P hε hh ha hw hW hb i j 2 θ) ∈
        (transverseMomentum h (antiDirection j)).graph :=
  weighted_momentum_graph ε h a W w C p b P hε hh ha hw hW hb i j 1 θ

theorem forward_graph (θ : ℝ) :
    (action h hh θ u,forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈
      (energyFactor ε hε h modelDirections pointField (antiIndex j)).graph :=
  KFCausalAntisymmetricKineticGraphAssembly.actual_forward_graph ε hε h j _ _
    (first_momentum_graph ε h a W w C p b P hε hh ha hw hW hb i j θ)

theorem reverse_graph (θ : ℝ) :
    (forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j θ,
      secondOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈
        (reverseFactor ε hε h modelDirections pointField (antiIndex j)).graph :=
  KFCausalAntisymmetricKineticGraphAssembly.actual_reverse_graph ε hε h j _ _
    (second_momentum_graph ε h a W w C p b P hε hh ha hw hW hb i j θ)

theorem mixed_graph (θ : ℝ) :
    (action h hh θ u,secondOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈
      (kineticSecond ε hε h j).graph :=
  KFCausalAntisymmetricKineticGraphAssembly.actual_second_graph ε hε h j _ _ _
    (first_momentum_graph ε h a W w C p b P hε hh ha hw hW hb i j θ)
    (second_momentum_graph ε h a W w C p b P hε hh ha hw hW hb i j θ)

include hW in
theorem mixed_domain (θ : ℝ) : action h hh θ u ∈ (kineticSecond ε hε h j).domain :=
  LinearPMap.mem_domain_of_mem_graph (mixed_graph ε h a W w C p b P hε hh ha hw hW hb i j θ)

theorem weightedOutput_continuous (n : ℕ) :
    Continuous (weightedOutput ε h a W w C p b P hε hh ha hw hW hb i j n) :=
  KFCausalAntisymmetricInsertionAction.action_continuous ε h a W w C p b P (innerDegree i) n j
    hε hh ha hw hW hb 0 (by simp) _

theorem secondOutput_continuous : Continuous (secondOutput ε h a W w C p b P hε hh ha hw hW hb i j) :=
  (inverseL ε hε).continuous.comp (weightedOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i j 2)

private theorem projected_first_momentum :
    (inverseL ε hε (zeroProjection h hh u),projectedForward ε h a W w C p b P hε hh ha hw hW hb i j) ∈
      (transverseMomentum h (antiDirection j)).graph := by
  have hg := average_graph _ (transverseMomentum_selfAdjoint h (antiDirection j)).isClosed
    (fun θ => inverseL ε hε (action h hh θ u)) _
    ((inverseL ε hε).continuous.comp (action_strong_continuous h hh u))
    (weightedOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i j 1)
    (first_momentum_graph ε h a W w C p b P hε hh ha hw hW hb i j)
  rwa [average_inverseL ε hε _ (action_strong_continuous h hh u),average_action h hh u] at hg

private theorem projected_second_momentum :
    (projectedForward ε h a W w C p b P hε hh ha hw hW hb i j,
      average (weightedOutput ε h a W w C p b P hε hh ha hw hW hb i j 2)) ∈
        (transverseMomentum h (antiDirection j)).graph :=
  average_graph _ (transverseMomentum_selfAdjoint h (antiDirection j)).isClosed _ _
    (weightedOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i j 1)
    (weightedOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i j 2)
    (second_momentum_graph ε h a W w C p b P hε hh ha hw hW hb i j)

theorem projected_forward_graph :
    (zeroProjection h hh u,projectedForward ε h a W w C p b P hε hh ha hw hW hb i j) ∈
      (energyFactor ε hε h modelDirections pointField (antiIndex j)).graph :=
  KFCausalAntisymmetricKineticGraphAssembly.actual_forward_graph ε hε h j _ _
    (projected_first_momentum ε h a W w C p b P hε hh ha hw hW hb i j)

theorem projected_reverse_graph :
    (projectedForward ε h a W w C p b P hε hh ha hw hW hb i j,
      projectedOutput ε h a W w C p b P hε hh ha hw hW hb i j) ∈
        (reverseFactor ε hε h modelDirections pointField (antiIndex j)).graph :=
  KFCausalAntisymmetricKineticGraphAssembly.actual_reverse_graph ε hε h j _ _
    (projected_second_momentum ε h a W w C p b P hε hh ha hw hW hb i j)

theorem projected_graph :
    (zeroProjection h hh u,projectedOutput ε h a W w C p b P hε hh ha hw hW hb i j) ∈
      (kineticSecond ε hε h j).graph :=
  KFCausalAntisymmetricKineticGraphAssembly.actual_second_graph ε hε h j _ _ _
    (projected_first_momentum ε h a W w C p b P hε hh ha hw hW hb i j)
    (projected_second_momentum ε h a W w C p b P hε hh ha hw hW hb i j)

include hW in
theorem projected_domain : zeroProjection h hh u ∈ (kineticSecond ε hε h j).domain :=
  LinearPMap.mem_domain_of_mem_graph (projected_graph ε h a W w C p b P hε hh ha hw hW hb i j)

#print axioms zero_output
#print axioms weighted_momentum_graph
#print axioms first_momentum_graph
#print axioms second_momentum_graph
#print axioms forward_graph
#print axioms reverse_graph
#print axioms mixed_graph
#print axioms mixed_domain
#print axioms weightedOutput_continuous
#print axioms secondOutput_continuous
#print axioms projected_forward_graph
#print axioms projected_reverse_graph
#print axioms projected_graph
#print axioms projected_domain
end
end UnifiedTheory.Audit.KFCausalOuterAntisymmetricVacuumMatter

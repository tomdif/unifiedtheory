/- The charge projection of each actual inner vacuum or matter output
has the actual outer matter graph, including both primitive factor graphs. -/
import UnifiedTheory.Audit.KFCausalOuterMatterSquare
import UnifiedTheory.Audit.KFCausalMatterPrimitiveAverage

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalOuterMatterProjected
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalVacuumMatterInput (innerDegree innerOutput)
open KFCausalOuterMatterExponential (halfState fullState)
open KFCausalOuterMatterSquare (forwardOutput secondOutput)
open KFCausalMixedFieldGaussianStrip (degree)
open KFCausalMatterPrimitiveAverage (average)
open KFCausalSourcedWidthMatterSquare (matterSecond)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalReciprocalNeutralMatterSpectral (matterIndex)

variable (ε h a W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hw : 1 ≤ w)
  (hW : w ≤ W) (hb : |h| ≤ ε/10) (i : Option (Fin 2)) (j : Fin 2)
local notation "u" => innerOutput ε h a w C p b P hε hh ha hw hb i
local notation "z" => (fun m => halfState ε h a W w C p b P (innerDegree i) m hε hh ha hw hW hb)
local notation "y" => (fun m => fullState ε h a W w C p b P (innerDegree i) m hε hh ha hw hW hb)
local notation "aout" => forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j

def projectedForward : Hilbert := average aout

def projectedOutput : Hilbert := inverseL ε hε (average (y (degree j)))

theorem projected_graphs :
    (zeroProjection h hh u,projectedForward ε h a W w C p b P hε hh ha hw hW hb i j) ∈
      (energyFactor ε hε h modelDirections pointField (matterIndex j)).graph ∧
    (projectedForward ε h a W w C p b P hε hh ha hw hW hb i j,
      projectedOutput ε h a W w C p b P hε hh ha hw hW hb i j) ∈
      (reverseFactor ε hε h modelDirections pointField (matterIndex j)).graph ∧
    (zeroProjection h hh u,projectedOutput ε h a W w C p b P hε hh ha hw hW hb i j) ∈
      (matterSecond ε h j hε).graph :=
  KFCausalMatterPrimitiveAverage.actual_projected_graphs ε hε h hh j u
    (z 0) aout (z (degree j)) (y (degree j))
    (KFCausalOuterMatterSquare.halfState_continuous ε h a W w C p b P hε hh ha hw hW hb i 0)
    (KFCausalOuterMatterSquare.forwardOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i j)
    (KFCausalOuterMatterSquare.halfState_continuous ε h a W w C p b P hε hh ha hw hW hb i (degree j))
    (KFCausalOuterMatterSquare.fullState_continuous ε h a W w C p b P hε hh ha hw hW hb i (degree j))
    (KFCausalOuterMatterExponential.actual_half_graph ε h a W w C p b P hε hh ha hw hW hb i)
    (KFCausalOuterMatterSquare.forward_field_graph ε h a W w C p b P hε hh ha hw hW hb i j)
    (KFCausalOuterMatterSquare.reverse_field_graph ε h a W w C p b P hε hh ha hw hW hb i j)
    (KFCausalOuterMatterExponential.second_half_graph ε h a W w C p b P
      (innerDegree i) (degree j) hε hh ha hw hW hb)

theorem projected_forward_graph :
    (zeroProjection h hh u,projectedForward ε h a W w C p b P hε hh ha hw hW hb i j) ∈
      (energyFactor ε hε h modelDirections pointField (matterIndex j)).graph :=
  (projected_graphs ε h a W w C p b P hε hh ha hw hW hb i j).1

theorem projected_reverse_graph :
    (projectedForward ε h a W w C p b P hε hh ha hw hW hb i j,
      projectedOutput ε h a W w C p b P hε hh ha hw hW hb i j) ∈
      (reverseFactor ε hε h modelDirections pointField (matterIndex j)).graph :=
  (projected_graphs ε h a W w C p b P hε hh ha hw hW hb i j).2.1

theorem projected_matter_graph :
    (zeroProjection h hh u,projectedOutput ε h a W w C p b P hε hh ha hw hW hb i j) ∈
      (matterSecond ε h j hε).graph :=
  (projected_graphs ε h a W w C p b P hε hh ha hw hW hb i j).2.2

include hW in
theorem projected_matter_domain : zeroProjection h hh u ∈ (matterSecond ε h j hε).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (projected_matter_graph ε h a W w C p b P hε hh ha hw hW hb i j)

theorem projectedOutput_average :
    projectedOutput ε h a W w C p b P hε hh ha hw hW hb i j =
      average (secondOutput ε h a W w C p b P hε hh ha hw hW hb i j) := by
  exact (KFCausalMatterPrimitiveAverage.average_inverseL ε hε (y (degree j))
    (KFCausalOuterMatterSquare.fullState_continuous ε h a W w C p b P hε hh ha hw hW hb i (degree j))).symm

#print axioms projected_graphs
#print axioms projected_forward_graph
#print axioms projected_reverse_graph
#print axioms projected_matter_graph
#print axioms projected_matter_domain
#print axioms projectedOutput_average
end
end UnifiedTheory.Audit.KFCausalOuterMatterProjected

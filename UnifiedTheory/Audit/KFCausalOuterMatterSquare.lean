/- Actual outer quadratic and quartic matter components on each original
vacuum or matter second output, with all primitive domain witnesses. -/
import UnifiedTheory.Audit.KFCausalOuterMatterExponential
import UnifiedTheory.Audit.KFCausalOuterMatterActionContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalOuterMatterSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalPhysicalCircleAction (action)
open KFCausalVacuumMatterInput (innerDegree innerOutput innerSecond)
open KFCausalOuterMatterExponential (halfState fullState baselineHalfOutput)
open KFCausalMixedFieldGaussianStrip (degree)
open KFCausalMatterHalfStepAssembly (fieldFactor)
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

def forwardOutput (θ : ℝ) : Hilbert := z (j.val+1) θ
def secondOutput (θ : ℝ) : Hilbert := inverseL ε hε (y (degree j) θ)

theorem forward_field_graph (θ : ℝ) :
    (z 0 θ,forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈
      (fieldFactor j).graph := by
  fin_cases j
  · exact KFCausalOuterMatterHalfField.pointField_graph ε h a W w C p b P
      (innerDegree i) 0 hε hh ha hw hW hb θ (baselineHalfOutput ε h a W hε hh ha hb)
  · exact KFCausalOuterMatterHalfField.fieldSquare_graph ε h a W w C p b P
      (innerDegree i) 0 hε hh ha hw hW hb θ (baselineHalfOutput ε h a W hε hh ha hb)

theorem reverse_field_graph (θ : ℝ) :
    (forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j θ,z (degree j) θ) ∈
      (fieldFactor j).graph := by
  fin_cases j
  · exact KFCausalOuterMatterHalfField.pointField_graph ε h a W w C p b P
      (innerDegree i) 1 hε hh ha hw hW hb θ (baselineHalfOutput ε h a W hε hh ha hb)
  · exact KFCausalOuterMatterHalfField.fieldSquare_graph ε h a W w C p b P
      (innerDegree i) 2 hε hh ha hw hW hb θ (baselineHalfOutput ε h a W hε hh ha hb)

theorem forward_graph (θ : ℝ) :
    (action h hh θ u,forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈
      (energyFactor ε hε h modelDirections pointField (matterIndex j)).graph :=
  KFCausalMatterHalfStepAssembly.actual_forward_graph ε hε h j _ _ _
    (KFCausalOuterMatterExponential.actual_half_graph ε h a W w C p b P hε hh ha hw hW hb i θ)
    (forward_field_graph ε h a W w C p b P hε hh ha hw hW hb i j θ)

theorem reverse_graph (θ : ℝ) :
    (forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j θ,
      secondOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈
      (reverseFactor ε hε h modelDirections pointField (matterIndex j)).graph :=
  KFCausalMatterHalfStepAssembly.actual_reverse_graph ε hε h j _ _ _
    (reverse_field_graph ε h a W w C p b P hε hh ha hw hW hb i j θ)
    (KFCausalOuterMatterExponential.second_half_graph ε h a W w C p b P
      (innerDegree i) (degree j) hε hh ha hw hW hb θ)

theorem mixed_graph (θ : ℝ) :
    (action h hh θ u,secondOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈
      (matterSecond ε h j hε).graph :=
  (KFCausalOrderedOperatorComposition.composition_graph _ _ _ _).mpr
    ⟨_,forward_graph ε h a W w C p b P hε hh ha hw hW hb i j θ,
      reverse_graph ε h a W w C p b P hε hh ha hw hW hb i j θ⟩

include hW in
theorem mixed_domain (θ : ℝ) : action h hh θ u ∈ (matterSecond ε h j hε).domain :=
  LinearPMap.mem_domain_of_mem_graph (mixed_graph ε h a W w C p b P hε hh ha hw hW hb i j θ)

theorem halfState_continuous (m : ℕ) : Continuous (z m) :=
  KFCausalOuterMatterActionContinuity.halfOutput_continuous ε h a W w C p b P
    (innerDegree i) m hε hh ha hw hW hb (baselineHalfOutput ε h a W hε hh ha hb)

theorem fullState_continuous (m : ℕ) : Continuous (y m) :=
  KFCausalOuterMatterActionContinuity.full_line_continuous ε h a W w C p b P
    (innerDegree i) m hε hh ha hw hW hb
    (KFCausalSourcedWidthMatterSquare.baselineOutput ε h a W hε hh ha hb)

theorem forwardOutput_continuous :
    Continuous (forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j) :=
  halfState_continuous ε h a W w C p b P hε hh ha hw hW hb i (j.val+1)

theorem secondOutput_continuous :
    Continuous (secondOutput ε h a W w C p b P hε hh ha hw hW hb i j) :=
  (inverseL ε hε).continuous.comp
    (fullState_continuous ε h a W w C p b P hε hh ha hw hW hb i (degree j))

theorem secondOutput_norm_bound (θ : ℝ) :
    ‖secondOutput ε h a W w C p b P hε hh ha hw hW hb i j θ‖ ≤
      ‖inverseL ε hε‖ * (KFCausalOuterMatterHalfField.bound ε h a W w C p b P
        (innerDegree i) (degree j) * ‖KFCausalSourcedWidthMatterSquare.baselineOutput ε h a W hε hh ha hb‖) := by
  exact ((inverseL ε hε).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (KFCausalOuterMatterActionContinuity.full_line_norm_bound
      ε h a W w C p b P (innerDegree i) (degree j) hε hh ha hw hW hb θ _) (norm_nonneg _))

#print axioms forward_field_graph
#print axioms reverse_field_graph
#print axioms forward_graph
#print axioms reverse_graph
#print axioms mixed_graph
#print axioms mixed_domain
#print axioms halfState_continuous
#print axioms fullState_continuous
#print axioms forwardOutput_continuous
#print axioms secondOutput_continuous
#print axioms secondOutput_norm_bound
end
end UnifiedTheory.Audit.KFCausalOuterMatterSquare

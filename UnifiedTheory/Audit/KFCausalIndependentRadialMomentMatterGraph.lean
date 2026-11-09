/- Actual quadratic and quartic matter second graphs for the radial
moment states, through both exponential and field primitive graphs. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialMomentExponential
import UnifiedTheory.Audit.KFCausalClockMixedFieldGraph
import UnifiedTheory.Audit.KFCausalNaturalSecondHamiltonianGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalIndependentRadialMomentMatterGraph
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (split)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalPhysicalField (physicalField)
open KFCausalTransverseFieldSquare (fieldSquare)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalMatterHalfStepAssembly (fieldFactor)
open KFCausalNaturalSecondHamiltonianGraph (component)
open KFCausalReciprocalNeutralMatterSpectral (matterIndex)
open KFCausalMixedFieldGaussianStrip (degree)
open KFCausalPairedModeCoordinates (scale)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalIndependentRadialPacketMoments (momentState)
open KFCausalIndependentRadialMomentExponential
  (halfState fullState baselineHalfOutput multiplierAction_clockMixed)

variable (ε h a W wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (m n : ℕ) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hL : 1 ≤ wL)
  (hR : 1 ≤ wR) (hW : wL ≤ W) (hb : |h| ≤ ε/10)
local notation "α" => groundWidth h
local notation "c" => momentumScale h
local notation "z" => halfState ε h a W wL wR C p b P m n hε hh ha hL hR hW hb
local notation "y" => fullState ε h a W wL wR C p b P m n hε hh ha hL hR hW hb

theorem half_field_graph (k : ℕ) : (z k,z (k+1)) ∈ (physicalField pointField).graph := by
  apply (KFCausalClockMixedFieldGraph.pointField_graph_iff ε hε _ _).mpr
  filter_upwards [multiplierAction_clockMixed ε h a W wL wR C p b P m n hε hh ha hL hR hW hb
      k (-h/2) (by rw [abs_div,abs_neg,show |(2:ℝ)|=2 by norm_num]; linarith [abs_nonneg h])
      (baselineHalfOutput ε h a W hε hh ha hb),
    multiplierAction_clockMixed ε h a W wL wR C p b P m n hε hh ha hL hR hW hb
      (k+1) (-h/2) (by rw [abs_div,abs_neg,show |(2:ℝ)|=2 by norm_num]; linarith [abs_nonneg h])
      (baselineHalfOutput ε h a W hε hh ha hb)] with x hk hn
  have he : KFCausalIndependentRadialShiftedField.coefficient ε h α wL wR c
      ((x.2 0:ℂ)+(-h/2:ℝ)*Complex.I) ((split 2 4).symm x)=
      ((2*scale*(mixedMap ε hε x).2 2+(mixedMap ε hε x).2 3:ℝ):ℂ) := by
    rw [show ((x.2 0:ℂ)+(-h/2:ℝ)*Complex.I)=
      KFCausalTwoShearClockQuotient.shift (h/2) (x.2 0:ℂ) by
        unfold KFCausalTwoShearClockQuotient.shift; push_cast; ring,
      KFCausalIndependentRadialShiftedField.coefficient_half_line]
    exact KFCausalIndependentRadialShiftedField.point_real ε α wL wR c hε
      (groundWidth_positive h hh) (zero_lt_one.trans_le hR) x
  change (clockMixed ε hε (z (k+1))) x=_
  change (clockMixed ε hε (z k)) x=_ at hk
  change (clockMixed ε hε (z (k+1))) x=_ at hn
  rw [hn,hk]
  simp only [KFCausalIndependentRadialMomentMultiplier.multiplier,pow_succ,he]
  ring

theorem half_fieldSquare_graph (k : ℕ) : (z k,z (k+2)) ∈ (fieldSquare pointField).graph :=
  KFCausalClockMixedFieldGraph.fieldSquare_of_two_fields pointField _ _ _
    (half_field_graph ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k)
    (half_field_graph ε h a W wL wR C p b P m n hε hh ha hL hR hW hb (k+1))

def forwardOutput (j : Fin 2) : Hilbert := z (j.val+1)
def secondOutput (j : Fin 2) : Hilbert := inverseL ε hε (y (degree j))

theorem forward_field_graph (j : Fin 2) :
    (z 0,forwardOutput ε h a W wL wR C p b P m n hε hh ha hL hR hW hb j) ∈ (fieldFactor j).graph := by
  fin_cases j
  · exact half_field_graph ε h a W wL wR C p b P m n hε hh ha hL hR hW hb 0
  · exact half_fieldSquare_graph ε h a W wL wR C p b P m n hε hh ha hL hR hW hb 0

theorem reverse_field_graph (j : Fin 2) :
    (forwardOutput ε h a W wL wR C p b P m n hε hh ha hL hR hW hb j,z (degree j)) ∈
      (fieldFactor j).graph := by
  fin_cases j
  · exact half_field_graph ε h a W wL wR C p b P m n hε hh ha hL hR hW hb 1
  · exact half_fieldSquare_graph ε h a W wL wR C p b P m n hε hh ha hL hR hW hb 2

theorem matter_graph (j : Fin 2) :
    (momentState ε a h wL wR C p b P hε ha hh hL hR m n,
      secondOutput ε h a W wL wR C p b P m n hε hh ha hL hR hW hb j) ∈
      (component ε hε h (matterIndex j)).graph :=
  KFCausalMatterHalfStepAssembly.actual_second_graph ε hε h j _ _ _ _ _
    (KFCausalIndependentRadialMomentExponential.actual_half_graph
      ε h a W wL wR C p b P m n hε hh ha hL hR hW hb)
    (forward_field_graph ε h a W wL wR C p b P m n hε hh ha hL hR hW hb j)
    (reverse_field_graph ε h a W wL wR C p b P m n hε hh ha hL hR hW hb j)
    (KFCausalIndependentRadialMomentExponential.second_half_graph
      ε h a W wL wR C p b P m n hε hh ha hL hR hW hb (degree j))

include hW hb in
theorem matter_domain (j : Fin 2) :
    momentState ε a h wL wR C p b P hε ha hh hL hR m n ∈
      (component ε hε h (matterIndex j)).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (matter_graph ε h a W wL wR C p b P m n hε hh ha hL hR hW hb j)

#print axioms half_field_graph
#print axioms half_fieldSquare_graph
#print axioms forward_field_graph
#print axioms reverse_field_graph
#print axioms matter_graph
#print axioms matter_domain
end
end UnifiedTheory.Audit.KFCausalIndependentRadialMomentMatterGraph

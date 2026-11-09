/- The graph-limit estimates survive the actual inverse-clock ordering.
This is a closed subgraph of the existing ordered factor, with proved
D stability; no equality to the whole natural domain is asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectGraphClosure
import UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorOrderedDefectClosure
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectBounds
open UnifiedTheory.Audit.KFCausalClockFloorDefectGraphClosure
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)
  (a α β : ℝ) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)

def orderedGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (graphClosure ε hε hbar hh a α β ha hα hβ hw).comap
    ((inverseL ε hε).prodMap (ContinuousLinearMap.id ℂ Hilbert)).toLinearMap

theorem orderedGraph_closed :
    IsClosed (orderedGraph ε hε hbar hh a α β ha hα hβ hw : Set (Hilbert × Hilbert)) :=
  (Submodule.isClosed_topologicalClosure _).preimage
    ((inverseL ε hε).prodMap (ContinuousLinearMap.id ℂ Hilbert)).continuous

theorem orderedGraph_le_graph :
    orderedGraph ε hε hbar hh a α β ha hα hβ hw ≤ (orderedExponential ε hε hbar).graph := by
  rintro ⟨f,g⟩ hfg
  apply (ordered_graph_iff ε hε hbar f g).mpr
  exact graphClosure_le_graph ε hε hbar hh a α β ha hα hβ hw hfg

theorem orderedGraph_defect_invariant (f g : Hilbert)
    (hfg : (f,g) ∈ orderedGraph ε hε hbar hh a α β ha hα hβ hw) :
    (defectOperator ε hε f,shiftedDefect ε hε hbar hh g) ∈
      orderedGraph ε hε hbar hh a α β ha hα hβ hw := by
  have h := graphClosure_defect_invariant ε hε hbar hh a α β ha hα hβ hw (inverseL ε hε f,g) hfg
  change (inverseL ε hε (defectOperator ε hε f),shiftedDefect ε hε hbar hh g) ∈
    graphClosure ε hε hbar hh a α β ha hα hβ hw
  rw [inverseL_defect]
  exact h

/-- For T=exp(L/2) C^(-1/2), the actual form pairing <T f,T D^2 f>
has the proved sign throughout this closed, defect-invariant subgraph. -/
theorem orderedGraph_control (f g : Hilbert)
    (hfg : (f,g) ∈ orderedGraph ε hε hbar hh a α β ha hα hβ hw) :
    (f,g) ∈ (orderedExponential ε hε hbar).graph ∧
    (defectOperator ε hε f,shiftedDefect ε hε hbar hh g) ∈
      (orderedExponential ε hε hbar).graph ∧
    (defectOperator ε hε (defectOperator ε hε f),
      shiftedDefect ε hε hbar hh (shiftedDefect ε hε hbar hh g)) ∈
      (orderedExponential ε hε hbar).graph ∧
    ‖shiftedDefect ε hε hbar hh g-defectOperator ε hε g‖ ≤
      (2*|hbar|/ε)*‖defectOperator ε hε (defectOperator ε hε g)‖ ∧
    0 ≤ hbar*(inner ℂ g (shiftedDefect ε hε hbar hh (shiftedDefect ε hε hbar hh g))).im := by
  have h1 := orderedGraph_defect_invariant ε hε hbar hh a α β ha hα hβ hw f g hfg
  have h2 := orderedGraph_defect_invariant ε hε hbar hh a α β ha hα hβ hw _ _ h1
  exact ⟨orderedGraph_le_graph ε hε hbar hh a α β ha hα hβ hw hfg,
    orderedGraph_le_graph ε hε hbar hh a α β ha hα hβ hw h1,
    orderedGraph_le_graph ε hε hbar hh a α β ha hα hβ hw h2,
    shiftedDefect_difference ε hε hbar hh g,shiftedDefect_square_form_sign ε hε hbar hh g⟩

#print axioms orderedGraph_closed
#print axioms orderedGraph_le_graph
#print axioms orderedGraph_defect_invariant
#print axioms orderedGraph_control

end
end UnifiedTheory.Audit.KFCausalClockFloorOrderedDefectClosure

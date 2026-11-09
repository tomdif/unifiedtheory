/- Full natural-domain defect identities for T = exp(L/2) C^(-1/2).
No coherent-subgraph or graph-core hypothesis remains in these statements. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectFullDomain
import UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorOrderedDefectFullDomain
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectBounds
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)

theorem ordered_graph_defect (f g : Hilbert)
    (hfg : (f,g) ∈ (orderedExponential ε hε hbar).graph) :
    (defectOperator ε hε f,shiftedDefect ε hε hbar hh g) ∈
      (orderedExponential ε hε hbar).graph := by
  apply (ordered_graph_iff ε hε hbar _ _).mpr
  rw [inverseL_defect]
  exact KFCausalClockFloorDefectFullDomain.graph_defect ε hε hbar hh _ _
    ((ordered_graph_iff ε hε hbar f g).mp hfg)

include hh in
theorem ordered_defect_domain (f : Hilbert) (hf : f ∈ (orderedExponential ε hε hbar).domain) :
    defectOperator ε hε f ∈ (orderedExponential ε hε hbar).domain :=
  LinearPMap.mem_domain_of_mem_graph (ordered_graph_defect ε hε hbar hh f _
    ((orderedExponential ε hε hbar).mem_graph ⟨f,hf⟩))

theorem ordered_defect_action (f : (orderedExponential ε hε hbar).domain) :
    orderedExponential ε hε hbar ⟨defectOperator ε hε f,ordered_defect_domain ε hε hbar hh f f.property⟩ =
      shiftedDefect ε hε hbar hh (orderedExponential ε hε hbar f) :=
  (orderedExponential ε hε hbar).mem_graph_snd_inj'
    ((orderedExponential ε hε hbar).mem_graph _)
    (ordered_graph_defect ε hε hbar hh f _ ((orderedExponential ε hε hbar).mem_graph f)) rfl

include hh in
theorem ordered_defect_square_domain (f : Hilbert) (hf : f ∈ (orderedExponential ε hε hbar).domain) :
    defectOperator ε hε (defectOperator ε hε f) ∈ (orderedExponential ε hε hbar).domain :=
  ordered_defect_domain ε hε hbar hh _ (ordered_defect_domain ε hε hbar hh f hf)

theorem ordered_defect_commutator (f : (orderedExponential ε hε hbar).domain) :
    ‖orderedExponential ε hε hbar ⟨defectOperator ε hε f,ordered_defect_domain ε hε hbar hh f f.property⟩-
      defectOperator ε hε (orderedExponential ε hε hbar f)‖ ≤
      (2*|hbar|/ε)*‖defectOperator ε hε (defectOperator ε hε (orderedExponential ε hε hbar f))‖ := by
  rw [ordered_defect_action]
  exact shiftedDefect_difference ε hε hbar hh _

theorem ordered_defect_square_sign (f : (orderedExponential ε hε hbar).domain) :
    0 ≤ hbar*(inner ℂ (orderedExponential ε hε hbar f)
      (orderedExponential ε hε hbar ⟨defectOperator ε hε (defectOperator ε hε f),
        ordered_defect_square_domain ε hε hbar hh f f.property⟩)).im := by
  have h1 := ordered_graph_defect ε hε hbar hh _ _ ((orderedExponential ε hε hbar).mem_graph f)
  have h2 := ordered_graph_defect ε hε hbar hh _ _ h1
  have he := (orderedExponential ε hε hbar).mem_graph_snd_inj'
    ((orderedExponential ε hε hbar).mem_graph
      ⟨defectOperator ε hε (defectOperator ε hε f),ordered_defect_square_domain ε hε hbar hh f f.property⟩) h2 rfl
  dsimp only at he
  rw [he]
  exact shiftedDefect_square_form_sign ε hε hbar hh _

#print axioms ordered_graph_defect
#print axioms ordered_defect_domain
#print axioms ordered_defect_action
#print axioms ordered_defect_square_domain
#print axioms ordered_defect_commutator
#print axioms ordered_defect_square_sign

end
end UnifiedTheory.Audit.KFCausalClockFloorOrderedDefectFullDomain

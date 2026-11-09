/- Both actual ordered field-matter rows are preserved by the radial
test. The necessary field identities for its shifted OUTPUT are proved on
the entire natural graphs, then composed with the ordered exponential. -/
import UnifiedTheory.Audit.KFCausalMixedStripFieldGraph
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialOrdered

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialMatter
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalField (physicalField)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (action)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialExponential (shifted)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialOrdered (ordered_graph_action)
open UnifiedTheory.Audit.KFCausalMixedRadialStripFamily
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMultiplier (stripBound)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shift_bound)

variable (ε h δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ)

theorem shifted_field_graph (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (f g : Hilbert)
    (hfg : (f,g) ∈ (physicalField pointField).graph) :
    (shifted ε h δ v hε hδ y hy f,shifted ε h δ v hε hδ y hy g) ∈ (physicalField pointField).graph :=
  KFCausalMixedStripFieldGraph.field_graph_action ε hε (family ε h δ v) (Real.pi*ε/3) (stripBound ε δ v)
    (family_line_continuous ε h δ v hε) (Real.exp_pos _).le (family_bound ε h δ v hε hδ) y hy f g hfg

theorem shifted_square_graph (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (f g : Hilbert)
    (hfg : (f,g) ∈ (fieldSquare pointField).graph) :
    (shifted ε h δ v hε hδ y hy f,shifted ε h δ v hε hδ y hy g) ∈ (fieldSquare pointField).graph :=
  KFCausalMixedStripFieldGraph.square_graph_action ε hε (family ε h δ v) (Real.pi*ε/3) (stripBound ε δ v)
    (family_line_continuous ε h δ v hε) (Real.exp_pos _).le (family_bound ε h δ v hε hδ) y hy f g hfg

variable (hh : |h| ≤ 2*Real.pi*ε/3)

theorem linear_matter_graph_action (f g : Hilbert)
    (hfg : (f,g) ∈ (matterFactor ε hε h (physicalField pointField)).graph) :
    (action h δ v hδ f,shifted ε h δ v hε hδ (-h/2) (shift_bound ε h hh) g) ∈
      (matterFactor ε hε h (physicalField pointField)).graph := by
  rw [matterFactor,composition_graph] at hfg ⊢
  obtain ⟨u,hu,hg⟩ := hfg
  exact ⟨shifted ε h δ v hε hδ (-h/2) (shift_bound ε h hh) u,
    ordered_graph_action ε h δ v hε hδ hh f u hu,
    shifted_field_graph ε h δ v hε hδ (-h/2) (shift_bound ε h hh) u g hg⟩

theorem quadratic_matter_graph_action (f g : Hilbert)
    (hfg : (f,g) ∈ (matterFactor ε hε h (fieldSquare pointField)).graph) :
    (action h δ v hδ f,shifted ε h δ v hε hδ (-h/2) (shift_bound ε h hh) g) ∈
      (matterFactor ε hε h (fieldSquare pointField)).graph := by
  rw [matterFactor,composition_graph] at hfg ⊢
  obtain ⟨u,hu,hg⟩ := hfg
  exact ⟨shifted ε h δ v hε hδ (-h/2) (shift_bound ε h hh) u,
    ordered_graph_action ε h δ v hε hδ hh f u hu,
    shifted_square_graph ε h δ v hε hδ (-h/2) (shift_bound ε h hh) u g hg⟩

#print axioms shifted_field_graph
#print axioms shifted_square_graph
#print axioms linear_matter_graph_action
#print axioms quadratic_matter_graph_action

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialMatter

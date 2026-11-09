/- Weighted domain transfer for the actual physical linear and quadratic
matter factors. Their outputs intertwine with B, rather than commuting
with the real defect D. All unbounded multiplication domains are checked. -/
import UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical
import UnifiedTheory.Audit.KFCausalClockFloorOrderedDefectFullDomain
import UnifiedTheory.Audit.KFCausalClockFloorTrialMatter

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorMatterDefect
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical
open UnifiedTheory.Audit.KFCausalClockFloorOrderedDefectFullDomain
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)

theorem physicalField_shifted_graph (l : Transverse →L[ℝ] ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (physicalField l).graph) :
    (shiftedDefect ε hε hbar hh f,shiftedDefect ε hε hbar hh g) ∈ (physicalField l).graph := by
  apply (physicalField_graph l _ _).mpr
  filter_upwards [shiftedDefect_physical_coe ε hε hbar hh f,
    shiftedDefect_physical_coe ε hε hbar hh g,(physicalField_graph l f g).mp hfg] with x hf hg hm
  rw [hg,hf,hm]
  ring

theorem fieldSquare_shifted_graph (l : Transverse →L[ℝ] ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (fieldSquare l).graph) :
    (shiftedDefect ε hε hbar hh f,shiftedDefect ε hε hbar hh g) ∈ (fieldSquare l).graph := by
  apply (fieldSquare_graph l _ _).mpr
  filter_upwards [shiftedDefect_physical_coe ε hε hbar hh f,
    shiftedDefect_physical_coe ε hε hbar hh g,(fieldSquare_graph l f g).mp hfg] with x hf hg hm
  rw [hg,hf,hm]
  ring

theorem matter_graph_defect (M : Hilbert →ₗ.[ℂ] Hilbert)
    (hM : ∀ f g : Hilbert, (f,g) ∈ M.graph →
      (shiftedDefect ε hε hbar hh f,shiftedDefect ε hε hbar hh g) ∈ M.graph)
    (f g : Hilbert) (hfg : (f,g) ∈ (matterFactor ε hε hbar M).graph) :
    (defectOperator ε hε f,shiftedDefect ε hε hbar hh g) ∈ (matterFactor ε hε hbar M).graph := by
  obtain ⟨u,hu,hg⟩ := (composition_graph _ _ f g).mp hfg
  exact (composition_graph _ _ _ _).mpr
    ⟨shiftedDefect ε hε hbar hh u,ordered_graph_defect ε hε hbar hh f u hu,hM u g hg⟩

theorem linear_matter_graph_defect (l : Transverse →L[ℝ] ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (matterFactor ε hε hbar (physicalField l)).graph) :
    (defectOperator ε hε f,shiftedDefect ε hε hbar hh g) ∈
      (matterFactor ε hε hbar (physicalField l)).graph :=
  matter_graph_defect ε hε hbar hh _ (physicalField_shifted_graph ε hε hbar hh l) f g hfg

theorem quadratic_matter_graph_defect (l : Transverse →L[ℝ] ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (matterFactor ε hε hbar (fieldSquare l)).graph) :
    (defectOperator ε hε f,shiftedDefect ε hε hbar hh g) ∈
      (matterFactor ε hε hbar (fieldSquare l)).graph :=
  matter_graph_defect ε hε hbar hh _ (fieldSquare_shifted_graph ε hε hbar hh l) f g hfg

#print axioms physicalField_shifted_graph
#print axioms fieldSquare_shifted_graph
#print axioms matter_graph_defect
#print axioms linear_matter_graph_defect
#print axioms quadratic_matter_graph_defect

end
end UnifiedTheory.Audit.KFCausalClockFloorMatterDefect

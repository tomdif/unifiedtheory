/- The actual localized neutral-position observable preserves the entire
natural ordered exponential and both physical matter graphs. The output is
the bounded imaginary-shift multiplier. These are unaveraged natural graphs;
charge-averaged full-form preservation is not asserted. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMultiplier
import UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
import UnifiedTheory.Audit.KFCausalClockFloorTrialMatter

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMatter
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMultiplier
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shift_bound)
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)

variable (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ)

theorem preserves_relation (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (a : Configuration → ℂ) (f g : Hilbert)
    (hfg : g =ᵐ[volume] fun x => a x*f x) :
    action ε δ v hε hδ y hy g =ᵐ[volume] fun x => a x*action ε δ v hε hδ y hy f x := by
  filter_upwards [action_coe ε δ v hε hδ y hy f,action_coe ε δ v hε hδ y hy g,hfg] with x hf hg hx
  rw [hf,hg,hx]
  ring

theorem clockHalf_graph_action (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (f g : Hilbert)
    (hfg : (f,g) ∈ (clockHalf ε).graph) :
    (action ε δ v hε hδ y hy f,action ε δ v hε hδ y hy g) ∈ (clockHalf ε).graph :=
  (clockHalf_graph ε _ _).mpr (preserves_relation ε δ v hε hδ y hy _ f g ((clockHalf_graph ε f g).mp hfg))

theorem inverseHalf_graph_action (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (f g : Hilbert)
    (hfg : (f,g) ∈ (inverseClockHalf ε).graph) :
    (action ε δ v hε hδ y hy f,action ε δ v hε hδ y hy g) ∈ (inverseClockHalf ε).graph :=
  (inverseClockHalf_graph ε _ _).mpr
    (preserves_relation ε δ v hε hδ y hy _ f g ((inverseClockHalf_graph ε f g).mp hfg))

theorem field_graph_action (y : ℝ) (hy : |y| ≤ Real.pi*ε/3)
    (l : Transverse →L[ℝ] ℝ) (f g : Hilbert) (hfg : (f,g) ∈ (physicalField l).graph) :
    (action ε δ v hε hδ y hy f,action ε δ v hε hδ y hy g) ∈ (physicalField l).graph :=
  (physicalField_graph l _ _).mpr
    (preserves_relation ε δ v hε hδ y hy _ f g ((physicalField_graph l f g).mp hfg))

theorem square_graph_action (y : ℝ) (hy : |y| ≤ Real.pi*ε/3)
    (l : Transverse →L[ℝ] ℝ) (f g : Hilbert) (hfg : (f,g) ∈ (fieldSquare l).graph) :
    (action ε δ v hε hδ y hy f,action ε δ v hε hδ y hy g) ∈ (fieldSquare l).graph :=
  (fieldSquare_graph l _ _).mpr
    (preserves_relation ε δ v hε hδ y hy _ f g ((fieldSquare_graph l f g).mp hfg))

variable (h : ℝ) (hh : |h| ≤ 2*Real.pi*ε/3) (h0 : |(0:ℝ)| ≤ Real.pi*ε/3)

theorem exponential_graph_action (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h (1/2)).graph) :
    (action ε δ v hε hδ 0 h0 f,action ε δ v hε hδ (-h/2) (shift_bound ε h hh) g) ∈
      (longitudinalExponential ε hε h (1/2)).graph :=
  KFCausalStripFamilyExponentialGraph.graph_multiplier (family ε δ v) (Real.pi*ε/3)
    (stripBound ε δ v) (family_analytic ε δ v hε) (family_line_continuous ε δ v hε)
    (Real.exp_pos _).le (family_bound ε δ v hε hδ) ε hε h h0 (shift_bound ε h hh) f g hfg

theorem ordered_graph_action (f g : Hilbert) (hfg : (f,g) ∈ (orderedExponential ε hε h).graph) :
    (action ε δ v hε hδ 0 h0 f,action ε δ v hε hδ (-h/2) (shift_bound ε h hh) g) ∈
      (orderedExponential ε hε h).graph := by
  rw [orderedExponential,composition_graph] at hfg ⊢
  obtain ⟨u,hu,hg⟩ := hfg
  exact ⟨action ε δ v hε hδ 0 h0 u,inverseHalf_graph_action ε δ v hε hδ 0 h0 f u hu,
    exponential_graph_action ε δ v hε hδ h hh h0 u g hg⟩

theorem linear_matter_graph_action (l : Transverse →L[ℝ] ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (matterFactor ε hε h (physicalField l)).graph) :
    (action ε δ v hε hδ 0 h0 f,action ε δ v hε hδ (-h/2) (shift_bound ε h hh) g) ∈
      (matterFactor ε hε h (physicalField l)).graph := by
  rw [matterFactor,composition_graph] at hfg ⊢
  obtain ⟨u,hu,hg⟩ := hfg
  exact ⟨action ε δ v hε hδ (-h/2) (shift_bound ε h hh) u,
    ordered_graph_action ε δ v hε hδ h hh h0 f u hu,
    field_graph_action ε δ v hε hδ (-h/2) (shift_bound ε h hh) l u g hg⟩

theorem quadratic_matter_graph_action (l : Transverse →L[ℝ] ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (matterFactor ε hε h (fieldSquare l)).graph) :
    (action ε δ v hε hδ 0 h0 f,action ε δ v hε hδ (-h/2) (shift_bound ε h hh) g) ∈
      (matterFactor ε hε h (fieldSquare l)).graph := by
  rw [matterFactor,composition_graph] at hfg ⊢
  obtain ⟨u,hu,hg⟩ := hfg
  exact ⟨action ε δ v hε hδ (-h/2) (shift_bound ε h hh) u,
    ordered_graph_action ε δ v hε hδ h hh h0 f u hu,
    square_graph_action ε δ v hε hδ (-h/2) (shift_bound ε h hh) l u g hg⟩

theorem output_norm (g : Hilbert) :
    ‖action ε δ v hε hδ (-h/2) (shift_bound ε h hh) g‖ ≤
      Real.exp (v^2*h^2/(8*δ*ε^2))*‖g‖ := by
  convert action_norm ε δ v hε hδ (-h/2) (shift_bound ε h hh) g using 1
  congr 2
  ring

#print axioms preserves_relation
#print axioms clockHalf_graph_action
#print axioms inverseHalf_graph_action
#print axioms field_graph_action
#print axioms square_graph_action
#print axioms exponential_graph_action
#print axioms ordered_graph_action
#print axioms linear_matter_graph_action
#print axioms quadratic_matter_graph_action
#print axioms output_norm

end
end UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMatter

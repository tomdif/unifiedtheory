/- Bounded clock multiplication preserves the unbounded field graphs.
The reduced actual T B output therefore inherits both matter weights
from the known shifted Gaussian outputs at two clock widths. -/
import UnifiedTheory.Audit.KFCausalCoherentMomentumOutputReduction
import UnifiedTheory.Audit.KFCausalClockFloorMatterDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalBoundedClockMatterGraphs
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPhysicalField (physicalField physicalField_graph)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare fieldSquare_graph)
open UnifiedTheory.Audit.KFCausalBoundedClockCharge (multiplier multiplier_coe)
open UnifiedTheory.Audit.KFCausalClockFloorMatterDefect (physicalField_shifted_graph fieldSquare_shifted_graph)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shiftedDefect)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator (correction)
open UnifiedTheory.Audit.KFCausalShiftedClockMomentOperator (inverseOperator momentOperator)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalCoherentMomentumOutputReduction (inverseOperator_eq reducedOutput)

theorem field_graph (m : ℝ → ℂ) (hm : Measurable m) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ s, ‖m s‖ ≤ C)
    (l : Transverse →L[ℝ] ℝ) (f g : Hilbert) (hg : (f,g) ∈ (physicalField l).graph) :
    (multiplier m hm C hC hb f,multiplier m hm C hC hb g) ∈ (physicalField l).graph := by
  apply (physicalField_graph l _ _).mpr
  filter_upwards [multiplier_coe m hm C hC hb f,multiplier_coe m hm C hC hb g,
    (physicalField_graph l f g).mp hg] with x hf hg' he
  rw [hf,hg',he]
  ring

theorem square_graph (m : ℝ → ℂ) (hm : Measurable m) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ s, ‖m s‖ ≤ C)
    (l : Transverse →L[ℝ] ℝ) (f g : Hilbert) (hg : (f,g) ∈ (fieldSquare l).graph) :
    (multiplier m hm C hC hb f,multiplier m hm C hC hb g) ∈ (fieldSquare l).graph := by
  apply (fieldSquare_graph l _ _).mpr
  filter_upwards [multiplier_coe m hm C hC hb f,multiplier_coe m hm C hC hb g,
    (fieldSquare_graph l f g).mp hg] with x hf hg' he
  rw [hf,hg',he]
  ring

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hb : |h| ≤ 2*Real.pi*ε/3)
  (l : Transverse →L[ℝ] ℝ)
local notation "Z" => shiftedDefect ε hε h hb

theorem correction_field_graph (f g : Hilbert) (hg : (f,g) ∈ (physicalField l).graph) :
    (correction ε hε h hb f,correction ε hε h hb g) ∈ (physicalField l).graph :=
  (physicalField l).graph.smul_mem _ (physicalField_shifted_graph ε hε h hb l _ _
    ((physicalField l).graph.sub_mem hg (physicalField_shifted_graph ε hε h hb l f g hg)))

theorem correction_square_graph (f g : Hilbert) (hg : (f,g) ∈ (fieldSquare l).graph) :
    (correction ε hε h hb f,correction ε hε h hb g) ∈ (fieldSquare l).graph :=
  (fieldSquare l).graph.smul_mem _ (fieldSquare_shifted_graph ε hε h hb l _ _
    ((fieldSquare l).graph.sub_mem hg (fieldSquare_shifted_graph ε hε h hb l f g hg)))

theorem reducedOutput_field_graph (p : ℝ) (f f' g g' : Hilbert)
    (hf : (f,f') ∈ (physicalField l).graph) (hg : (g,g') ∈ (physicalField l).graph) :
    (reducedOutput ε a h hε ha hb p f g,reducedOutput ε a h hε ha hb p f' g') ∈ (physicalField l).graph := by
  have hi : (inverseOperator ε (-h/2) hε (shift_bound ε h hb) f,
      inverseOperator ε (-h/2) hε (shift_bound ε h hb) f') ∈ (physicalField l).graph := by
    rw [inverseOperator_eq ε h hε hb]
    exact (physicalField l).graph.smul_mem _ (physicalField_shifted_graph ε hε h hb l f f' hf)
  have hm : (momentOperator ε a (-h/2) ha g,momentOperator ε a (-h/2) ha g') ∈ (physicalField l).graph :=
    field_graph _ _ _ _ _ l g g' hg
  exact (physicalField l).graph.sub_mem ((physicalField l).graph.smul_mem _
    ((physicalField l).graph.sub_mem ((physicalField l).graph.smul_mem _ hi)
      ((physicalField l).graph.smul_mem _ hm))) (correction_field_graph ε h hε hb l f f' hf)

theorem reducedOutput_square_graph (p : ℝ) (f f' g g' : Hilbert)
    (hf : (f,f') ∈ (fieldSquare l).graph) (hg : (g,g') ∈ (fieldSquare l).graph) :
    (reducedOutput ε a h hε ha hb p f g,reducedOutput ε a h hε ha hb p f' g') ∈ (fieldSquare l).graph := by
  have hi : (inverseOperator ε (-h/2) hε (shift_bound ε h hb) f,
      inverseOperator ε (-h/2) hε (shift_bound ε h hb) f') ∈ (fieldSquare l).graph := by
    rw [inverseOperator_eq ε h hε hb]
    exact (fieldSquare l).graph.smul_mem _ (fieldSquare_shifted_graph ε hε h hb l f f' hf)
  have hm : (momentOperator ε a (-h/2) ha g,momentOperator ε a (-h/2) ha g') ∈ (fieldSquare l).graph :=
    square_graph _ _ _ _ _ l g g' hg
  exact (fieldSquare l).graph.sub_mem ((fieldSquare l).graph.smul_mem _
    ((fieldSquare l).graph.sub_mem ((fieldSquare l).graph.smul_mem _ hi)
      ((fieldSquare l).graph.smul_mem _ hm))) (correction_square_graph ε h hε hb l f f' hf)

#print axioms field_graph
#print axioms square_graph
#print axioms correction_field_graph
#print axioms correction_square_graph
#print axioms reducedOutput_field_graph
#print axioms reducedOutput_square_graph
end
end UnifiedTheory.Audit.KFCausalBoundedClockMatterGraphs

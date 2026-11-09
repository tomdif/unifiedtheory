/- The two physical field powers commute with bounded clock corrections
and with pure-clock momentum on their actual composition graphs. This
identifies a matter weak response while retaining the field-weighted JG
output; it does not replace FJG by J(FG). -/
import UnifiedTheory.Audit.KFCausalBoundedClockMatterGraphs
import UnifiedTheory.Audit.KFCausalClockFloorPureClockFields

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalPhysicalField (physicalField physicalField_graph)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare fieldSquare_graph)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator defectOperator_coe)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shiftedDefect)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (pureCorrection shearCorrection)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse (response pure_pairing_real)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator (correction)

def fieldPower (l : Transverse →L[ℝ] ℝ) : Fin 2 → Hilbert →ₗ.[ℂ] Hilbert :=
  ![physicalField l,fieldSquare l]

theorem fieldPower_graph (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (f g : Hilbert) :
    (f,g) ∈ (fieldPower l i).graph ↔
      g =ᵐ[volume] fun x : Configuration => (l x.2:ℂ)^(i.val+1)*f x := by
  fin_cases i
  · change (f,g) ∈ (physicalField l).graph ↔
      g =ᵐ[volume] fun x : Configuration => (l x.2:ℂ)^1*f x
    simpa only [pow_one] using physicalField_graph l f g
  · exact fieldSquare_graph l f g

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
local notation "F" => fieldPower l i
local notation "B" => pureMomentum ε hε h

include hh in
theorem momentum_interchange (f g b k : Hilbert) (hg : (f,g) ∈ (F).graph) (hB : (f,b) ∈ (B).graph) :
    (b,k) ∈ (F).graph ↔ (g,k) ∈ (B).graph := by
  fin_cases i
  · exact KFCausalClockFloorPureClockFields.field_interchange ε hε l h hh f g b k hg hB
  · exact KFCausalClockFloorPureClockFields.square_interchange ε hε l h hh f g b k hg hB

theorem defect_graph (f g : Hilbert) (hg : (f,g) ∈ (F).graph) :
    (defectOperator ε hε f,defectOperator ε hε g) ∈ (F).graph := by
  apply (fieldPower_graph l i _ _).mpr
  filter_upwards [defectOperator_coe ε hε f,defectOperator_coe ε hε g,
    (fieldPower_graph l i f g).mp hg] with x hf hg' he
  rw [hf,hg',he]
  ring

theorem shifted_graph (f g : Hilbert) (hg : (f,g) ∈ (F).graph) :
    (shiftedDefect ε hε h hb f,shiftedDefect ε hε h hb g) ∈ (F).graph := by
  fin_cases i
  · exact KFCausalClockFloorMatterDefect.physicalField_shifted_graph ε hε h hb l f g hg
  · exact KFCausalClockFloorMatterDefect.fieldSquare_shifted_graph ε hε h hb l f g hg

theorem correction_graph (f g : Hilbert) (hg : (f,g) ∈ (F).graph) :
    (correction ε hε h hb f,correction ε hε h hb g) ∈ (F).graph := by
  fin_cases i
  · exact KFCausalBoundedClockMatterGraphs.correction_field_graph ε h hε hb l f g hg
  · exact KFCausalBoundedClockMatterGraphs.correction_square_graph ε h hε hb l f g hg

theorem pureCorrection_graph (g u j v : Hilbert) (hg : (g,u) ∈ (F).graph) (hj : (j,v) ∈ (F).graph) :
    (pureCorrection ε hε h hb g j,pureCorrection ε hε h hb u v) ∈ (F).graph :=
  (F).graph.sub_mem (correction_graph ε h hε hb l i g u hg)
    ((F).graph.smul_mem (1/(ε:ℂ)) ((F).graph.sub_mem (defect_graph ε hε l i j v hj)
      (shifted_graph ε h hε hb l i j v hj)))

include hh in
theorem weighted_momentum_graph (g bg tb jg u v j : Hilbert)
    (hbg : (g,bg) ∈ (B).graph) (he : bg-tb = pureCorrection ε hε h hb g jg)
    (hu : (g,u) ∈ (F).graph) (hv : (tb,v) ∈ (F).graph) (hj : (jg,j) ∈ (F).graph) :
    (u,v+pureCorrection ε hε h hb u j) ∈ (B).graph := by
  apply (momentum_interchange ε h hε hh l i g u bg _ hu hbg).mp
  have he' : bg = tb+pureCorrection ε hε h hb g jg := by rw [← he]; abel
  rw [he']
  exact (F).graph.add_mem hv (pureCorrection_graph ε h hε hb l i g u jg j hu hj)

include hh in
theorem weighted_weak_response (g bg tb jg u v j : Hilbert)
    (hbg : (g,bg) ∈ (B).graph) (he : bg-tb = pureCorrection ε hε h hb g jg)
    (hu : (g,u) ∈ (F).graph) (hv : (tb,v) ∈ (F).graph) (hj : (jg,j) ∈ (F).graph) :
    (-2/h)*(inner ℂ u v).im = response ε hε h hb u j := by
  have hp := pure_pairing_real ε hε h hh u (v+pureCorrection ε hε h hb u j)
    (weighted_momentum_graph ε h hε hh hb l i g bg tb jg u v j hbg he hu hv hj)
  rw [inner_add_right,Complex.add_im] at hp
  unfold response
  linear_combination (-2/h)*hp

#print axioms fieldPower_graph
#print axioms momentum_interchange
#print axioms defect_graph
#print axioms shifted_graph
#print axioms correction_graph
#print axioms pureCorrection_graph
#print axioms weighted_momentum_graph
#print axioms weighted_weak_response
end
end UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator

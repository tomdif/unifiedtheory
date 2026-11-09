/- The actual pure-clock/vacuum commutator on the constructed joint
 graph core. All B,T composition outputs are derived. The transverse
 shear correction is retained and bounded, not assumed to vanish. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockJointDomain
import UnifiedTheory.Audit.KFCausalClockFloorJointMomentumCore
import UnifiedTheory.Audit.KFCausalClockFloorVacuumMomentumResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain (clockInverse)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockJointDomain
open UnifiedTheory.Audit.KFCausalClockFloorJointMomentumCore (regularGraph)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator (correction)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shiftedDefect)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectBounds (shiftedDefect_difference)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedDefectFullDomain (ordered_graph_defect)
open UnifiedTheory.Audit.KFCausalClockFloorVacuumMomentumResponse (correction_sharp_bound)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hbound : |h| ≤ 2*Real.pi*ε/3)
local notation "B" => pureMomentum ε hε h
local notation "J" => shearMomentum h
local notation "T" => orderedExponential ε hε h
local notation "D" => defectOperator ε hε
local notation "Z" => shiftedDefect ε hε h hbound
local notation "G" => regularGraph ε hε h

def shearCorrection : Hilbert →L[ℂ] Hilbert := (1/(ε:ℂ)) • (D-Z)
def pureCorrection (g jg : Hilbert) : Hilbert := correction ε hε h hbound g-shearCorrection ε hε h hbound jg

theorem shearCorrection_bound (j : Hilbert) :
    ‖shearCorrection ε hε h hbound j‖ ≤ (2*|h|/ε^2)*‖D (D j)‖ := by
  change ‖(1/(ε:ℂ)) • (D j-Z j)‖ ≤ _
  rw [norm_smul,norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
  have hz : ‖D j-Z j‖ ≤ (2*|h|/ε)*‖D (D j)‖ := by
    rw [norm_sub_rev]
    exact shiftedDefect_difference ε hε h hbound j
  calc
    _ ≤ (1/ε)*((2*|h|/ε)*‖D (D j)‖) := mul_le_mul_of_nonneg_left hz (by positivity)
    _ = _ := by ring

theorem pureCorrection_bound (g jg : Hilbert) :
    ‖pureCorrection ε hε h hbound g jg‖ ≤
      (|h|/(4*ε))*‖g‖+(2*|h|/ε^2)*‖D (D jg)‖ :=
  (norm_sub_le _ _).trans (add_le_add (correction_sharp_bound ε hε h hbound g)
    (shearCorrection_bound ε hε h hbound jg))

omit hbound in
theorem core_pure_domains (hne : h ≠ 0) (f g : Hilbert) (hfg : (f,g) ∈ G) :
    f ∈ (B).domain ∧ g ∈ (B).domain :=
  ⟨joint_domain ε hε h hne f hfg.1.2.1 hfg.2.1,joint_domain ε hε h hne g hfg.1.2.2 hfg.2.2⟩

theorem core_compositions (hne : h ≠ 0) (f g : Hilbert) (hfg : (f,g) ∈ G) :
    ∃ b tb bg jg : Hilbert, (f,b) ∈ (B).graph ∧ (b,tb) ∈ (T).graph ∧
      (g,bg) ∈ (B).graph ∧ (g,jg) ∈ (J).graph ∧
      bg-tb = pureCorrection ε hε h hbound g jg := by
  obtain ⟨lf,tlf,ltf,jf,jtf,hl,htl,hlt,he,hj,htj,hjt⟩ :=
    KFCausalClockFloorJointMomentumCore.common_compositions ε hε h hne hbound f g hfg
  refine ⟨lf-clockInverse ε hε jf,tlf-(1/(ε:ℂ)) • Z jtf,ltf-clockInverse ε hε jtf,jtf,
    graph_decomposition ε hε h hne f lf jf hl hj,?_,
    graph_decomposition ε hε h hne g ltf jtf hlt hjt,hjt,?_⟩
  · exact (T).graph.sub_mem htl ((T).graph.smul_mem (1/(ε:ℂ))
      (ordered_graph_defect ε hε h hbound jf jtf htj))
  · change (ltf-(1/(ε:ℂ)) • D jtf)-(tlf-(1/(ε:ℂ)) • Z jtf) =
      correction ε hε h hbound g-(1/(ε:ℂ)) • (D jtf-Z jtf)
    rw [smul_sub,← he]
    abel

theorem commutator_graph (hne : h ≠ 0) (f g b tb bg jg : Hilbert) (hfg : (f,g) ∈ G)
    (hb : (f,b) ∈ (B).graph) (htb : (b,tb) ∈ (T).graph)
    (hbg : (g,bg) ∈ (B).graph) (hjg : (g,jg) ∈ (J).graph) :
    bg-tb = pureCorrection ε hε h hbound g jg := by
  obtain ⟨b',tb',bg',jg',hb',htb',hbg',hjg',he⟩ := core_compositions ε hε h hbound hne f g hfg
  have eb : b = b' := (B).mem_graph_snd_inj' hb hb' rfl
  have etb : tb = tb' := (T).mem_graph_snd_inj' htb htb' eb
  have ebg : bg = bg' := (B).mem_graph_snd_inj' hbg hbg' rfl
  have ejg : jg = jg' := (J).mem_graph_snd_inj' hjg hjg' rfl
  simpa only [etb,ebg,ejg] using he

include hbound in
theorem commutator_bound (hne : h ≠ 0) (f g b tb bg jg : Hilbert) (hfg : (f,g) ∈ G)
    (hb : (f,b) ∈ (B).graph) (htb : (b,tb) ∈ (T).graph)
    (hbg : (g,bg) ∈ (B).graph) (hjg : (g,jg) ∈ (J).graph) :
    ‖bg-tb‖ ≤ (|h|/(4*ε))*‖g‖+(2*|h|/ε^2)*‖D (D jg)‖ := by
  rw [commutator_graph ε hε h hbound hne f g b tb bg jg hfg hb htb hbg hjg]
  exact pureCorrection_bound ε hε h hbound g jg

#print axioms shearCorrection_bound
#print axioms pureCorrection_bound
#print axioms core_pure_domains
#print axioms core_compositions
#print axioms commutator_graph
#print axioms commutator_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator

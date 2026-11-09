/- Actual ordered matter/momentum compositions on the coherent span.
The extra FJG graphs follow from derived fourth moments. The signed weak
response retains this weighted shear output and has a quantitative bound
in its defect-weighted norm, not yet in Hamiltonian energy alone. -/
import UnifiedTheory.Audit.KFCausalCoherentWeightedShearDomains
import UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentMatterWeakResponse
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (pureCorrection)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse (response pure_pairing_real)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower weighted_momentum_graph)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
local notation "F" => fieldPower l i
local notation "T" => orderedExponential ε hε h
local notation "B" => pureMomentum ε hε h
local notation "J" => shearMomentum h
local notation "D" => defectOperator ε hε

theorem actual_composition (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (b g jg u v : Hilbert) (hB : (f,b) ∈ (B).graph) (hg : (f,g) ∈ (T).graph)
    (hj : (g,jg) ∈ (J).graph) (hu : (f,u) ∈ (matterFactor ε hε h (F)).graph)
    (hv : (b,v) ∈ (matterFactor ε hε h (F)).graph) :
    ∃ j : Hilbert, (jg,j) ∈ (F).graph ∧ (u,v+pureCorrection ε hε h hb u j) ∈ (B).graph := by
  obtain ⟨g',hg',hu'⟩ := (composition_graph _ _ _ _).mp hu
  obtain ⟨tb,htb,hv'⟩ := (composition_graph _ _ _ _).mp hv
  have eg : g' = g := (T).mem_graph_snd_inj' hg' hg rfl
  have hFu : (g,u) ∈ (F).graph := eg ▸ hu'
  obtain ⟨b',tb',bg,jg',hB',htb',hbg,hjg',he⟩ :=
    KFCausalCoherentVacuumCommutator.span_compositions ε a h hε ha hh hb f hf g hg
  have eb : b' = b := (B).mem_graph_snd_inj' hB' hB rfl
  have et : tb' = tb := (T).mem_graph_snd_inj' htb' htb eb
  have ej : jg' = jg := (J).mem_graph_snd_inj' hjg' hj rfl
  have he' : bg-tb = pureCorrection ε hε h hb g jg := by simpa only [et,ej] using he
  have hd : jg ∈ (F).domain := by
    have hd := KFCausalCoherentWeightedShearDomains.actual_shear_field_domains ε a h hε ha hh hb f hf g jg hg hj l
    fin_cases i
    · exact hd.1
    · exact hd.2
  let j : Hilbert := (F) ⟨jg,hd⟩
  have hj' : (jg,j) ∈ (F).graph := (F).mem_graph ⟨jg,hd⟩
  exact ⟨j,hj',weighted_momentum_graph ε h hε hh hb l i g bg tb jg u v j hbg he' hFu hv' hj'⟩

theorem actual_weak_response (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (b g jg u v j : Hilbert) (hB : (f,b) ∈ (B).graph) (hg : (f,g) ∈ (T).graph)
    (hj : (g,jg) ∈ (J).graph) (hu : (f,u) ∈ (matterFactor ε hε h (F)).graph)
    (hv : (b,v) ∈ (matterFactor ε hε h (F)).graph) (hj' : (jg,j) ∈ (F).graph) :
    (-2/h)*(inner ℂ u v).im = response ε hε h hb u j := by
  obtain ⟨j',hF,hc⟩ := actual_composition ε a h hε ha hh hb l i f hf b g jg u v hB hg hj hu hv
  have ej : j' = j := (F).mem_graph_snd_inj' hF hj' rfl
  have hp := pure_pairing_real ε hε h hh u (v+pureCorrection ε hε h hb u j') hc
  rw [ej,inner_add_right,Complex.add_im] at hp
  unfold response
  linear_combination (-2/h)*hp

include hb in
theorem actual_response_bounds (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (b g jg u v j : Hilbert) (hB : (f,b) ∈ (B).graph) (hg : (f,g) ∈ (T).graph)
    (hj : (g,jg) ∈ (J).graph) (hu : (f,u) ∈ (matterFactor ε hε h (F)).graph)
    (hv : (b,v) ∈ (matterFactor ε hε h (F)).graph) (hj' : (jg,j) ∈ (F).graph) :
    -(4/ε^2)*‖u‖*‖D (D j)‖ ≤ (-2/h)*(inner ℂ u v).im ∧
      (-2/h)*(inner ℂ u v).im ≤ (1/(2*ε))*‖u‖^2+(4/ε^2)*‖u‖*‖D (D j)‖ := by
  rw [actual_weak_response ε a h hε ha hh hb l i f hf b g jg u v j hB hg hj hu hv hj']
  exact KFCausalClockFloorPureClockVacuumResponse.response_bounds ε hε h hb hh u j

#print axioms actual_composition
#print axioms actual_weak_response
#print axioms actual_response_bounds
end
end UnifiedTheory.Audit.KFCausalCoherentMatterWeakResponse

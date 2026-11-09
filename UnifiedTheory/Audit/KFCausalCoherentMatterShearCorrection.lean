/- The corrected weighted-shear formula for each actual ordered matter
weak response. Both FJG and the field-derivative output are constructed
from the coherent input; no commutator or extra moment is assumed. -/
import UnifiedTheory.Audit.KFCausalFieldShearResponseCorrection
import UnifiedTheory.Audit.KFCausalCoherentMatterWeakResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentMatterShearCorrection
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerSlope)
open UnifiedTheory.Audit.KFCausalFieldShearResponseCorrection
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
local notation "F" => fieldPower l i
local notation "T" => orderedExponential ε hε h
local notation "B" => pureMomentum ε hε h
local notation "J" => shearMomentum h
local notation "D" => defectOperator ε hε
local notation "W" => root ε hε h hb hh
local notation "responseL" => KFCausalClockFloorVacuumMomentumResponse.response ε hε h hb

theorem actual_response_with_derivative (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (b g jg u v : Hilbert) (hB : (f,b) ∈ (B).graph) (hg : (f,g) ∈ (T).graph)
    (hjg : (g,jg) ∈ (J).graph) (hu : (f,u) ∈ (matterFactor ε hε h (F)).graph)
    (hv : (b,v) ∈ (matterFactor ε hε h (F)).graph) :
    ∃ j d : Hilbert,
      (jg,j) ∈ (F).graph ∧
      d =ᵐ[volume] (fun x => powerSlope l i x*g x) ∧
      (u,j+(-Complex.I*(h:ℂ)) • d) ∈ (J).graph ∧
      (-2/h)*(inner ℂ u v).im = responseL u+
        (4/ε^2)*(inner ℂ (W u) (W (j+(-Complex.I*(h:ℂ)) • d))).re-
        derivativeCorrection ε hε h hb u d ∧
      |(-2/h)*(inner ℂ u v).im-(responseL u+
        (4/ε^2)*(inner ℂ (W u) (W (j+(-Complex.I*(h:ℂ)) • d))).re)| ≤
        (4*|h|/ε^2)*‖u‖*‖D (D d)‖ := by
  obtain ⟨j,hj,_⟩ := KFCausalCoherentMatterWeakResponse.actual_composition
    ε a h hε ha hh hb l i f hf b g jg u v hB hg hjg hu hv
  obtain ⟨g',hg',hu'⟩ := (composition_graph _ _ _ _).mp hu
  have eg : g' = g := (T).mem_graph_snd_inj' hg' hg rfl
  have hFu : (g,u) ∈ (F).graph := eg ▸ hu'
  obtain ⟨d,hd,hk⟩ := KFCausalCoherentFieldShearGraph.actual_power_graph
    ε a h hε ha hh hb l i f hf g jg u j hg hjg hFu hj
  have hr := KFCausalCoherentMatterWeakResponse.actual_weak_response
    ε a h hε ha hh hb l i f hf b g jg u v j hB hg hjg hu hv hj
  refine ⟨j,d,hj,hd,hk,hr.trans (corrected_response ε hε h hb hh u j d hk),?_⟩
  rw [hr]
  exact corrected_response_error ε hε h hb hh u j d hk

#print axioms actual_response_with_derivative
end
end UnifiedTheory.Audit.KFCausalCoherentMatterShearCorrection

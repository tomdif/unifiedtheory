/- The defect acts on the full closed joint energy graph. This transfers
the eight natural-factor identities through the actual simultaneous graph
closure, including vanishing energy weights, and proves its signed pairing. -/
import UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorClosedEnergyDefect
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)
  (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
  (mass2 quartic vacuum t : ℝ)

include hε hh in
theorem energy_bound : |hbar| ≤ Real.pi*ε := by nlinarith [Real.pi_pos]

theorem jointGraph_defect (c : Fin 8 → ℂ) (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ jointGraph (energyFactor ε hε hbar v l) c) :
    (defectOperator ε hε f,outputAction ε hε hbar hh g) ∈ jointGraph (energyFactor ε hε hbar v l) c := by
  intro i
  have h := energyFactor_graph_defect ε hε hbar hh v l i (c i • f) (g i) (hfg i)
  simpa only [map_smul,outputAction_apply] using h

theorem jointClosure_defect (c : Fin 8 → ℂ) (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (jointGraph (energyFactor ε hε hbar v l) c).topologicalClosure) :
    (defectOperator ε hε f,outputAction ε hε hbar hh g) ∈
      (jointGraph (energyFactor ε hε hbar v l) c).topologicalClosure := by
  let K := jointGraph (energyFactor ε hε hbar v l) c
  let P := (defectOperator ε hε).prodMap (outputAction ε hε hbar hh)
  have hK : K ≤ K.topologicalClosure.comap P.toLinearMap := by
    rintro ⟨x,y⟩ hxy
    exact K.le_topologicalClosure (jointGraph_defect ε hε hbar hh v l c x y hxy)
  exact K.topologicalClosure_minimal hK (K.isClosed_topologicalClosure.preimage P.continuous) hfg

theorem closedEnergy_graph_defect (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (closedEnergy ε hε hbar v l mass2 quartic vacuum t).graph) :
    (defectOperator ε hε f,outputAction ε hε hbar hh g) ∈
      (closedEnergy ε hε hbar v l mass2 quartic vacuum t).graph := by
  rw [closedEnergy_graph ε hε hbar v l mass2 quartic vacuum t (energy_bound ε hε hbar hh)] at hfg ⊢
  exact jointClosure_defect ε hε hbar hh v l _ f g hfg

include hh in
theorem closedEnergy_defect_domain (f : Hilbert)
    (hf : f ∈ (closedEnergy ε hε hbar v l mass2 quartic vacuum t).domain) :
    defectOperator ε hε f ∈ (closedEnergy ε hε hbar v l mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph (closedEnergy_graph_defect ε hε hbar hh v l mass2 quartic vacuum t f _
    ((closedEnergy ε hε hbar v l mass2 quartic vacuum t).mem_graph ⟨f,hf⟩))

theorem closedEnergy_defect_action (f : (closedEnergy ε hε hbar v l mass2 quartic vacuum t).domain) :
    closedEnergy ε hε hbar v l mass2 quartic vacuum t
      ⟨defectOperator ε hε f,closedEnergy_defect_domain ε hε hbar hh v l mass2 quartic vacuum t f f.property⟩ =
      outputAction ε hε hbar hh (closedEnergy ε hε hbar v l mass2 quartic vacuum t f) :=
  (closedEnergy ε hε hbar v l mass2 quartic vacuum t).mem_graph_snd_inj'
    ((closedEnergy ε hε hbar v l mass2 quartic vacuum t).mem_graph _)
    (closedEnergy_graph_defect ε hε hbar hh v l mass2 quartic vacuum t f _
      ((closedEnergy ε hε hbar v l mass2 quartic vacuum t).mem_graph f)) rfl

theorem closedEnergy_defect_bound (f : (closedEnergy ε hε hbar v l mass2 quartic vacuum t).domain) :
    ‖closedEnergy ε hε hbar v l mass2 quartic vacuum t
      ⟨defectOperator ε hε f,closedEnergy_defect_domain ε hε hbar hh v l mass2 quartic vacuum t f f.property⟩‖ ≤
      2*‖closedEnergy ε hε hbar v l mass2 quartic vacuum t f‖ := by
  rw [closedEnergy_defect_action]
  exact outputAction_norm ε hε hbar hh _

include hh in
theorem closedEnergy_square_sign (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (closedEnergy ε hε hbar v l mass2 quartic vacuum t).graph) :
    ∃ gDD : Output (Fin 8) Hilbert,
      (defectOperator ε hε (defectOperator ε hε f),gDD) ∈
        (closedEnergy ε hε hbar v l mass2 quartic vacuum t).graph ∧
      0 ≤ hbar*(inner ℂ g gDD).im := by
  have h1 := closedEnergy_graph_defect ε hε hbar hh v l mass2 quartic vacuum t f g hfg
  exact ⟨_,closedEnergy_graph_defect ε hε hbar hh v l mass2 quartic vacuum t _ _ h1,
    outputAction_square_sign ε hε hbar hh g⟩

#print axioms energy_bound
#print axioms jointGraph_defect
#print axioms jointClosure_defect
#print axioms closedEnergy_graph_defect
#print axioms closedEnergy_defect_domain
#print axioms closedEnergy_defect_action
#print axioms closedEnergy_defect_bound
#print axioms closedEnergy_square_sign

end
end UnifiedTheory.Audit.KFCausalClockFloorClosedEnergyDefect

/- Neutral translation preserves the actual weighted joint graph and its
closure. Nonzero weights are explicit: no common-domain core is silently
assumed for a graph with vanishing energy channels. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslationOutput
import UnifiedTheory.Audit.KFCausalClockFloorJointEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNeutralTranslationJointGraph
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates (action)
open UnifiedTheory.Audit.KFCausalNeutralTranslationFactors
open UnifiedTheory.Audit.KFCausalNeutralTranslationMatter
open UnifiedTheory.Audit.KFCausalNeutralTranslationOutput
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (jointGraph)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)

variable (ε : ℝ) (hε : 0 < ε) (h r : ℝ)
  (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)

theorem factor_outputs_action (f : Hilbert) (g : Outputs)
    (hg : ∀ i, (f,g i) ∈ (energyFactor ε hε h v l i).graph) :
    ∀ i, (action r f,action r (mixValues (shiftValue l r) g i)) ∈
      (energyFactor ε hε h v l i).graph := by
  intro i
  fin_cases i
  · exact clockHalf_graph_action ε r f (g 0) (hg 0)
  · exact kinetic_graph_action ε h r (v 0) f (g 1) (hg 1)
  · exact kinetic_graph_action ε h r (v 1) f (g 2) (hg 2)
  · exact kinetic_graph_action ε h r (v 2) f (g 3) (hg 3)
  · exact kinetic_graph_action ε h r (v 3) f (g 4) (hg 4)
  · exact linear_matter_graph_action ε hε h r l f (g 7) (g 5) (hg 7) (hg 5)
  · exact quadratic_matter_graph_action ε hε h r l f (g 7) (g 5) (g 6) (hg 7) (hg 5) (hg 6)
  · exact ordered_graph_action ε hε h r f (g 7) (hg 7)

theorem joint_graph_action (w : Fin 8 → ℂ) (hw : ∀ i, w i ≠ 0)
    (f : Hilbert) (g : Outputs) (hfg : (f,g) ∈ jointGraph (energyFactor ε hε h v l) w) :
    (action r f,outputAction w (shiftValue l r) r g) ∈
      jointGraph (energyFactor ε hε h v l) w := by
  have hu : ∀ i, (f,scaleOutput (fun j => (w j)⁻¹) g i) ∈
      (energyFactor ε hε h v l i).graph := by
    intro i
    have hi := (energyFactor ε hε h v l i).graph.smul_mem ((w i)⁻¹) (hfg i)
    change ((w i)⁻¹ • (w i • f),(w i)⁻¹ • g i) ∈ _ at hi
    simpa only [smul_smul,inv_mul_cancel₀ (hw i),one_smul] using hi
  have ht := factor_outputs_action ε hε h r v l f _ hu
  intro i
  have hi := (energyFactor ε hε h v l i).graph.smul_mem (w i) (ht i)
  change (w i • action r f,w i • action r (mixValues (shiftValue l r)
    (scaleOutput (fun j => (w j)⁻¹) g) i)) ∈ _ at hi
  simpa only [outputAction_apply,map_smul] using hi

def pairAction (w : Fin 8 → ℂ) : (Hilbert × Outputs) →L[ℂ] (Hilbert × Outputs) :=
  (action r : Hilbert →L[ℂ] Hilbert).prodMap (outputAction w (shiftValue l r) r)

theorem joint_closure_action (w : Fin 8 → ℂ) (hw : ∀ i, w i ≠ 0)
    (f : Hilbert) (g : Outputs)
    (hfg : (f,g) ∈ (jointGraph (energyFactor ε hε h v l) w).topologicalClosure) :
    (action r f,outputAction w (shiftValue l r) r g) ∈
      (jointGraph (energyFactor ε hε h v l) w).topologicalClosure := by
  let S := jointGraph (energyFactor ε hε h v l) w
  let T := pairAction r l w
  have hS : S ≤ S.comap T.toLinearMap := fun z hz => joint_graph_action ε hε h r v l w hw z.1 z.2 hz
  have hT : S ≤ S.topologicalClosure.comap T.toLinearMap :=
    fun z hz => S.le_topologicalClosure (hS hz)
  have hc : IsClosed (S.topologicalClosure.comap T.toLinearMap : Set (Hilbert × Outputs)) :=
    S.isClosed_topologicalClosure.preimage T.continuous
  exact S.topologicalClosure_minimal hT hc hfg

theorem energyWeight_ne_zero (m g k t : ℝ) (hm : 0 < m) (hg : 0 < g) (hk : 0 < k) :
    ∀ i, energyWeight m g k t i ≠ 0 := by
  intro i
  have hm' : Real.sqrt m ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hm)
  have hg' : Real.sqrt g ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hg)
  have hk' : Real.sqrt k ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hk)
  fin_cases i <;> simp [energyWeight,hm',hg',hk']

theorem closed_energy_graph_action (m g k t : ℝ) (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
    (hh : |h| ≤ Real.pi*ε) (f : Hilbert) (y : Outputs)
    (hfy : (f,y) ∈ (closedEnergy ε hε h v l m g k t).graph) :
    (action r f,outputAction (energyWeight m g k t) (shiftValue l r) r y) ∈
      (closedEnergy ε hε h v l m g k t).graph := by
  rw [closedEnergy_graph ε hε h v l m g k t hh] at hfy ⊢
  exact joint_closure_action ε hε h r v l _ (energyWeight_ne_zero m g k t hm hg hk) f y hfy

theorem closed_energy_domain_action (m g k t : ℝ) (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
    (hh : |h| ≤ Real.pi*ε) (f : Hilbert)
    (hf : f ∈ (closedEnergy ε hε h v l m g k t).domain) :
    action r f ∈ (closedEnergy ε hε h v l m g k t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (closed_energy_graph_action ε hε h r v l m g k t hm hg hk hh f _
      ((closedEnergy ε hε h v l m g k t).mem_graph ⟨f,hf⟩))

theorem closed_energy_domain_action_iff (m g k t : ℝ) (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
    (hh : |h| ≤ Real.pi*ε) (f : Hilbert) :
    action r f ∈ (closedEnergy ε hε h v l m g k t).domain ↔
      f ∈ (closedEnergy ε hε h v l m g k t).domain := by
  refine ⟨fun hf => ?_,closed_energy_domain_action ε hε h r v l m g k t hm hg hk hh f⟩
  simpa only [action_inverse] using
    closed_energy_domain_action ε hε h (-r) v l m g k t hm hg hk hh _ hf

#print axioms factor_outputs_action
#print axioms joint_graph_action
#print axioms joint_closure_action
#print axioms energyWeight_ne_zero
#print axioms closed_energy_graph_action
#print axioms closed_energy_domain_action
#print axioms closed_energy_domain_action_iff

end
end UnifiedTheory.Audit.KFCausalNeutralTranslationJointGraph
